--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],
  
  userAuthorized = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}

\* Check if a truck is currently handling bin "b".
TruckBusy(b) == \E t \in Trucks : truckCommand[t].bin = b /\ truckCommand[t].command /= "emptied"


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each trash bin, the outer door can only be locked if it is closed.
\* SAFETY
OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]


\* The vertical ram is only used when the outer door is closed and locked.
\* SAFETY
RamOuterDoor == \A b \in Bins : ramExtended[b] => outerDoorLocked[b] /\ ~outerDoorOpen[b]

\* Every time the trash bin is full, it is eventually not full anymore.
\* LIVENESS
TrashEmptied == \A b \in Bins : [](~TrashFitsCapacity(b, MaxUserTrash) => <>TrashFitsCapacity(b, MaxUserTrash))


\* An unauthorized user cannot open the outer door.
\* SAFETY
AuthorizedOpenOnly == \A b \in Bins : outerDoorOpen[b] => userAuthorized[b]


\* The user infinitely often has trash and infinitely often has no trash
\* LIVENESS
UserTrash == \A u \in Users : []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)


\* Every time the user has trash, they can deposit their trash.
\* LIVENESS
UserTrashDeposited == \A u \in Users : []((userTrash[u] > 0) => <>(userTrash[u] = 0))


\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
\* LIVENESS
TruckEmpties == \A t \in Trucks : (truckCommand[t].command = "request") ~> (truckCommand[t].command = "emptied")

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
fair process truckProcess \in Trucks

begin
  
  TruckStart:
    while TRUE do
        \* wait until truck is requested
        await truckCommand[self].command = "request";
        
    \* Note that the truck arrived.    
    TruckDriveToBin:
        truckCommand[self].command := "arrived";
    
    \* Truck starts its progress.    
    TruckStartEmpty:
        truckCommand[self].command := "start_emptying";
        
    \* Send the command for the bin to empty. 
    TruckEmptyBin:
        binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
    
    \* Wait until the bin has finished.
    TruckFinishEmpty:
        await binCommand[truckCommand[self].bin].command = "finished";
        
    \* Report the completion and keep track of ID of bin emptied.    
    TruckDone:
        truckCommand[self].command := "emptied"
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = Control

variables
    \* Local storage for scans
    scanMsg = [user |-> 0, bin |-> 0],
    \* Store response from server
    serverMsg = [user |-> 0, permission |-> FALSE];
    
begin
  ControlStart:
    while TRUE do
    
    \* Read incoming scans, and store.
    ReadScans:
        read(scans, scanMsg);
        
    \* Validate user’s card.    
    SendServerReq:
        write(serverRequests, [user |-> scanMsg.user]);
        
    \* Wait for server response.    
    ReadServerResp:
        read(serverResponses, serverMsg);
    
    \* Check if the user has permission and the remaining bin capacity has space for the user deposit
    \* and if the truck is currently not doing anything
    CheckPermission:
        if serverMsg.permission /\ TrashFitsCapacity(scanMsg.bin, MaxUserTrash) /\ ~TruckBusy(scanMsg.bin)
        
        then
            
        \* Unlock door and wait.            
        UnlockDoor:
            binCommand[scanMsg.bin] := [command |-> "change_outer_lock", open |-> TRUE];
            
        AwaitDoorUnlocked:
            await binCommand[scanMsg.bin].command = "finished";
        
        \* Permit users access.
        PermitUserAccess:    
            write(permissions[scanMsg.user], [user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> TRUE]);
            userAuthorized[scanMsg.bin] := TRUE;
        
        \* Wait until user deposits trash and closes outer door.    
        AwaitUserCloses:
            await binSensor[scanMsg.bin].sensor = "outer_door_closed";

        AwaitUserClosesFinished:
            await binCommand[scanMsg.bin].command = "finished";
            binSensor[scanMsg.bin] := [sensor |-> "idle"];
            userAuthorized[scanMsg.bin] := FALSE;
        
        \* Lock the outer door and wait until finished.    
        LockDoor:
            binCommand[scanMsg.bin] := [command |-> "change_outer_lock", open |-> FALSE];
            
        AwaitDoorLocked:
            await binCommand[scanMsg.bin].command = "finished";
         
        \* Open the trapdoor and wait until finished.    
        OpenTrapDoor:
            binCommand[scanMsg.bin] := [command |-> "change_trap_door", open |-> TRUE];
            
        AwaitTrapDoorOpened:
            await binCommand[scanMsg.bin].command = "finished";
        
        \* Extend and retract ram, wait for each to finish.    
        ExtendRam:
            binCommand[scanMsg.bin] := [command |-> "change_ram", open |-> TRUE];
            
        AwaitRamExtended:
            await binCommand[scanMsg.bin].command = "finished";
            
        RetractRam:
            binCommand[scanMsg.bin] := [command |-> "change_ram", open |-> FALSE];
            
        AwaitRamRetracted:
            await binCommand[scanMsg.bin].command = "finished";
        
        \* Close the trapdoor and wait until closed.    
        CloseTrapDoor:
            binCommand[scanMsg.bin] := [command |-> "change_trap_door", open |-> FALSE];
            
        AwaitTrapDoorClosed:
            await binCommand[scanMsg.bin].command = "finished";
        
        \* Check if bin needs emptying.    
        CheckTruckNeeded:
            if ~TrashFitsCapacity(scanMsg.bin, MaxUserTrash) then
                \* Pick one available truck randomly.
                with truck \in AvailableTrucks do
                    truckCommand[truck] := [command |-> "request", bin |-> scanMsg.bin];
                end with;
            end if;
        
        else
            \* In case permission is false, decline access.
            write(permissions[scanMsg.user], [user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> FALSE]);
        end if;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a990abea" /\ chksum(tla) = "fee627d0")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userAuthorized, userTrash, binCommand, binSensor, 
          scans, permissions, serverRequests, serverResponses, truckCommand, 
          pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}


TruckBusy(b) == \E t \in Trucks : truckCommand[t].bin = b /\ truckCommand[t].command /= "emptied"






TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)










OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]




RamOuterDoor == \A b \in Bins : ramExtended[b] => outerDoorLocked[b] /\ ~outerDoorOpen[b]



TrashEmptied == \A b \in Bins : [](~TrashFitsCapacity(b, MaxUserTrash) => <>TrashFitsCapacity(b, MaxUserTrash))




AuthorizedOpenOnly == \A b \in Bins : outerDoorOpen[b] => userAuthorized[b]




UserTrash == \A u \in Users : []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)




UserTrashDeposited == \A u \in Users : []((userTrash[u] > 0) => <>(userTrash[u] = 0))




TruckEmpties == \A t \in Trucks : (truckCommand[t].command = "request") ~> (truckCommand[t].command = "emptied")

VARIABLES perm, selectedBin, req, scanMsg, serverMsg

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userAuthorized, userTrash, binCommand, binSensor, 
           scans, permissions, serverRequests, serverResponses, truckCommand, 
           pc, perm, selectedBin, req, scanMsg, serverMsg >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userAuthorized = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scanMsg = [user |-> 0, bin |-> 0]
        /\ serverMsg = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 193, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 200, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 203, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 215, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 227, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 228, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 229, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 230, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 231, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 235, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userAuthorized, 
                                           userTrash, binCommand, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scanMsg, 
                                           serverMsg >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userAuthorized, 
                                            userTrash, binSensor, scans, 
                                            permissions, serverRequests, 
                                            serverResponses, truckCommand, 
                                            perm, selectedBin, req, scanMsg, 
                                            serverMsg >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userAuthorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scanMsg, 
                                           serverMsg >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, userTrash, binCommand, 
                                      binSensor, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scanMsg, serverMsg >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 267, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 268, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userAuthorized, userTrash, 
                                               binCommand, binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, selectedBin, req, 
                                               scanMsg, serverMsg >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, userTrash, binSensor, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, scanMsg, serverMsg >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userAuthorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scanMsg, 
                                           serverMsg >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 275, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          userAuthorized, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, perm, selectedBin, req, 
                                          scanMsg, serverMsg >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binSensor, 
                                       scans, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, scanMsg, serverMsg >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userAuthorized, 
                                             userTrash, binCommand, binSensor, 
                                             scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, selectedBin, 
                                             req, scanMsg, serverMsg >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, binCommand, binSensor, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, scanMsg, serverMsg >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       scanMsg, serverMsg >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, userTrash, binCommand, 
                                      binSensor, scans, permissions, 
                                      truckCommand, perm, selectedBin, scanMsg, 
                                      serverMsg >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ truckCommand[self].command = "request"
                    /\ pc' = [pc EXCEPT ![self] = "TruckDriveToBin"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, 
                                    scanMsg, serverMsg >>

TruckDriveToBin(self) == /\ pc[self] = "TruckDriveToBin"
                         /\ truckCommand' = [truckCommand EXCEPT ![self].command = "arrived"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckStartEmpty"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userAuthorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, perm, 
                                         selectedBin, req, scanMsg, serverMsg >>

TruckStartEmpty(self) == /\ pc[self] = "TruckStartEmpty"
                         /\ truckCommand' = [truckCommand EXCEPT ![self].command = "start_emptying"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckEmptyBin"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userAuthorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, perm, 
                                         selectedBin, req, scanMsg, serverMsg >>

TruckEmptyBin(self) == /\ pc[self] = "TruckEmptyBin"
                       /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "TruckFinishEmpty"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binSensor, 
                                       scans, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, scanMsg, serverMsg >>

TruckFinishEmpty(self) == /\ pc[self] = "TruckFinishEmpty"
                          /\ binCommand[truckCommand[self].bin].command = "finished"
                          /\ pc' = [pc EXCEPT ![self] = "TruckDone"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userAuthorized, 
                                          userTrash, binCommand, binSensor, 
                                          scans, permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          selectedBin, req, scanMsg, serverMsg >>

TruckDone(self) == /\ pc[self] = "TruckDone"
                   /\ truckCommand' = [truckCommand EXCEPT ![self].command = "emptied"]
                   /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, perm, 
                                   selectedBin, req, scanMsg, serverMsg >>

truckProcess(self) == TruckStart(self) \/ TruckDriveToBin(self)
                         \/ TruckStartEmpty(self) \/ TruckEmptyBin(self)
                         \/ TruckFinishEmpty(self) \/ TruckDone(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "ReadScans"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userAuthorized, userTrash, 
                                binCommand, binSensor, scans, permissions, 
                                serverRequests, serverResponses, truckCommand, 
                                perm, selectedBin, req, scanMsg, serverMsg >>

ReadScans == /\ pc[Control] = "ReadScans"
             /\ scans /= <<>>
             /\ scanMsg' = Head(scans)
             /\ scans' = Tail(scans)
             /\ pc' = [pc EXCEPT ![Control] = "SendServerReq"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userAuthorized, userTrash, binCommand, binSensor, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, perm, selectedBin, req, serverMsg >>

SendServerReq == /\ pc[Control] = "SendServerReq"
                 /\ serverRequests' = Append(serverRequests, ([user |-> scanMsg.user]))
                 /\ pc' = [pc EXCEPT ![Control] = "ReadServerResp"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userAuthorized, userTrash, 
                                 binCommand, binSensor, scans, permissions, 
                                 serverResponses, truckCommand, perm, 
                                 selectedBin, req, scanMsg, serverMsg >>

ReadServerResp == /\ pc[Control] = "ReadServerResp"
                  /\ serverResponses /= <<>>
                  /\ serverMsg' = Head(serverResponses)
                  /\ serverResponses' = Tail(serverResponses)
                  /\ pc' = [pc EXCEPT ![Control] = "CheckPermission"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userAuthorized, userTrash, 
                                  binCommand, binSensor, scans, permissions, 
                                  serverRequests, truckCommand, perm, 
                                  selectedBin, req, scanMsg >>

CheckPermission == /\ pc[Control] = "CheckPermission"
                   /\ IF serverMsg.permission /\ TrashFitsCapacity(scanMsg.bin, MaxUserTrash) /\ ~TruckBusy(scanMsg.bin)
                         THEN /\ pc' = [pc EXCEPT ![Control] = "UnlockDoor"]
                              /\ UNCHANGED permissions
                         ELSE /\ permissions' = [permissions EXCEPT ![scanMsg.user] = Append((permissions[scanMsg.user]), ([user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> FALSE]))]
                              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, serverRequests, 
                                   serverResponses, truckCommand, perm, 
                                   selectedBin, req, scanMsg, serverMsg >>

UnlockDoor == /\ pc[Control] = "UnlockDoor"
              /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
              /\ pc' = [pc EXCEPT ![Control] = "AwaitDoorUnlocked"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userAuthorized, userTrash, binSensor, scans, 
                              permissions, serverRequests, serverResponses, 
                              truckCommand, perm, selectedBin, req, scanMsg, 
                              serverMsg >>

AwaitDoorUnlocked == /\ pc[Control] = "AwaitDoorUnlocked"
                     /\ binCommand[scanMsg.bin].command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "PermitUserAccess"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, 
                                     userAuthorized, userTrash, binCommand, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, selectedBin, req, 
                                     scanMsg, serverMsg >>

PermitUserAccess == /\ pc[Control] = "PermitUserAccess"
                    /\ permissions' = [permissions EXCEPT ![scanMsg.user] = Append((permissions[scanMsg.user]), ([user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> TRUE]))]
                    /\ userAuthorized' = [userAuthorized EXCEPT ![scanMsg.bin] = TRUE]
                    /\ pc' = [pc EXCEPT ![Control] = "AwaitUserCloses"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, 
                                    scanMsg, serverMsg >>

AwaitUserCloses == /\ pc[Control] = "AwaitUserCloses"
                   /\ binSensor[scanMsg.bin].sensor = "outer_door_closed"
                   /\ pc' = [pc EXCEPT ![Control] = "AwaitUserClosesFinished"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, selectedBin, req, 
                                   scanMsg, serverMsg >>

AwaitUserClosesFinished == /\ pc[Control] = "AwaitUserClosesFinished"
                           /\ binCommand[scanMsg.bin].command = "finished"
                           /\ binSensor' = [binSensor EXCEPT ![scanMsg.bin] = [sensor |-> "idle"]]
                           /\ userAuthorized' = [userAuthorized EXCEPT ![scanMsg.bin] = FALSE]
                           /\ pc' = [pc EXCEPT ![Control] = "LockDoor"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, selectedBin, 
                                           req, scanMsg, serverMsg >>

LockDoor == /\ pc[Control] = "LockDoor"
            /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
            /\ pc' = [pc EXCEPT ![Control] = "AwaitDoorLocked"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userAuthorized, userTrash, binSensor, scans, 
                            permissions, serverRequests, serverResponses, 
                            truckCommand, perm, selectedBin, req, scanMsg, 
                            serverMsg >>

AwaitDoorLocked == /\ pc[Control] = "AwaitDoorLocked"
                   /\ binCommand[scanMsg.bin].command = "finished"
                   /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, selectedBin, req, 
                                   scanMsg, serverMsg >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_trap_door", open |-> TRUE]]
                /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapDoorOpened"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userAuthorized, userTrash, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, perm, 
                                selectedBin, req, scanMsg, serverMsg >>

AwaitTrapDoorOpened == /\ pc[Control] = "AwaitTrapDoorOpened"
                       /\ binCommand[scanMsg.bin].command = "finished"
                       /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       scanMsg, serverMsg >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_ram", open |-> TRUE]]
             /\ pc' = [pc EXCEPT ![Control] = "AwaitRamExtended"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userAuthorized, userTrash, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, perm, selectedBin, req, scanMsg, 
                             serverMsg >>

AwaitRamExtended == /\ pc[Control] = "AwaitRamExtended"
                    /\ binCommand[scanMsg.bin].command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "RetractRam"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, 
                                    scanMsg, serverMsg >>

RetractRam == /\ pc[Control] = "RetractRam"
              /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_ram", open |-> FALSE]]
              /\ pc' = [pc EXCEPT ![Control] = "AwaitRamRetracted"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userAuthorized, userTrash, binSensor, scans, 
                              permissions, serverRequests, serverResponses, 
                              truckCommand, perm, selectedBin, req, scanMsg, 
                              serverMsg >>

AwaitRamRetracted == /\ pc[Control] = "AwaitRamRetracted"
                     /\ binCommand[scanMsg.bin].command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, 
                                     userAuthorized, userTrash, binCommand, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, selectedBin, req, 
                                     scanMsg, serverMsg >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [binCommand EXCEPT ![scanMsg.bin] = [command |-> "change_trap_door", open |-> FALSE]]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapDoorClosed"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userAuthorized, userTrash, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, perm, 
                                 selectedBin, req, scanMsg, serverMsg >>

AwaitTrapDoorClosed == /\ pc[Control] = "AwaitTrapDoorClosed"
                       /\ binCommand[scanMsg.bin].command = "finished"
                       /\ pc' = [pc EXCEPT ![Control] = "CheckTruckNeeded"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       scanMsg, serverMsg >>

CheckTruckNeeded == /\ pc[Control] = "CheckTruckNeeded"
                    /\ IF ~TrashFitsCapacity(scanMsg.bin, MaxUserTrash)
                          THEN /\ \E truck \in AvailableTrucks:
                                    truckCommand' = [truckCommand EXCEPT ![truck] = [command |-> "request", bin |-> scanMsg.bin]]
                          ELSE /\ TRUE
                               /\ UNCHANGED truckCommand
                    /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, perm, 
                                    selectedBin, req, scanMsg, serverMsg >>

controlProcess == ControlStart \/ ReadScans \/ SendServerReq
                     \/ ReadServerResp \/ CheckPermission \/ UnlockDoor
                     \/ AwaitDoorUnlocked \/ PermitUserAccess
                     \/ AwaitUserCloses \/ AwaitUserClosesFinished
                     \/ LockDoor \/ AwaitDoorLocked \/ OpenTrapDoor
                     \/ AwaitTrapDoorOpened \/ ExtendRam
                     \/ AwaitRamExtended \/ RetractRam \/ AwaitRamRetracted
                     \/ CloseTrapDoor \/ AwaitTrapDoorClosed
                     \/ CheckTruckNeeded

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Oct 13 12:52:55 CEST 2026 by robin
