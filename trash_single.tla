---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,
  
  userAuthorized = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
\* SAFETY
OuterDoorLocked == outerDoorLocked => ~outerDoorOpen

\* The vertical ram is only used when the outer door is closed and locked.
\* SAFETY
RamOuterDoor == ramExtended => outerDoorLocked /\ ~outerDoorOpen

\* Every time the trash bin is full, it is eventually not full anymore.
\* LIVENESS
TrashEmptied == [](~TrashFitsCapacity(MaxUserTrash) => <>TrashFitsCapacity(MaxUserTrash))


\* An unauthorized user cannot open the outer door.
\* SAFETY
AuthorizedOpenOnly == outerDoorOpen => userAuthorized


\* The user infinitely often has trash and infinitely often has no trash
\* LIVENESS
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)


\* Every time the user has trash, they can deposit their trash.
\* LIVENESS
UserTrashDeposited == []((userTrash > 0) => <>(userTrash = 0))


\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
\* LIVENESS
TruckEmpties == (truckCommand.command = "request") ~> (truckCommand.command = "emptied")

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
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
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
        await truckCommand.command = "request";
        
    \* Note that the truck arrived.    
    TruckDriveToBin:
        truckCommand.command := "arrived";
    
    \* Truck starts its progress.    
    TruckStartEmpty:
        truckCommand.command := "start_emptying";
        
    \* Send the command for the bin to empty.     
    TruckEmptyBin:
        binCommand := [command |-> "empty", open |-> FALSE];
    
    \* Wait until the bin has finished.
    TruckFinishEmpty:
        await binCommand.command = "finished";
        
    \* Report the completion. 
    TruckDone:
        truckCommand.command := "emptied";
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
        if serverMsg.permission /\ TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied" 
        then
            
        \* Unlock door and wait.            
        UnlockDoor:
            binCommand := [command |-> "change_outer_lock", open |-> TRUE];
            
        AwaitDoorUnlocked:
            await binCommand.command = "finished";
            
        \* Permit users access.
        PermitUserAccess:    
            write(permissions, [user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> TRUE]);
            userAuthorized := TRUE;
        
        \* Wait until user deposits trash and closes outer door.    
        AwaitUserCloses:
            await binSensor.sensor = "outer_door_closed";

        AwaitUserClosesFinished:
            await binCommand.command = "finished";
            binSensor := [sensor |-> "idle"];
            userAuthorized := FALSE;
        
        \* Lock the outer door and wait until finished.    
        LockDoor:
            binCommand := [command |-> "change_outer_lock", open |-> FALSE];
            
        AwaitDoorLocked:
            await binCommand.command = "finished";
         
        \* Open the trapdoor and wait until finished.    
        OpenTrapDoor:
            binCommand := [command |-> "change_trap_door", open |-> TRUE];
            
        AwaitTrapDoorOpened:
            await binCommand.command = "finished";
        
        \* Extend and retract ram, wait for each to finish.    
        ExtendRam:
            binCommand := [command |-> "change_ram", open |-> TRUE];
            
        AwaitRamExtended:
            await binCommand.command = "finished";
            
        RetractRam:
            binCommand := [command |-> "change_ram", open |-> FALSE];
            
        AwaitRamRetracted:
            await binCommand.command = "finished";
        
        \* Close the trapdoor and wait until closed.    
        CloseTrapDoor:
            binCommand := [command |-> "change_trap_door", open |-> FALSE];
            
        AwaitTrapDoorClosed:
            await binCommand.command = "finished";
        
        \* Check if bin needs emptying.    
        CheckTruckNeeded:
            if ~TrashFitsCapacity(MaxUserTrash) then
                truckCommand := [command |-> "request", bin |-> scanMsg.bin];
                
            end if;
        
        else
            \* In case permission is false, decline access.
            write(permissions, [user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> FALSE]);
        end if;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5ede3ba4" /\ chksum(tla) = "a7de200")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userAuthorized, userTrash, binCommand, binSensor, 
          scans, permissions, serverRequests, serverResponses, truckCommand, 
          pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded









OuterDoorLocked == outerDoorLocked => ~outerDoorOpen



RamOuterDoor == ramExtended => outerDoorLocked /\ ~outerDoorOpen



TrashEmptied == [](~TrashFitsCapacity(MaxUserTrash) => <>TrashFitsCapacity(MaxUserTrash))




AuthorizedOpenOnly == outerDoorOpen => userAuthorized




UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)




UserTrashDeposited == []((userTrash > 0) => <>(userTrash = 0))




TruckEmpties == (truckCommand.command = "request") ~> (truckCommand.command = "emptied")

VARIABLES perm, req, scanMsg, serverMsg

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userAuthorized, userTrash, binCommand, binSensor, 
           scans, permissions, serverRequests, serverResponses, truckCommand, 
           pc, perm, req, scanMsg, serverMsg >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userAuthorized = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
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
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 181, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 188, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 191, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 203, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 215, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 216, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 217, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 218, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 219, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 223, column 9.")
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
                                           req, scanMsg, serverMsg >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userAuthorized, 
                                            userTrash, binSensor, scans, 
                                            permissions, serverRequests, 
                                            serverResponses, truckCommand, 
                                            perm, req, scanMsg, serverMsg >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
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
                                           req, scanMsg, serverMsg >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
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
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 250, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 251, column 7.")
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
                                               truckCommand, req, scanMsg, 
                                               serverMsg >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, userTrash, binSensor, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scanMsg, serverMsg >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userAuthorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scanMsg, serverMsg >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 258, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          userAuthorized, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, perm, req, scanMsg, 
                                          serverMsg >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binSensor, 
                                       scans, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, scanMsg, serverMsg >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userAuthorized, 
                                             userTrash, binCommand, binSensor, 
                                             scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, req, scanMsg, 
                                             serverMsg >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      userAuthorized, binCommand, binSensor, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scanMsg, serverMsg >>

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
                                       truckCommand, perm, req, scanMsg, 
                                       serverMsg >>

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
                                      truckCommand, perm, scanMsg, serverMsg >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ truckCommand.command = "request"
                    /\ pc' = [pc EXCEPT ![self] = "TruckDriveToBin"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scanMsg, 
                                    serverMsg >>

TruckDriveToBin(self) == /\ pc[self] = "TruckDriveToBin"
                         /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckStartEmpty"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userAuthorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, perm, 
                                         req, scanMsg, serverMsg >>

TruckStartEmpty(self) == /\ pc[self] = "TruckStartEmpty"
                         /\ truckCommand' = [truckCommand EXCEPT !.command = "start_emptying"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckEmptyBin"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userAuthorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, perm, 
                                         req, scanMsg, serverMsg >>

TruckEmptyBin(self) == /\ pc[self] = "TruckEmptyBin"
                       /\ binCommand' = [command |-> "empty", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "TruckFinishEmpty"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binSensor, 
                                       scans, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, scanMsg, serverMsg >>

TruckFinishEmpty(self) == /\ pc[self] = "TruckFinishEmpty"
                          /\ binCommand.command = "finished"
                          /\ pc' = [pc EXCEPT ![self] = "TruckDone"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userAuthorized, 
                                          userTrash, binCommand, binSensor, 
                                          scans, permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          req, scanMsg, serverMsg >>

TruckDone(self) == /\ pc[self] = "TruckDone"
                   /\ truckCommand' = [truckCommand EXCEPT !.command = "emptied"]
                   /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, perm, req, 
                                   scanMsg, serverMsg >>

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
                                perm, req, scanMsg, serverMsg >>

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
                             truckCommand, perm, req, serverMsg >>

SendServerReq == /\ pc[Control] = "SendServerReq"
                 /\ serverRequests' = Append(serverRequests, ([user |-> scanMsg.user]))
                 /\ pc' = [pc EXCEPT ![Control] = "ReadServerResp"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userAuthorized, userTrash, 
                                 binCommand, binSensor, scans, permissions, 
                                 serverResponses, truckCommand, perm, req, 
                                 scanMsg, serverMsg >>

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
                                  serverRequests, truckCommand, perm, req, 
                                  scanMsg >>

CheckPermission == /\ pc[Control] = "CheckPermission"
                   /\ IF serverMsg.permission /\ TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied"
                         THEN /\ pc' = [pc EXCEPT ![Control] = "UnlockDoor"]
                              /\ UNCHANGED permissions
                         ELSE /\ permissions' = Append(permissions, ([user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> FALSE]))
                              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, serverRequests, 
                                   serverResponses, truckCommand, perm, req, 
                                   scanMsg, serverMsg >>

UnlockDoor == /\ pc[Control] = "UnlockDoor"
              /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
              /\ pc' = [pc EXCEPT ![Control] = "AwaitDoorUnlocked"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userAuthorized, userTrash, binSensor, scans, 
                              permissions, serverRequests, serverResponses, 
                              truckCommand, perm, req, scanMsg, serverMsg >>

AwaitDoorUnlocked == /\ pc[Control] = "AwaitDoorUnlocked"
                     /\ binCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "PermitUserAccess"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, 
                                     userAuthorized, userTrash, binCommand, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scanMsg, 
                                     serverMsg >>

PermitUserAccess == /\ pc[Control] = "PermitUserAccess"
                    /\ permissions' = Append(permissions, ([user |-> scanMsg.user, bin |-> scanMsg.bin, granted |-> TRUE]))
                    /\ userAuthorized' = TRUE
                    /\ pc' = [pc EXCEPT ![Control] = "AwaitUserCloses"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scanMsg, 
                                    serverMsg >>

AwaitUserCloses == /\ pc[Control] = "AwaitUserCloses"
                   /\ binSensor.sensor = "outer_door_closed"
                   /\ pc' = [pc EXCEPT ![Control] = "AwaitUserClosesFinished"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, scanMsg, serverMsg >>

AwaitUserClosesFinished == /\ pc[Control] = "AwaitUserClosesFinished"
                           /\ binCommand.command = "finished"
                           /\ binSensor' = [sensor |-> "idle"]
                           /\ userAuthorized' = FALSE
                           /\ pc' = [pc EXCEPT ![Control] = "LockDoor"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, req, scanMsg, 
                                           serverMsg >>

LockDoor == /\ pc[Control] = "LockDoor"
            /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
            /\ pc' = [pc EXCEPT ![Control] = "AwaitDoorLocked"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userAuthorized, userTrash, binSensor, scans, 
                            permissions, serverRequests, serverResponses, 
                            truckCommand, perm, req, scanMsg, serverMsg >>

AwaitDoorLocked == /\ pc[Control] = "AwaitDoorLocked"
                   /\ binCommand.command = "finished"
                   /\ pc' = [pc EXCEPT ![Control] = "OpenTrapDoor"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, 
                                   userAuthorized, userTrash, binCommand, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, scanMsg, serverMsg >>

OpenTrapDoor == /\ pc[Control] = "OpenTrapDoor"
                /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
                /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapDoorOpened"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userAuthorized, userTrash, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, perm, req, 
                                scanMsg, serverMsg >>

AwaitTrapDoorOpened == /\ pc[Control] = "AwaitTrapDoorOpened"
                       /\ binCommand.command = "finished"
                       /\ pc' = [pc EXCEPT ![Control] = "ExtendRam"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, scanMsg, 
                                       serverMsg >>

ExtendRam == /\ pc[Control] = "ExtendRam"
             /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
             /\ pc' = [pc EXCEPT ![Control] = "AwaitRamExtended"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userAuthorized, userTrash, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, perm, req, scanMsg, serverMsg >>

AwaitRamExtended == /\ pc[Control] = "AwaitRamExtended"
                    /\ binCommand.command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "RetractRam"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scanMsg, 
                                    serverMsg >>

RetractRam == /\ pc[Control] = "RetractRam"
              /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
              /\ pc' = [pc EXCEPT ![Control] = "AwaitRamRetracted"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userAuthorized, userTrash, binSensor, scans, 
                              permissions, serverRequests, serverResponses, 
                              truckCommand, perm, req, scanMsg, serverMsg >>

AwaitRamRetracted == /\ pc[Control] = "AwaitRamRetracted"
                     /\ binCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "CloseTrapDoor"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, 
                                     userAuthorized, userTrash, binCommand, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scanMsg, 
                                     serverMsg >>

CloseTrapDoor == /\ pc[Control] = "CloseTrapDoor"
                 /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapDoorClosed"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userAuthorized, userTrash, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, perm, req, 
                                 scanMsg, serverMsg >>

AwaitTrapDoorClosed == /\ pc[Control] = "AwaitTrapDoorClosed"
                       /\ binCommand.command = "finished"
                       /\ pc' = [pc EXCEPT ![Control] = "CheckTruckNeeded"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       userAuthorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, scanMsg, 
                                       serverMsg >>

CheckTruckNeeded == /\ pc[Control] = "CheckTruckNeeded"
                    /\ IF ~TrashFitsCapacity(MaxUserTrash)
                          THEN /\ truckCommand' = [command |-> "request", bin |-> scanMsg.bin]
                          ELSE /\ TRUE
                               /\ UNCHANGED truckCommand
                    /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, 
                                    userAuthorized, userTrash, binCommand, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, perm, req, 
                                    scanMsg, serverMsg >>

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
\* Last modified Fri Oct 16 10:52:29 CEST 2026 by robin
\* Last modified Mon Oct 05 15:27:09 CEST 2026 by sva20
\* Last modified Mon Oct 05 13:41:28 CEST 2026 by sva20
