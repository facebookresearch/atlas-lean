/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# The asynchronous shared-memory model

This is the interleaving model of Aspnes, *Notes on Theory of Distributed Systems*,
Chapter 16, §§16.1 and 16.3. Each atomic operation acts on a single shared object and
returns a value to the process that issued it. A chosen schedule determines the order
of steps; there is no clock and there are no simultaneous operations. A process halts
as soon as it has no next operation. A crash is a separate event that does not access memory.
-/

namespace Cslib.Distributed.AsynchronousSharedMemory

universe u v w x y

/-- The execution status of a process, together with its current local state. Halting and
crashing disable further steps without erasing the local state. -/
public inductive Status (State : Type u) where
  | running (state : State)
  | halted (state : State)
  | crashed (state : State)

/-- The process and object interfaces of an asynchronous shared-memory system.

A process chooses its next atomic operation and a continuation based on its local state alone.
An object gives a reply and a new state based on the selected operation and its own state.
There are finitely many processes, and neither operations nor reply types need to be uniform. -/
public structure Model where
  /-- The process identifiers; a system with `n` processes can use `Fin n`. -/
  Process : Type u
  /-- The system has finitely many processes. -/
  finiteProcesses : Finite Process
  /-- The shared object identifiers. -/
  Object : Type v
  /-- The running local state of each process. -/
  LocalState : Process → Type w
  /-- The private state of each shared object. -/
  ObjectState : Object → Type x
  /-- The atomic operations supported by an object, including their arguments. -/
  Operation : Object → Type y
  /-- The type of reply to a selected operation on an object. -/
  Reply : (o : Object) → Operation o → Type w
  /-- The initial local state of each process. -/
  initialProcess : (p : Process) → LocalState p
  /-- The initial contents of each object. -/
  initialObject : (o : Object) → ObjectState o
  /-- A process selects one object, an operation, and how to continue with its reply.
  Returning `none` makes this a halting state. -/
  next : (p : Process) → LocalState p →
    Option (Σ o : Object, Σ op : Operation o, Reply o op → LocalState p)
  /-- An atomic operation produces a reply and the updated state of that object. -/
  apply : (o : Object) → (op : Operation o) → ObjectState o → Reply o op × ObjectState o

/-- Classify a process's local state as halted when it has no next operation, and as running
otherwise. Both outcomes retain that state. This applies on initialization and after an
operation, not on an additional turn of the schedule. -/
@[expose] public def Model.localStatus (M : Model) (p : M.Process) (s : M.LocalState p) :
    Status (M.LocalState p) :=
  match M.next p s with
  | none => .halted s
  | some _ => .running s

/-- The vector of process states and the vector of shared object states at one point in a run. -/
public structure Configuration (M : Model) where
  /-- The status and current local state of every process. -/
  processState : (p : M.Process) → Status (M.LocalState p)
  /-- The state of every shared object. -/
  objectState : (o : M.Object) → M.ObjectState o

/-- The starting configuration. A process with no initial operation is already halted. -/
@[expose] public def Model.initial (M : Model) : Configuration M where
  processState p := M.localStatus p (M.initialProcess p)
  objectState := M.initialObject

/-- One scheduled event: a running process performs its chosen atomic operation or crashes.
Normal halting is part of entering a local state, not an event. -/
public inductive Event (M : Model) where
  | operate (process : M.Process) (object : M.Object) (operation : M.Operation object)
  | crash (process : M.Process)

/-- Valid scheduled transitions. The operation must be the one chosen by the running process;
its reply determines that process's next local state, and the process halts if that state has
no next operation. An operation can change only the selected object's state and the selected
process's status. A crash is possible only for a running process with a pending operation,
and marks its local state as crashed without changing that state or any shared object. -/
public inductive Step (M : Model) : Configuration M → Event M → Configuration M → Prop where
  | operate {before after : Configuration M} {p : M.Process} {o : M.Object}
      {s : M.LocalState p} {op : M.Operation o} {resume : M.Reply o op → M.LocalState p}
      (running : before.processState p = .running s)
      (command : M.next p s = some ⟨o, op, resume⟩)
      (process : after.processState p =
        M.localStatus p (resume (M.apply o op (before.objectState o)).1))
      (object : after.objectState o = (M.apply o op (before.objectState o)).2)
      (otherProcesses : ∀ q, q ≠ p → after.processState q = before.processState q)
      (otherObjects : ∀ a, a ≠ o → after.objectState a = before.objectState a) :
      Step M before (.operate p o op) after
  | crash {before after : Configuration M} {p : M.Process} {s : M.LocalState p}
      (running : before.processState p = .running s) (pending : M.next p s ≠ none)
      (process : after.processState p = .crashed s)
      (otherProcesses : ∀ q, q ≠ p → after.processState q = before.processState q)
      (objects : after.objectState = before.objectState) : Step M before (.crash p) after

/-- A halted or crashed process retains its local state and status under every subsequent step. -/
public theorem Step.stopped_preserved {M : Model} {before after : Configuration M}
    {event : Event M} {p : M.Process} {s : M.LocalState p} (step : Step M before event after)
    (stopped : before.processState p = .halted s ∨ before.processState p = .crashed s) :
    after.processState p = before.processState p := by
  cases step with
  | operate running _ _ _ other _ => exact other p (by rintro rfl; simp [running] at stopped)
  | crash running _ _ other _ => exact other p (by rintro rfl; simp [running] at stopped)

/-- The labelled transition system whose states are shared-memory configurations and whose
labels and transitions are the scheduled events and the one-step rules, respectively. -/
@[expose] public def Model.lts (M : Model) : LTS (Configuration M) (Event M) where
  Tr := Step M

/-- A finite execution starts in the model's initial configuration and follows each event
legally to the next configuration, ending at `last`. The configuration list has one more
entry than the event list, including a single initial configuration in a zero-step execution. -/
@[expose] public def FiniteExecution (M : Model) (events : List (Event M)) (last : Configuration M)
    (configurations : List (Configuration M)) : Prop :=
  M.lts.Execution M.initial events last configurations

/-- An infinite execution starts in the model's initial configuration. Each scheduled event
must be a valid transition from its preceding configuration to the next one. -/
public structure InfiniteExecution (M : Model) where
  /-- The initial and successive configurations. -/
  configuration : Nat → Configuration M
  /-- The event between positions `i` and `i + 1`. -/
  event : Nat → Event M
  /-- The execution begins at the system's initial configuration. -/
  initial : configuration 0 = M.initial
  /-- The configurations and events form an infinite execution of the model's transition system. -/
  execution : M.lts.OmegaExecution configuration event

/-- Fairness requires a process to perform atomic operations at arbitrarily late positions
unless it has halted or crashed. A crash itself is not an atomic operation.
This constrains schedules; it does not assume that every execution is fair. -/
@[expose] public def InfiniteExecution.Fair {M : Model} (run : InfiniteExecution M) : Prop :=
  ∀ p, (∃ i s, (run.configuration i).processState p = .halted s ∨
      (run.configuration i).processState p = .crashed s) ∨
    ∀ n, ∃ i ≥ n, ∃ o op, run.event i = .operate p o op

end Cslib.Distributed.AsynchronousSharedMemory
