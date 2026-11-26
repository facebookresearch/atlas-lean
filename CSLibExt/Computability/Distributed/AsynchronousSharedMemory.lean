/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs

/-!
# The asynchronous shared-memory model

This is the interleaving model of Aspnes, *Notes on Theory of Distributed Systems*,
Chapter 16, §§16.1 and 16.3. Each atomic operation acts on a single shared object and
returns a value to the process that issued it. A chosen schedule determines the order
of steps; there is no clock and no simultaneous operation. Halting and crash-stop are
distinct local events, neither of which accesses shared memory.
-/

namespace Cslib.Distributed.AsynchronousSharedMemory

universe u v w x y

/-- A process has a local state while running; halted and crashed processes cannot take steps. -/
public inductive Status (State : Type u) where
  | running (state : State)
  | halted
  | crashed

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
  Returning `none` means the process is ready to halt. -/
  next : (p : Process) → LocalState p →
    Option (Σ o : Object, Σ op : Operation o, Reply o op → LocalState p)
  /-- An atomic operation produces a reply and the updated state of that object. -/
  apply : (o : Object) → (op : Operation o) → ObjectState o → Reply o op × ObjectState o

/-- The vector of process states and the vector of shared object states at one point in a run. -/
public structure Configuration (M : Model) where
  /-- The status and, when running, local state of every process. -/
  processState : (p : M.Process) → Status (M.LocalState p)
  /-- The state of every shared object. -/
  objectState : (o : M.Object) → M.ObjectState o

/-- The starting configuration, with every process running. -/
@[expose] public def Model.initial (M : Model) : Configuration M where
  processState p := .running (M.initialProcess p)
  objectState := M.initialObject

/-- One scheduled event: an atomic operation, a local halt, or a crash-stop event. -/
public inductive Event (M : Model) where
  | operate (process : M.Process) (object : M.Object) (operation : M.Operation object)
  | halt (process : M.Process)
  | crash (process : M.Process)

/-- Valid scheduled transitions. The selected process alone can change local state.
Only an atomic operation can change shared memory, and then only at its selected object. -/
public inductive Step (M : Model) : Configuration M → Event M → Configuration M → Prop where
  | operate {before after : Configuration M} {p : M.Process} {o : M.Object}
      {s : M.LocalState p} {op : M.Operation o} {resume : M.Reply o op → M.LocalState p}
      (running : before.processState p = .running s)
      (command : M.next p s = some ⟨o, op, resume⟩)
      (process : after.processState p = .running (resume (M.apply o op (before.objectState o)).1))
      (object : after.objectState o = (M.apply o op (before.objectState o)).2)
      (otherProcesses : ∀ q, q ≠ p → after.processState q = before.processState q)
      (otherObjects : ∀ a, a ≠ o → after.objectState a = before.objectState a) :
      Step M before (.operate p o op) after
  | halt {before after : Configuration M} {p : M.Process} {s : M.LocalState p}
      (running : before.processState p = .running s) (done : M.next p s = none)
      (process : after.processState p = .halted)
      (otherProcesses : ∀ q, q ≠ p → after.processState q = before.processState q)
      (objects : after.objectState = before.objectState) : Step M before (.halt p) after
  | crash {before after : Configuration M} {p : M.Process} {s : M.LocalState p}
      (running : before.processState p = .running s)
      (process : after.processState p = .crashed)
      (otherProcesses : ∀ q, q ≠ p → after.processState q = before.processState q)
      (objects : after.objectState = before.objectState) : Step M before (.crash p) after

/-- A halted or crashed process keeps that status under every subsequent step. -/
public theorem Step.stopped_preserved {M : Model} {before after : Configuration M}
    {event : Event M} {p : M.Process} (step : Step M before event after)
    (stopped : before.processState p = .halted ∨ before.processState p = .crashed) :
    after.processState p = before.processState p := by
  cases step with
  | operate running _ _ _ other _ => exact other p (by rintro rfl; simp [running] at stopped)
  | halt running _ _ other _ => exact other p (by rintro rfl; simp [running] at stopped)
  | crash running _ other _ => exact other p (by rintro rfl; simp [running] at stopped)

/-- A finite prefix of `n` scheduled events and `n + 1` configurations. -/
public structure FiniteExecution (M : Model) (n : Nat) where
  /-- The initial and successive configurations. -/
  configuration : Fin (n + 1) → Configuration M
  /-- The event between each consecutive pair of configurations. -/
  event : Fin n → Event M
  /-- The execution begins at the system's initial configuration. -/
  initial : configuration 0 = M.initial
  /-- Each event produces the next configuration by the one-step relation. -/
  step : ∀ i, Step M (configuration i.castSucc) (event i) (configuration i.succ)

/-- An infinite sequence of scheduled events and their successive configurations. -/
public structure InfiniteExecution (M : Model) where
  /-- The initial and successive configurations. -/
  configuration : Nat → Configuration M
  /-- The event between positions `i` and `i + 1`. -/
  event : Nat → Event M
  /-- The execution begins at the system's initial configuration. -/
  initial : configuration 0 = M.initial
  /-- Each event produces the next configuration by the one-step relation. -/
  step : ∀ i, Step M (configuration i) (event i) (configuration (i + 1))

/-- Fairness requires a process to perform atomic operations at arbitrarily late positions
unless it has halted or crashed. The stopping events themselves are not atomic operations.
This constrains schedules; it does not assume that every execution is fair. -/
@[expose] public def InfiniteExecution.Fair {M : Model} (run : InfiniteExecution M) : Prop :=
  ∀ p, (∃ i, (run.configuration i).processState p = .halted ∨
      (run.configuration i).processState p = .crashed) ∨
    ∀ n, ∃ i ≥ n, ∃ o op, run.event i = .operate p o op

end Cslib.Distributed.AsynchronousSharedMemory
