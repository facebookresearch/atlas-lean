/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.AsynchronousSharedMemory

namespace Cslib.Distributed.AsynchronousSharedMemory

private inductive RegisterOp where
  | read
  | write (value : Nat)
  | swap (value : Nat)

-- Process `false` swaps, then reads and halts; `true` repeats reads. Neither touches object `true`.
private abbrev registers : Model where
  Process := Bool
  finiteProcesses := inferInstance
  Object := Bool
  LocalState _ := Nat
  ObjectState _ := Nat
  Operation _ := RegisterOp
  Reply _
    | .read | .swap _ => Nat
    | .write _ => Unit
  initialProcess p := if p then 7 else 0
  initialObject o := if o then 99 else 7
  next p s := if p then some ⟨false, .read, id⟩
    else if s = 0 then some ⟨false, .swap 9, id⟩
    else if s = 7 then some ⟨false, .read, id⟩ else none
  apply _
    | .read, s => (s, s)
    | .swap n, s => (s, n)
    | .write n, _ => ((), n)

private def afterSwap : Configuration registers where
  processState _ := .running 7
  objectState o := if o then 99 else 9

private def afterFinalRead : Configuration registers where
  processState p := if p then .running 7 else .halted
  objectState := afterSwap.objectState

private def afterReaderRead : Configuration registers where
  processState p := if p then .running 9 else .halted
  objectState := afterSwap.objectState

private theorem swapStep : Step registers registers.initial (.operate false false (.swap 9))
    afterSwap := by
  refine .operate (s := (0 : Nat)) (resume := id) rfl rfl rfl rfl ?_ ?_
  · intro q h
    cases q with
    | false => exact (h rfl).elim
    | true => rfl
  · intro o h
    cases o with
    | false => exact (h rfl).elim
    | true => rfl

private theorem finalReadStep : Step registers afterSwap (.operate false false .read)
    afterFinalRead := by
  refine .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl ?_ (fun _ _ => rfl)
  intro q h
  cases q with
  | false => exact (h rfl).elim
  | true => rfl

private theorem readerStep : Step registers afterFinalRead (.operate true false .read)
    afterReaderRead := by
  refine .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl ?_ (fun _ _ => rfl)
  intro q h
  cases q with
  | false => rfl
  | true => exact (h rfl).elim

private theorem steadyReader : Step registers afterReaderRead (.operate true false .read)
    afterReaderRead :=
  .operate (s := (9 : Nat)) (resume := id) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

example : FiniteExecution registers
    [.operate false false (.swap 9), .operate false false .read, .operate true false .read]
    afterReaderRead [registers.initial, afterSwap, afterFinalRead, afterReaderRead] :=
  LTS.Execution.stepL swapStep (.stepL finalReadStep (.of_tr readerStep))

private def normalTermination : InfiniteExecution registers where
  configuration
    | 0 => registers.initial
    | 1 => afterSwap
    | 2 => afterFinalRead
    | _ + 3 => afterReaderRead
  event
    | 0 => .operate false false (.swap 9)
    | 1 => .operate false false .read
    | _ + 2 => .operate true false .read
  initial := rfl
  execution := fun
    | 0 => swapStep
    | 1 => finalReadStep
    | 2 => readerStep
    | _ + 3 => steadyReader

-- The final read suffices: no extra scheduler turn or artificial halt event is needed.
example : normalTermination.Fair := by
  intro p
  cases p with
  | false => exact Or.inl ⟨2, Or.inl rfl⟩
  | true => exact Or.inr fun n => ⟨n + 2, by omega, false, .read, rfl⟩

-- An initially terminal local state is already halted.
example : ({ registers with initialProcess := fun _ => 9 } : Model).initial.processState false =
    .halted := rfl

private theorem readInitial : Step registers registers.initial (.operate true false .read)
    registers.initial :=
  .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

private def starvation : InfiniteExecution registers where
  configuration _ := registers.initial
  event _ := .operate true false .read
  initial := rfl
  execution _ := readInitial

-- An always-running process that is never selected cannot satisfy fairness.
example : ¬ starvation.Fair := by
  intro fair
  rcases fair false with ⟨i, stop | stop⟩ | often
  · change Status.running 0 = Status.halted at stop
    cases stop
  · change Status.running 0 = Status.crashed at stop
    cases stop
  · obtain ⟨i, _, o, op, h⟩ := often 0
    change Event.operate (M := registers) true false .read = .operate false o op at h
    cases h

private def afterCrash : Configuration registers where
  processState p := if p then .running 7 else .crashed
  objectState := registers.initial.objectState

private theorem crashStep : Step registers registers.initial (.crash false) afterCrash := by
  refine .crash (s := (0 : Nat)) rfl (by intro impossible; cases impossible) rfl ?_ rfl
  intro q h
  cases q with
  | false => exact (h rfl).elim
  | true => rfl

private theorem readAfterCrash : Step registers afterCrash (.operate true false .read) afterCrash :=
  .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

private def crashRun : InfiniteExecution registers where
  configuration
    | 0 => registers.initial
    | _ + 1 => afterCrash
  event
    | 0 => .crash false
    | _ + 1 => .operate true false .read
  initial := rfl
  execution := fun
    | 0 => crashStep
    | _ + 1 => readAfterCrash

example : crashRun.Fair := by
  intro p
  cases p with
  | false => exact Or.inl ⟨1, Or.inr rfl⟩
  | true => exact Or.inr fun n => ⟨n + 1, Nat.le_succ n, false, .read, rfl⟩

-- A halted process cannot instead be counted as crashed.
example (c : Configuration registers) : ¬ Step registers afterFinalRead (.crash false) c := by
  intro h
  cases h with
  | crash running _ _ _ _ => cases running

example (c : Configuration registers) (o : registers.Object) (op : registers.Operation o) :
    ¬ Step registers afterCrash (.operate false o op) c := by
  intro h
  cases h with
  | operate running _ _ _ _ _ => cases running

-- The scheduler cannot substitute a read for the process's chosen swap.
example (c : Configuration registers) :
    ¬ Step registers registers.initial (.operate false false .read) c := by
  intro h
  cases h with
  | operate running command _ _ _ _ =>
    have hs := Status.running.inj running
    subst_vars
    have ho := congrArg (fun cmd => cmd.2.1) (Option.some.inj command)
    cases ho

private def touchesOtherObject : Configuration registers where
  processState := afterSwap.processState
  objectState o := if o then 100 else 9

example :
    ¬ Step registers registers.initial (.operate false false (.swap 9)) touchesOtherObject := by
  intro h
  cases h with
  | operate _ _ _ _ _ otherObjects =>
    have bad := otherObjects true (by decide)
    change (100 : Nat) = 99 at bad
    cases bad

end Cslib.Distributed.AsynchronousSharedMemory
