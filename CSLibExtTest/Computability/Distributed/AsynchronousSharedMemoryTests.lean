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

-- Process `false` swaps once and is then ready to halt. Process `true` keeps reading.
-- The other object is untouched. Writes and reads illustrate distinct reply types.
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
    else if s = 0 then some ⟨false, .swap 9, id⟩ else none
  apply _
    | .read, s => (s, s)
    | .swap n, s => (s, n)
    | .write n, _ => ((), n)

private def afterSwap : Configuration registers where
  processState _ := .running 7
  objectState o := if o then 99 else 9

private def afterRead : Configuration registers where
  processState p := .running (if p then 9 else 7)
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

private theorem readAfterSwap : Step registers afterSwap (.operate true false .read) afterRead := by
  refine .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl ?_ ?_
  · intro q h
    cases q with
    | false => rfl
    | true => exact (h rfl).elim
  · intro _ _
    rfl

example : FiniteExecution registers 2 where
  configuration i := if i.val = 0 then registers.initial else if i.val = 1 then afterSwap
    else afterRead
  event i := if i.val = 0 then .operate false false (.swap 9) else .operate true false .read
  initial := rfl
  step i := by
    by_cases h : i.val = 0
    · simpa [h] using swapStep
    · have h₁ : i.val = 1 := by omega
      simpa [h₁] using readAfterSwap

private theorem readInitial : Step registers registers.initial (.operate true false .read)
    registers.initial :=
  .operate (s := (7 : Nat)) (resume := id) rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

private def starvation : InfiniteExecution registers where
  configuration _ := registers.initial
  event _ := .operate true false .read
  initial := rfl
  step _ := readInitial

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
  refine .crash (s := (0 : Nat)) rfl rfl ?_ rfl
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
  step
    | 0 => crashStep
    | _ + 1 => readAfterCrash

-- After the explicit crash event, only the reader must take steps arbitrarily late.
example : crashRun.Fair := by
  intro p
  cases p with
  | false => exact Or.inl ⟨1, Or.inr rfl⟩
  | true => exact Or.inr fun n => ⟨n + 1, Nat.le_succ n, false, .read, rfl⟩

private def afterHalt : Configuration registers where
  processState p := if p then .running 7 else .halted
  objectState := afterSwap.objectState

example : Step registers afterSwap (.halt false) afterHalt := by
  refine .halt (s := (7 : Nat)) rfl rfl rfl ?_ rfl
  intro q h
  cases q with
  | false => exact (h rfl).elim
  | true => rfl

example (c : Configuration registers) (o : registers.Object) (op : registers.Operation o) :
    ¬ Step registers afterCrash (.operate false o op) c := by
  intro h
  cases h with
  | operate running _ _ _ _ _ => cases running

end Cslib.Distributed.AsynchronousSharedMemory
