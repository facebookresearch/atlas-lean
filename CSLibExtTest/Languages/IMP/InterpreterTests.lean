/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for fuelled IMP evaluation
-/
module

import CSLibExt.Languages.IMP.Interpreter

/-!
# Interpreter tests

Executable checks for `exec`: fuel-`0` failure, single commands,
compound programs, a diverging loop, factorial and gcd fixtures, and
instantiations of soundness, completeness, and monotonicity. States
are observed at finitely many variables, never compared whole.
-/

namespace Cslib.IMP

/-- All-zero initial state. -/
def init0 : State := fun _ => 0

/-- Initial state with variable `0` set to `5`. -/
def init5 : State := Function.update init0 0 5

/-- Countdown input: variable `0` set to `4`. -/
def init4 : State := Function.update init0 0 4

/-- Gcd input `(12, 18)` on variables `0` and `1`. -/
def initGcd : State :=
  Function.update (Function.update init0 0 12) 1 18

/-- Two assignments: `x0 := 3; x1 := x0 + 4`. -/
def seqProg : Cmd :=
  .seq (.assign 0 (.const 3)) (.assign 1 (.add (.var 0) (.const 4)))

/-- Branch on whether `x0` is zero. -/
def iteProg : Cmd :=
  .ite (.eq (.var 0) (.const 0)) (.assign 1 (.const 10))
    (.assign 1 (.const 20))

/-- Loop with a false guard over `x0`. -/
def whileFalseProg : Cmd :=
  .while (.eq (.var 0) (.const 99)) (.assign 0 (.const 1))

/-- Diverging loop: `while true do skip`. -/
def loopForever : Cmd := .while (.truth true) .skip

/-- Countdown factorial on `x0` with accumulator `x1`. -/
def factProg : Cmd :=
  .seq (.assign 1 (.const 1))
    (.while (.not (.eq (.var 0) (.const 0)))
      (.seq (.assign 1 (.mul (.var 1) (.var 0)))
        (.assign 0 (.sub (.var 0) (.const 1)))))

/-- Subtraction gcd on `x0` and `x1`. -/
def gcdProg : Cmd :=
  .while (.not (.eq (.var 0) (.var 1)))
    (.ite (.le (.var 0) (.var 1))
      (.assign 1 (.sub (.var 1) (.var 0)))
      (.assign 0 (.sub (.var 0) (.var 1))))

theorem zero_fuel_assign_none :
    exec 0 (.assign 0 (.const 1)) init0 = none :=
  rfl

theorem zero_fuel_skip_none : exec 0 .skip init0 = none :=
  rfl

theorem skip_fuel_one :
    (exec 1 .skip init0).map (fun t => t 7) = some 0 := by
  decide

theorem assign_updated :
    (exec 1 (.assign 0 (.const 5)) init0).map (fun t => t 0) =
      some 5 := by
  decide

theorem assign_untouched :
    (exec 1 (.assign 0 (.const 5)) init0).map (fun t => t 1) =
      some 0 := by
  decide

theorem seq_two_assigns :
    (exec 3 seqProg init0).map (fun t => (t 0, t 1)) =
      some (3, 7) := by
  decide

theorem ite_true_branch :
    (exec 3 iteProg init0).map (fun t => t 1) = some 10 := by
  decide

theorem ite_false_branch :
    (exec 3 iteProg init5).map (fun t => t 1) = some 20 := by
  decide

theorem while_false_guard :
    (exec 3 whileFalseProg init0).map (fun t => t 0) = some 0 := by
  decide

theorem loop_none_1 : exec 1 loopForever init0 = none :=
  rfl

theorem loop_none_5 : exec 5 loopForever init0 = none :=
  rfl

theorem loop_none_12 : exec 12 loopForever init0 = none :=
  rfl

theorem factorial_four :
    (exec 12 factProg init4).map (fun t => (t 0, t 1)) =
      some (0, 24) := by
  decide

theorem gcd_twelve_eighteen :
    (exec 10 gcdProg initGcd).map (fun t => (t 0, t 1)) =
      some (6, 6) := by
  decide

theorem sound_seq :
    ∃ t, BigStep seqProg init0 t ∧ t 0 = 3 ∧ t 1 = 7 := by
  have h3 : (exec 3 seqProg init0).map (fun t => (t 0, t 1)) =
      some (3, 7) := by
    decide
  cases ht : exec 3 seqProg init0 with
  | none =>
      simp [ht] at h3
  | some t =>
      simp [ht] at h3
      exact ⟨t, exec_sound ht, h3.1, h3.2⟩

theorem complete_skip :
    ∃ fuel, exec fuel .skip init0 = some init0 :=
  exists_fuel_of_bigStep (BigStep.skip init0)

theorem complete_seq : ∃ fuel, exec fuel seqProg init0 =
    some (Function.update (Function.update init0 0 3) 1 7) :=
  exists_fuel_of_bigStep
    (BigStep.seq (BigStep.assign init0 0 (.const 3))
      (BigStep.assign _ 1 (.add (.var 0) (.const 4))))

theorem mono_seq :
    (exec 10 seqProg init0).map (fun t => (t 0, t 1)) =
      some (3, 7) := by
  have h3 : (exec 3 seqProg init0).map (fun t => (t 0, t 1)) =
      some (3, 7) := by
    decide
  cases ht : exec 3 seqProg init0 with
  | none =>
      simp [ht] at h3
  | some t =>
      simp [ht] at h3
      have h10 := exec_mono (show 3 ≤ 10 by decide) ht
      simp [h10, h3]

end Cslib.IMP

#print axioms Cslib.IMP.sound_seq
#print axioms Cslib.IMP.complete_skip
#print axioms Cslib.IMP.complete_seq
#print axioms Cslib.IMP.mono_seq
