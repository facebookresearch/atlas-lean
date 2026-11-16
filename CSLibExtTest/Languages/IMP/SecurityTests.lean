/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Security tests for IMP
-/
module

public import CSLibExt.Languages.IMP.Security

/-!
# IMP security tests

Boundary checks for Volpano-Smith-Irvine typing and
termination-insensitive noninterference: accepted and rejected
programs, a typed preservation example, an untyped leak that is not a
counterexample, and the conditional high-guard loop.
-/

@[expose] public section

namespace Cslib.IMP

/-- Test environment: variable `0` is public, all others secret. -/
def testEnv (x : Nat) : SecLevel :=
  if x = 0 then .Low else .High

@[simp] theorem testEnv_zero : testEnv 0 = .Low := by simp [testEnv]

@[simp] theorem testEnv_one : testEnv 1 = .High := by simp [testEnv]

theorem testEnv_of_ne_zero {x : Nat} (h : x ≠ 0) :
    testEnv x = .High := by
  simp [testEnv, h]

/-- Initial states agreeing on public data, differing in the secret. -/
def sHi0 : State := fun x => if x = 0 then 5 else 0

def sHi9 : State := fun x => if x = 0 then 5 else 9

theorem test_init_lowEq : LowEq testEnv sHi0 sHi9 := by
  intro x hx
  simp only [sHi0, sHi9]
  by_cases h : x = 0
  · simp [h]
  · rw [testEnv_of_ne_zero h] at hx
    simp at hx

/-- `0 := 0 + 1` is typable at `Low`. -/
theorem test_assign_public_add :
    SecTyped testEnv .Low (.assign 0 (.add (.var 0) (.const 1))) :=
  SecTyped.assign _ _ _
    (by simp [AExp.label, SecLevel.join, SecLevel.le, testEnv])

/-- `1 := 0` is typable at `Low`. -/
theorem test_assign_secret_from_public :
    SecTyped testEnv .Low (.assign 1 (.var 0)) :=
  SecTyped.assign _ _ _
    (by simp [AExp.label, SecLevel.join, SecLevel.le, testEnv])

/-- Typable `0 := 0 + 1` preserves low-equivalence (via `tini`). -/
theorem test_tini_public_add : LowEq testEnv
    (Function.update sHi0 0 ((AExp.add (.var 0) (.const 1)).eval sHi0))
    (Function.update sHi9 0 ((AExp.add (.var 0) (.const 1)).eval sHi9)) := by
  have h1 : BigStep (.assign 0 (.add (.var 0) (.const 1))) sHi0
      (Function.update sHi0 0 ((AExp.add (.var 0) (.const 1)).eval sHi0)) :=
    BigStep.assign _ _ _
  have h2 : BigStep (.assign 0 (.add (.var 0) (.const 1))) sHi9
      (Function.update sHi9 0 ((AExp.add (.var 0) (.const 1)).eval sHi9)) :=
    BigStep.assign _ _ _
  exact SecTyped.tini test_assign_public_add test_init_lowEq h1 h2

/-- Both runs compute public result `6`. -/
theorem test_public_result_same :
    (Function.update sHi0 0 ((AExp.add (.var 0) (.const 1)).eval sHi0)) 0 = 6 ∧
    (Function.update sHi9 0 ((AExp.add (.var 0) (.const 1)).eval sHi9)) 0 = 6 := by
  constructor
  · simp only [Function.update]
    decide
  · simp only [Function.update]
    decide

/-- `0 := 1` (secret to public) is rejected at `Low`. -/
theorem test_assign_public_from_secret_rejected :
    ¬ SecTyped testEnv .Low (.assign 0 (.var 1)) := by
  intro h
  cases h with
  | assign _ _ _ hle =>
      simp [AExp.label, SecLevel.join, SecLevel.le, testEnv] at hle

/-- `if 1 ≠ 0 then 0 := 1 else skip` is rejected at `Low`. -/
theorem test_branch_secret_guard_rejected :
    ¬ SecTyped testEnv .Low
      (.ite (.not (.eq (.var 1) (.const 0)))
        (.assign 0 (.const 1)) .skip) := by
  intro h
  cases h with
  | ite _ _ _ _ ht1 ht2 =>
      cases ht1 with
      | assign _ _ _ hle =>
          simp [AExp.label, BExp.label, SecLevel.join, SecLevel.le,
            testEnv] at hle

/-- Untyped `0 := 1` runs on the two initial states. -/
theorem test_untyped_runs :
    BigStep (.assign 0 (.var 1)) sHi0
      (Function.update sHi0 0 (sHi0 1)) ∧
    BigStep (.assign 0 (.var 1)) sHi9
      (Function.update sHi9 0 (sHi9 1)) := by
  constructor
  · exact BigStep.assign _ _ _
  · exact BigStep.assign _ _ _

/-- Those untyped finals are low-inequivalent: not a `tini` counterexample. -/
theorem test_untyped_flow_breaks_lowEq :
    ¬ LowEq testEnv (Function.update sHi0 0 (sHi0 1))
      (Function.update sHi9 0 (sHi9 1)) := by
  intro h
  have h0 := h 0 testEnv_zero
  simp only [Function.update] at h0
  simp [sHi0, sHi9] at h0

/-- `while 1 ≠ 0 do skip` is typable at `Low`. -/
theorem test_while_high_guard_typable :
    SecTyped testEnv .Low
      (.while (.not (.eq (.var 1) (.const 0))) .skip) := by
  apply SecTyped.while
  exact SecTyped.skip _

/-- Two low-equal secret-zero states that genuinely differ elsewhere. -/
def sA : State := fun x => if x = 0 then 5 else 0

def sB : State := fun x => if x = 0 then 5 else if x = 2 then 7 else 0

theorem test_while_init_lowEq : LowEq testEnv sA sB := by
  intro x hx
  simp only [sA, sB]
  by_cases h : x = 0
  · simp [h]
  · rw [testEnv_of_ne_zero h] at hx
    simp at hx

theorem test_guard_false_A :
    (BExp.not (.eq (.var 1) (.const 0))).eval sA = false := by
  decide

theorem test_guard_false_B :
    (BExp.not (.eq (.var 1) (.const 0))).eval sB = false := by
  decide

theorem test_run_A :
    BigStep (.while (.not (.eq (.var 1) (.const 0))) .skip) sA sA :=
  BigStep.whileFalse test_guard_false_A

theorem test_run_B :
    BigStep (.while (.not (.eq (.var 1) (.const 0))) .skip) sB sB :=
  BigStep.whileFalse test_guard_false_B

/-- Conditional `tini` use on two terminating high-guard runs. -/
theorem test_while_tini_two_runs : LowEq testEnv sA sB :=
  SecTyped.tini test_while_high_guard_typable test_while_init_lowEq
    test_run_A test_run_B

/-- Non-vacuity: the two states genuinely differ. -/
theorem test_states_differ : sA 2 ≠ sB 2 := by
  decide

/-
Termination channel note: with a nonzero secret the guard stays true
and `skip` never changes it, so only secret-zero states terminate
above. `tini` claims nothing about divergent runs, and no divergence
theorem is stated here.
-/

#print axioms testEnv
#print axioms testEnv_zero
#print axioms testEnv_one
#print axioms testEnv_of_ne_zero
#print axioms sHi0
#print axioms sHi9
#print axioms test_init_lowEq
#print axioms test_assign_public_add
#print axioms test_assign_secret_from_public
#print axioms test_tini_public_add
#print axioms test_public_result_same
#print axioms test_assign_public_from_secret_rejected
#print axioms test_branch_secret_guard_rejected
#print axioms test_untyped_runs
#print axioms test_untyped_flow_breaks_lowEq
#print axioms test_while_high_guard_typable
#print axioms sA
#print axioms sB
#print axioms test_while_init_lowEq
#print axioms test_guard_false_A
#print axioms test_guard_false_B
#print axioms test_run_A
#print axioms test_run_B
#print axioms test_while_tini_two_runs
#print axioms test_states_differ
#print axioms SecLevel
#print axioms SecLevel.le
#print axioms SecLevel.join
#print axioms SecLevel.decLe
#print axioms SecLevel.le_low
#print axioms SecLevel.le_high_high
#print axioms SecLevel.not_le_high_low
#print axioms SecLevel.le_refl
#print axioms SecLevel.of_le_low
#print axioms SecLevel.eq_high_of_le_high
#print axioms SecLevel.join_high_left
#print axioms SecLevel.join_high_right
#print axioms SecLevel.join_low_left
#print axioms SecLevel.join_low_right
#print axioms SecLevel.join_eq_low_iff
#print axioms SecLevel.eq_high_of_ne_low
#print axioms SecEnv
#print axioms LowEq
#print axioms LowEq_refl
#print axioms LowEq_symm
#print axioms LowEq_trans
#print axioms LowEq_update_high
#print axioms LowEq_update_low
#print axioms LowEq_update_high_both
#print axioms AExp.label
#print axioms AExp.label_const
#print axioms AExp.label_var
#print axioms AExp.label_add
#print axioms AExp.label_sub
#print axioms AExp.label_mul
#print axioms AExp.eval_eq_of_low_label
#print axioms BExp.label
#print axioms BExp.label_truth
#print axioms BExp.label_eq
#print axioms BExp.label_le
#print axioms BExp.label_not
#print axioms BExp.label_and
#print axioms BExp.eval_eq_of_low_label
#print axioms SecTyped
#print axioms SecTyped.confinement_aux
#print axioms SecTyped.confinement
#print axioms SecTyped.while_high_body
#print axioms SecTyped.tini_aux
#print axioms SecTyped.tini

end Cslib.IMP
