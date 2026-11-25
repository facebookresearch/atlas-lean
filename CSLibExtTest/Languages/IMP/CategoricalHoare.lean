/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.CategoricalHoare

/-!
# Worked categorical Hoare proofs for IMP

Repeated subtraction computes quotient and remainder: variable 0 is the remainder
and variable 1 the quotient. The invariant is `remainder + quotient * divisor = n`.
The loop proof below uses the categorical invariant characterization, rather than
the existing IMP while rule. These are partial-correctness claims; the final
diverging-loop example explicitly prevents reading them as termination theorems.
-/

@[expose] public section
open CategoryTheory CategoryTheory.VerificationFunctor
namespace Cslib.IMP.CategoricalHoareTests
open CategoricalHoare

example (c : Cmd) (P Q : Assertion) :
    VerificationFunctor.Triple PowersetVerification.verification
      (commandRel c) {s | P s} {s | Q s} ↔
      Valid P c Q := triple_iff_valid c P Q

example (b : BExp) (c : Cmd) :
    commandRel (.while b c) = SumRelCat.symmetricTrace.trace (loopBody b c) :=
  commandRel_while b c

/-- Subtract the divisor and increment the quotient. -/
def divideBody (d : Nat) : Cmd :=
  .seq (.assign 0 (.sub (.var 0) (.const d)))
    (.assign 1 (.add (.var 1) (.const 1)))

/-- Repeated subtraction, with the quotient supplied initially as zero. -/
def divide (d : Nat) : Cmd := .while (.le (.const d) (.var 0)) (divideBody d)

/-- One guarded iteration preserves the division equation. -/
theorem divideBody_valid (d n : Nat) :
    Valid (fun s => s 0 + s 1 * d = n ∧
      (BExp.le (.const d) (.var 0)).eval s = true)
      (divideBody d) (fun s => s 0 + s 1 * d = n) := by
  refine Valid.consequence ?_
    (Valid.seq (Valid.assign _ 0 (.sub (.var 0) (.const d)))
      (Valid.assign _ 1 (.add (.var 1) (.const 1)))) (Assertion.entails_refl _)
  intro s hs
  have hle : d ≤ s 0 := BExp.eval_le_eq_true.mp hs.2
  simp [Assertion.subst, AExp.eval, Function.update]
  rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_right_comm, Nat.sub_add_cancel hle]
  exact hs.1

/-- Categorical feedback verifies quotient and remainder for every terminating run. -/
theorem divide_valid (d n : Nat) :
    Valid (fun s => s 0 = n ∧ s 1 = 0) (divide d)
      (fun s => s 0 + s 1 * d = n ∧ s 0 < d) := by
  have hloop := (while_valid_iff_invariant (.le (.const d) (.var 0)) (divideBody d)
    (fun s => s 0 + s 1 * d = n)
    (fun s => s 0 + s 1 * d = n ∧ (BExp.le (.const d) (.var 0)).eval s = false)).mpr
      ⟨{s | s 0 + s 1 * d = n}, loopBody_invariant _ _ _ (divideBody_valid d n)⟩
  refine Valid.consequence ?_ hloop ?_
  · intro s hs
    simp [hs.1, hs.2]
  · intro s hs
    refine ⟨hs.1, ?_⟩
    have hn : ¬ d ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const d) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hle
      rw [hs.2] at ht
      contradiction
    omega

-- The same proof can be consumed as a categorical triple or an existing IMP derivation.
example (d n : Nat) :
    VerificationFunctor.Triple PowersetVerification.verification (commandRel (divide d))
      {s | s 0 = n ∧ s 1 = 0} {s | s 0 + s 1 * d = n ∧ s 0 < d} :=
  (triple_iff_valid _ _ _).mpr (divide_valid d n)

example (d n : Nat) :
    IMP.Derivable (fun s => s 0 = n ∧ s 1 = 0) (divide d)
      (fun s => s 0 + s 1 * d = n ∧ s 0 < d) :=
  IMP.Derivable.complete (divide_valid d n)

-- Both zero iterations and repeated iterations are covered by the theorem.
example : Valid (fun s => s 0 = 2 ∧ s 1 = 0) (divide 5)
    (fun s => s 0 + s 1 * 5 = 2 ∧ s 0 < 5) := divide_valid 5 2
example : Valid (fun s => s 0 = 17 ∧ s 1 = 0) (divide 5)
    (fun s => s 0 + s 1 * 5 = 17 ∧ s 0 < 5) := divide_valid 5 17

/-- A concrete nonempty input for the execution probes. -/
private def sampleState (r q : Nat) : State := fun k =>
  if k = 0 then r else if k = 1 then q else 0

-- Actual executions establish nonvacuity independently of the validity theorem.
example : BigStep (divide 5) (sampleState 2 0) (sampleState 2 0) :=
  .whileFalse (by decide)

example : ∃ t, BigStep (divide 5) (sampleState 7 0) t ∧ t 0 = 2 ∧ t 1 = 1 := by
  let s := sampleState 7 0
  let m := Function.update s 0 (s 0 - 5)
  let t := Function.update m 1 (m 1 + 1)
  refine ⟨t, ?_, ?_, ?_⟩
  · exact .whileTrue (by decide) (.seq (.assign s 0 _) (.assign m 1 _))
      (.whileFalse (by decide))
  · decide
  · decide

/-- Divergence remains possible: partial correctness does not manufacture a final state. -/
def spin : Cmd := .while (.truth true) .skip

theorem spin_no_run {s t : State} : ¬ BigStep spin s t := by
  intro h
  obtain ⟨n, hn⟩ := Iterates.exists_of_bigStep h
  clear h
  induction hn with
  | exit h => simp at h
  | step _ _ _ ih => exact ih

example : VerificationFunctor.Triple PowersetVerification.verification
    (commandRel spin) Set.univ ∅ :=
  (triple_iff_valid _ _ _).mpr (fun _ _ _ h => spin_no_run h)

example : ¬ TValid (fun _ => True) spin (fun _ => True) := by
  intro h
  obtain ⟨t, ht, _⟩ := h (s := fun _ => 0) trivial
  exact spin_no_run ht

-- A false specification for a terminating instruction is rejected.
example : ¬ VerificationFunctor.Triple PowersetVerification.verification
    (commandRel .skip) Set.univ ∅ := by
  intro h
  exact (triple_iff_valid _ _ _).mp h (initial := fun _ => 0) trivial (.skip _)
end Cslib.IMP.CategoricalHoareTests
