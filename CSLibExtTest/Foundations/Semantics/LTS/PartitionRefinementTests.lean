/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.PartitionRefinement

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS.PartitionRefinementTests

/-- State `0` has no transition; states `1` and `2` each loop on themselves. -/
def loopLTS : LTS (Fin 3) Unit := ⟨fun a _ b => a ≠ 0 ∧ b = a⟩

/-- Refinement separates `0` from `1` in the first round, by direct
evaluation: `1` can move and `0` cannot. -/
theorem not_refineIter_one_zero_one : ¬ loopLTS.refineIter 1 0 1 := by
  simp only [refineIter, refineStep, loopLTS]
  decide

/-- The stabilized iterate does not relate `0` and `1`, by direct evaluation. -/
theorem not_refineIter_card_zero_one :
    ¬ loopLTS.refineIter (Fintype.card (Fin 3)) 0 1 := by
  rw [Fintype.card_fin]
  simp [refineIter, refineStep, loopLTS]

/-- The separation found in round one persists, since the iterates decrease. -/
example : ¬ loopLTS.refineIter 3 0 1 := fun h =>
  not_refineIter_one_zero_one
    (loopLTS.refineIter_antitone 1 0 1 (loopLTS.refineIter_antitone 2 0 1 h))

/-- The stabilized iterate relates the distinct looping states `1` and `2`, by
direct evaluation. -/
theorem refineIter_card_one_two : loopLTS.refineIter (Fintype.card (Fin 3)) 1 2 := by
  rw [Fintype.card_fin]
  simp [refineIter, refineStep, loopLTS]

/-- The correctness theorem turns the computed separation into
non-bisimilarity. -/
theorem not_homBisimilarity_zero_one : ¬ loopLTS.HomBisimilarity 0 1 := fun h =>
  not_refineIter_card_zero_one
    ((loopLTS.refineIter_card_iff_homBisimilarity 0 1).mpr h)

/-- The correctness theorem turns the computed relation into bisimilarity of
the distinct states `1` and `2`. -/
theorem homBisimilarity_one_two : loopLTS.HomBisimilarity 1 2 :=
  (loopLTS.refineIter_card_iff_homBisimilarity 1 2).mp refineIter_card_one_two

/-- Every iterate is an equivalence relation, so it relates each state to
itself. -/
example (k : ℕ) (a : Fin 3) : loopLTS.refineIter k a a :=
  (loopLTS.refineIter_equivalence k).refl a

/-- Every later round still separates `0` from `1`. -/
example (i : ℕ) (hi : 3 ≤ i) : ¬ loopLTS.refineIter i 0 1 := fun h =>
  not_homBisimilarity_zero_one
    ((loopLTS.refineIter_iff_homBisimilarity_of_card_le (by simpa using hi) 0 1).mp h)

/-- Bisimilar states stay related in every round. -/
example (k : ℕ) : loopLTS.refineIter k 1 2 :=
  loopLTS.refineIter_of_homBisimilarity k homBisimilarity_one_two

end Cslib.LTS.PartitionRefinementTests
