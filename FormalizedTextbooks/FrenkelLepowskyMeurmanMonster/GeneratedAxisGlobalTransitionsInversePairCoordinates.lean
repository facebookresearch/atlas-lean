/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Direct original matrix and pair-short coordinates of actual inverse triality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual inverse triality keeps the matrix diagonal and uses the original pair difference. -/
theorem generatedAxisGlobal_inverse_matrix_coordinate (x : GriessSpace) (i j : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).1 i j =
      if h : i = j then (griessConwayEncode x).1 i i else
        ((griessConwayEncode x).2.1 (Sum.inl (0, griessPairIndex i j h)) -
          (griessConwayEncode x).2.1 (Sum.inl (1, griessPairIndex i j h))) / 2 := by
  rw [generatedAxisGlobalRawInverseFormula_actual]
  by_cases h : i = j
  · subst j
    simp only [generatedAxisGlobalRawInverseFormula, generatedAxisGlobalRawTrialityFormula,
      generatedAxisGlobalRawTrialityMatrix, dite_true]
  · simp only [generatedAxisGlobalRawInverseFormula, generatedAxisGlobalRawTrialityFormula,
      generatedAxisGlobalRawTrialityMatrix, h, dite_false,
      generatedAxisGlobalRawTrialityShort, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    ring

/-- The first preferred inverse pair row uses the original matrix and the pair sum. -/
theorem generatedAxisGlobal_inverse_pair_zero_coordinate (x : GriessSpace) (p : Fin 276) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inl (0, p)) =
      (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
        ((griessConwayEncode x).2.1 (Sum.inl (0, p)) +
          (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 := by
  rw [generatedAxisGlobalRawInverseFormula_actual]
  simp only [generatedAxisGlobalRawInverseFormula, generatedAxisGlobalRawTrialityFormula,
    generatedAxisGlobalRawTrialityShort, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    generatedAxisGlobalRawTrialityMatrix, griessCoordinatePair_ne, dite_false,
    griessPairIndex_pair]
  ring

/-- The second preferred inverse pair row uses the original matrix minus the pair sum. -/
theorem generatedAxisGlobal_inverse_pair_one_coordinate (x : GriessSpace) (p : Fin 276) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inl (1, p)) =
      (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 -
        ((griessConwayEncode x).2.1 (Sum.inl (0, p)) +
          (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 := by
  rw [generatedAxisGlobalRawInverseFormula_actual]
  simp only [generatedAxisGlobalRawInverseFormula, generatedAxisGlobalRawTrialityFormula,
    generatedAxisGlobalRawTrialityShort, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    generatedAxisGlobalRawTrialityMatrix, griessCoordinatePair_ne, dite_false,
    griessPairIndex_pair]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
