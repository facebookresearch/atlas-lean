/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialMatrix

/-! Direct rational entries of the complete original spatial normalization stages. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Multiplying the source signs and permutation retains its exact inverse-coordinate convention. -/
theorem generatedAxisGlobalSpatialSignPermutation_entry (d : golayCode)
    (p : Equiv.Perm (Fin 24)) (i j : Fin 24) :
    (generatedAxisGlobalSpatialSignMatrix d * generatedAxisGlobalSpatialPermutationMatrix p) i j =
      if p.symm i = j then (if d.val i = 0 then 1 else -1) else 0 := by
  rw [generatedAxisGlobalSpatialSignMatrix, Matrix.diagonal_mul]
  simp [generatedAxisGlobalSpatialPermutationMatrix, mul_ite]

/-- Each original rational stage entry needs just one source Xi entry and one actual code sign. -/
theorem generatedAxisGlobalFifthSpatialStageMatrix_entry (k : Fin 14) (h : Fin 7)
    (i j : Fin 24) :
    generatedAxisGlobalFifthSpatialStageMatrix k h i j =
      (if generatedAxisGlobalFifthShortNormalizationXi k h then
        co1XiMatrixQ i ((generatedAxisGlobalFifthShortNormalizationPermutation k h).val j)
      else if i = (generatedAxisGlobalFifthShortNormalizationPermutation k h).val j then
        1 else 0) *
      (if (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns k h)).val
        ((generatedAxisGlobalFifthShortNormalizationPermutation k h).val j) = 0 then
          1 else -1) := by
  rw [generatedAxisGlobalFifthSpatialStageMatrix, Matrix.mul_apply]
  simp_rw [generatedAxisGlobalSpatialSignPermutation_entry, Equiv.symm_apply_eq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  cases generatedAxisGlobalFifthShortNormalizationXi k h <;> simp [Matrix.one_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
