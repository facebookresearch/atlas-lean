/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! The actual positive triality transforms every original octad block by its signed
integer Fourier matrix. No coefficient catalogue or orbit count enters these formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every actual final octad row is the signed Fourier sum of the original octad rows. -/
theorem generatedNinth_final_triality_octad_coordinate
    (x : GriessSpace) (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, ((trialityIntegerMatrix e f : ℝ) / 8) *
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f))) := by
  change (trialityBlocksEquiv (sExtra x)).2.2.1 o e = _
  have h : (trialityBlocksEquiv (sExtra x)).2.2.1 o =
      trialityOctadAction ((trialityBlocksEquiv x).2.2.1 o) := by
    simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [h, trialityOctadAction_matrix]
  simp only [trialityRealMatrix, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro f _
  change (1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ) *
      (trialityBlocksEquiv x).2.2.1 o f =
    (trialityIntegerMatrix e f : ℝ) / 8 * (trialityBlocksEquiv x).2.2.1 o f
  ring

/-- Exact integer middle octad numerators give the actual final numerator over128. -/
theorem generatedNinth_final_triality_octad_integer
    (x : GriessSpace) (o : Fin 759) (n : Fin 64 → ℤ)
    (h : ∀ f : Fin 64,
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f))) = (n f : ℝ) / 16)
    (e : Fin 64) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      ((∑ f : Fin 64, trialityIntegerMatrix e f * n f : ℤ) : ℝ) / 128 := by
  rw [generatedNinth_final_triality_octad_coordinate]
  simp_rw [h]
  simp only [Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
