/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact actual seventh octad coordinate values in the first-line word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadCoefficientData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem octad_fourier_integer (v : Fin 64 → ℤ) (e : Fin 64) :
    trialityOctadAction (fun r => (1 / 64 : ℝ) * (v r : ℝ)) e =
      (1 / 512 : ℝ) *
        (((if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℤ) else -1) *
          ∑ r : Fin 64, trialityHadamard e r * v r : ℤ) : ℝ) := by
  change (if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    (trialityNormalizedHadamard *ᵥ (fun r => (1 / 64 : ℝ) * (v r : ℝ))) e = _
  simp only [Matrix.mulVec, dotProduct, trialityNormalizedHadamard, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum, Int.cast_ite,
    Int.cast_one, Int.cast_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hc : (Int.castRingHom ℝ) (trialityHadamard e r) =
      (trialityHadamard e r : ℝ) := rfl
  rw [hc]
  ring

/-- Every actual seventh octad coordinate equals its kernel-checked Fourier numerator over 512. -/
theorem monsterNortonLine01OctadSeventh_coordinates (j : Fin 16) (e : Fin 64) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1
      (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) =
        (1 / 512 : ℝ) * (monsterNortonLine01OctadSeventhCoefficientLookup j e : ℝ) := by
  rw [monsterNortonLine01ShortSeventh_octad_coordinates]
  change trialityOctadAction (fun r =>
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
      (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, r)))) e = _
  simp_rw [monsterNortonLine01OctadSixth_coordinates,
    monsterNortonLine01OctadSixthCoefficientLookup_actual]
  rw [octad_fourier_integer]
  change (1 / 512 : ℝ) * (monsterNortonLine01OctadSeventhNumerator j e : ℝ) = _
  rw [monsterNortonLine01OctadSeventhCoefficientLookup_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
