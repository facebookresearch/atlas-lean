/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPreferredQ

/-! Integer physical certificates determine genuine normalized Xi short-vector transport. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual Xi image of a normalized short vector is its exact integer numerator. -/
theorem generatedFifthXiShort_physical_vector (r : GriessShortIndex) (i : Fin 24) :
    xiSpinLocalFiber.val.2.val (griessShortVector r) i =
      (((co1XiNumerator *ᵥ griessShortIntegral r) i : ℤ) : ℝ) / (2 * Real.sqrt 8) := by
  rw [← leechIsomMatrix_mulVec xiSpinLocalFiber.val.2]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, generatedFifth_xi_spatial_unit,
    griessShortVector, div_mul_div_comm]
  rw [← Finset.sum_div]
  simp only [Int.cast_sum, Int.cast_mul]

/-- A genuine integer certificate gives the full normalized Xi transport, including sign. -/
theorem generatedFifthXiShort_physical_of_certificate (r s : GriessShortIndex) (c : ℤ)
    (h : ∀ i : Fin 24, (co1XiNumerator *ᵥ griessShortIntegral r) i =
      2 * c * griessShortIntegral s i) :
    xiSpinLocalFiber.val.2.val (griessShortVector r) = (c : ℝ) • griessShortVector s := by
  funext i
  rw [generatedFifthXiShort_physical_vector, h]
  simp only [Int.cast_mul, Int.cast_ofNat, griessShortVector, Pi.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (8 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
