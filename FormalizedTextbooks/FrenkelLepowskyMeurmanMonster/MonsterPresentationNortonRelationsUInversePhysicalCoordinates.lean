/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual inverse Norton Leech transport in physical short-vector coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUTensorData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual inverse-U physical columns are the transpose of the certified source numerator. -/
theorem monsterNortonUInversePhysical_basis (j i : Fin 24) :
    (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1) i =
      (monsterNortonUNumerator1 j i : ℝ) / 4 := by
  change monsterNortonUFiber.val.2.val.symm (Pi.single j 1) i = _
  rw [leechIsom_inverse_coordinate]
  change monsterNortonUFiber.val.2.val (Pi.single i 1) j = _
  rw [monsterNortonUPhysicalMatrix_basis]
  ring

/-- Every actual inverse-U physical vector coordinate is the exact finite transpose action. -/
theorem monsterNortonUInversePhysical_vector (x : Fin 24 → ℝ) (i : Fin 24) :
    (monsterNortonUFiber.val.2⁻¹).val x i =
      ∑ j : Fin 24, ((monsterNortonUNumerator1 j i : ℝ) / 4) * x j := by
  rw [← leechIsomMatrix_mulVec (monsterNortonUFiber.val.2⁻¹)]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, monsterNortonUInversePhysical_basis]

/-- The shortest-vector normalization converts the actual inverse action to an integer numerator. -/
theorem monsterNortonUInversePhysical_short (r : GriessShortIndex) (i : Fin 24) :
    (monsterNortonUFiber.val.2⁻¹).val (griessShortVector r) i =
      (((monsterNortonUNumerator1.transpose *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (4 * Real.sqrt 8) := by
  rw [monsterNortonUInversePhysical_vector]
  simp only [griessShortVector, div_mul_div_comm]
  rw [← Finset.sum_div]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Int.cast_sum, Int.cast_mul]

/-- An exact integer physical-vector certificate identifies the complete actual inverse image. -/
theorem monsterNortonUInversePhysical_of_certificate (r s : GriessShortIndex) (c : ℤ)
    (h : ∀ i : Fin 24, (monsterNortonUNumerator1.transpose *ᵥ griessShortIntegral r) i =
      4 * c * griessShortIntegral s i) :
    (monsterNortonUFiber.val.2⁻¹).val (griessShortVector r) = (c : ℝ) • griessShortVector s := by
  funext i
  rw [monsterNortonUInversePhysical_short, h]
  simp only [Int.cast_mul, Int.cast_ofNat, griessShortVector, Pi.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (8 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
