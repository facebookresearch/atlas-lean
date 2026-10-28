/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual physical U action on all short units of the sparse second-input half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUPhysicalCertificate

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem forward_vector (x : Fin 24 → ℝ) (i : Fin 24) :
    monsterNortonUFiber.val.2.val x i =
      ∑ j : Fin 24, ((monsterNortonUNumerator1 i j : ℝ) / 4) * x j := by
  rw [← leechIsomMatrix_mulVec monsterNortonUFiber.val.2]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, monsterNortonUPhysicalMatrix_basis]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem forward_short (r : GriessShortIndex) (i : Fin 24) :
    monsterNortonUFiber.val.2.val (griessShortVector r) i =
      (((monsterNortonUNumerator1 *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (4 * Real.sqrt 8) := by
  rw [forward_vector]
  simp only [griessShortVector, div_mul_div_comm]
  rw [← Finset.sum_div]
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

/-- The finite physical certificates are the complete actual real Leech-vector images. -/
theorem monsterNortonSecondHalfUPhysical_actual (i : NortonSecondHalfShortIndex) :
    monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonSecondHalfShortInput i)) =
      (monsterNortonSecondHalfUPhysicalSign (monsterNortonSecondHalfShortStorage i) : ℝ) •
        griessShortVector (monsterNortonSecondHalfShortUOutput i) := by
  funext j
  rw [forward_short, monsterNortonSecondHalfInputIntegral_actual,
    monsterNortonSecondHalfUPhysical_certificate]
  simp only [Int.cast_mul, Int.cast_ofNat, griessShortVector, Pi.smul_apply, smul_eq_mul]
  rw [monsterNortonSecondHalfOutputIntegral_actual]
  have hs : Real.sqrt (8 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]

/-- Every displayed physical representative sign is exactly plus or minus one. -/
theorem monsterNortonSecondHalfUPhysicalSign_unit (i : NortonSecondHalfShortIndex) :
    monsterNortonSecondHalfUPhysicalSign (monsterNortonSecondHalfShortStorage i) = 1 ∨
      monsterNortonSecondHalfUPhysicalSign (monsterNortonSecondHalfShortStorage i) = -1 := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
