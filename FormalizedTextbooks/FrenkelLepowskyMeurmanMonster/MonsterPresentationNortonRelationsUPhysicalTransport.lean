/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Generic exact physical transport under the actual source Norton U numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every actual U vector coordinate is its genuine finite source numerator divided by four. -/
theorem monsterNortonUPhysical_vector (x : Fin 24 → ℝ) (i : Fin 24) :
    monsterNortonUFiber.val.2.val x i =
      ∑ j : Fin 24, ((monsterNortonUNumerator1 i j : ℝ) / 4) * x j := by
  rw [← leechIsomMatrix_mulVec monsterNortonUFiber.val.2]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, monsterNortonUPhysicalMatrix_basis]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual shortest-vector normalization leaves an exact integer numerator
over four sqrt eight. -/
theorem monsterNortonUPhysical_short (r : GriessShortIndex) (i : Fin 24) :
    monsterNortonUFiber.val.2.val (griessShortVector r) i =
      (((monsterNortonUNumerator1 *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (4 * Real.sqrt 8) := by
  rw [monsterNortonUPhysical_vector]
  simp only [griessShortVector, div_mul_div_comm]
  rw [← Finset.sum_div]
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

/-- A true integer coordinate certificate determines the entire actual real U image. -/
theorem monsterNortonUPhysical_of_certificate (r s : GriessShortIndex) (c : ℤ)
    (h : ∀ i : Fin 24, (monsterNortonUNumerator1 *ᵥ griessShortIntegral r) i =
      4 * c * griessShortIntegral s i) :
    monsterNortonUFiber.val.2.val (griessShortVector r) = (c : ℝ) • griessShortVector s := by
  funext i
  rw [monsterNortonUPhysical_short, h]
  simp only [Int.cast_mul, Int.cast_ofNat, griessShortVector, Pi.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (8 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
