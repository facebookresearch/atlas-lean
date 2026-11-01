/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer pairing arithmetic for physical matrix, short, and spin-tensor packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortDiagonal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem scaled_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ) (a b : ℝ) :
    (∑ i, (a * f i) * (b * g i)) = a * b * ∑ i, f i * g i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem cast_pairing {ι : Type*} [Fintype ι] (f g : ι → ℤ) :
    (∑ i, (f i : ℝ) * (g i : ℝ)) = ((∑ i, f i * g i : ℤ) : ℝ) := by
  simp only [Int.cast_sum, Int.cast_mul]

/-- The true raw-coordinate pairing, including the full spin-tensor summand. -/
theorem monsterNortonForm_raw_coordinates (x y : GriessSpace) :
    griessForm x y =
      (∑ i, ∑ j, (griessConwayEncode x).1 i j * (griessConwayEncode y).1 i j) +
      (∑ r, (griessConwayEncode x).2.1 r * (griessConwayEncode y).2.1 r) +
      ∑ t, ∑ i, (griessConwayEncode x).2.2 t i * (griessConwayEncode y).2.2 t i := by
  rw [griessForm_eq_conwayRawForm]
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, conwayTensorForm,
    LinearMap.mk₂_apply]

/-- Integer spin-tensor coordinates carry the actual additional factor one over sqrt two. -/
theorem monsterNortonForm_integer_coordinates
    (x y : GriessSpace) (a b : ℝ)
    (M N : Matrix (Fin 24) (Fin 24) ℤ)
    (X Y : GriessShortIndex → ℤ) (F H : SpinIndex → Fin 24 → ℤ)
    (hxM : ∀ i j, (griessConwayEncode x).1 i j = a * (M i j : ℝ))
    (hyM : ∀ i j, (griessConwayEncode y).1 i j = b * (N i j : ℝ))
    (hxX : ∀ r, (griessConwayEncode x).2.1 r = a * (X r : ℝ))
    (hyX : ∀ r, (griessConwayEncode y).2.1 r = b * (Y r : ℝ))
    (hxF : ∀ t i, (griessConwayEncode x).2.2 t i = a / Real.sqrt 2 * (F t i : ℝ))
    (hyF : ∀ t i, (griessConwayEncode y).2.2 t i = b / Real.sqrt 2 * (H t i : ℝ)) :
    griessForm x y = a * b / 2 *
      ((2 * (∑ i, ∑ j, M i j * N i j) + 2 * (∑ r, X r * Y r) +
        (∑ t, ∑ i, F t i * H t i) : ℤ) : ℝ) := by
  rw [monsterNortonForm_raw_coordinates]
  simp only [hxM, hyM, hxX, hyX, hxF, hyF]
  simp_rw [scaled_sum, ← Finset.mul_sum]
  simp_rw [cast_pairing]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  simp only [Int.cast_sum]
  field_simp
  rw [hs2]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
