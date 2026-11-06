/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthShortPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialActions

/-! Integer physical certificates determine the genuine Xi and C preferred-short labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Clearing the genuine physical denominator determines a preferred short-line image. -/
theorem generatedSixth_short_permutation_of_integer_matrix (g : leechIsomSubgroup)
    (M : Matrix (Fin 24) (Fin 24) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hM : leechIsomMatrix g = (1 / (d : ℝ)) • M.map (Int.castRingHom ℝ))
    (r s : GriessShortIndex) (p : ZMod 2)
    (h : M *ᵥ griessShortIntegral r =
      fun i => d * nortonUIntegerSign p * griessShortIntegral s i) :
    griessShortPermutation g r = s := by
  apply generatedSixth_short_permutation_of_vector
  have hv : g.val (griessShortVector r) =
      qSign p • griessShortVector s := by
    funext i
    rw [← leechIsomMatrix_mulVec, hM]
    have hi := congrArg (fun z : ℤ => (z : ℝ)) (congrFun h i)
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
      nortonUIntegerSign_real] at hi
    change (∑ j : Fin 24, (1 / (d : ℝ) * (M i j : ℝ)) *
        ((griessShortIntegral r j : ℝ) / Real.sqrt 8)) =
      qSign p * ((griessShortIntegral s i : ℝ) / Real.sqrt 8)
    calc
      _ = (1 / (d : ℝ)) *
          (∑ j : Fin 24, (M i j : ℝ) * (griessShortIntegral r j : ℝ)) /
            Real.sqrt 8 := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [hi]
        have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast hd
        field_simp [hdn]
  by_cases hp : p = 0
  · left
    simpa [hp] using hv
  · right
    simpa [qSign, hp] using hv

/-- Every complete cleared Xi physical row gives the actual preferred-short permutation. -/
theorem generatedSixth_xi_short_permutation_of_integer (r s : GriessShortIndex)
    (p : ZMod 2)
    (h : sixthFrameOrbitSpatialNumerator 14 *ᵥ griessShortIntegral r =
      fun i => 2 * nortonUIntegerSign p * griessShortIntegral s i) :
    griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s := by
  apply generatedSixth_short_permutation_of_integer_matrix _ _ 2 (by norm_num) _ r s p h
  exact sixthFrameOrbit_original_physical_matrix 14

/-- The original C coordinate pullback gives its actual preferred-short permutation. -/
theorem generatedSixth_C_short_permutation_of_integer (r a : GriessShortIndex)
    (p : ZMod 2)
    (h : ∀ i : Fin 24,
      griessShortIntegral r (sixthFrameOrbitCInverse i) =
        nortonUIntegerSign p * griessShortIntegral a i) :
    griessShortPermutation leechRootedA2SixthXiTransportFiber.val.2 r = a := by
  apply generatedSixth_short_permutation_of_vector
  have hv : leechRootedA2SixthXiTransportFiber.val.2.val (griessShortVector r) =
      qSign p • griessShortVector a := by
    funext i
    have he := sixthFrameOrbit_permutation_apply 4 (griessShortVector r) i
    change leechRootedA2SixthXiTransportFiber.val.2.val (griessShortVector r) i =
      griessShortVector r (sixthFrameOrbitCInverse i) at he
    rw [he]
    simp only [griessShortVector, h i, Int.cast_mul, nortonUIntegerSign_real,
      Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  by_cases hp : p = 0
  · left
    simpa [hp] using hv
  · right
    simpa [qSign, hp] using hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
