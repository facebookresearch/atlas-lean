/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.CrossingQuotient

@[expose] public section

noncomputable section

namespace MvPolynomial.CrossingQuotient

/-- Consumer using the original binders of the crossing quotient carrier. -/
example {W : Type*} [CommRing W] (t : W) : Type _ := CrossingQuotient W t

example {W : Type*} [CommRing W] (t : W) : CrossingQuotient W t := U t * V t

theorem exactSource {W : Type*} [CommRing W] (t : W) :
    U t * V t = algebraMap W (CrossingQuotient W t) t := U_mul_V t

/-! The examples below evaluate the maps on concrete elements. Swapping the coordinates or
changing an exponent of a map changes the values they check. -/

/-! ### Monomials over `ℤ` with `t = 6` -/

/-- A positive exponent gives a power of `U`. -/
example : monomial (6 : ℤ) 3 = U 6 ^ 3 := by
  rw [monomial_of_nonneg _ (by norm_num)]
  rfl

/-- A negative exponent gives a power of `V`. -/
example : monomial (6 : ℤ) (-2) = V 6 ^ 2 := by
  rw [monomial_of_neg _ (by norm_num)]
  rfl

/-- The zero exponent gives `1`. -/
example : monomial (6 : ℤ) 0 = 1 := by simp

/-- Opposite exponents multiply to a power of `t`, through the relation `U * V = t`. -/
example (n : ℕ) : monomial (6 : ℤ) n * monomial 6 (-n) = 6 ^ n := by
  simp only [monomial_natCast, monomial_neg_natCast]
  rw [← mul_pow, mk_X_mul_mk_X]
  simp

/-- Monomials of each sign at `(U, V) = (2, 3)`: `2 ^ 3 + 3 ^ 2 + 1`. -/
example :
    lift (6 : ℤ) (2 : ℤ) 3 (by norm_num) (monomial 6 3 + monomial 6 (-2) + monomial 6 0) = 18 := by
  rw [monomial_of_nonneg _ (by norm_num), monomial_of_neg _ (by norm_num), monomial_zero,
    map_add, map_add, map_pow, map_pow, map_one, lift_U, lift_V]
  norm_num

/-! ### The universal map and the power maps -/

/-- `lift` sends `U` to `2` and `V` to `3`. -/
example : lift (6 : ℤ) (2 : ℤ) 3 (by norm_num) (U 6 ^ 2 - V 6) = 1 := by
  simp

/-- `powMap 6 2` on each coordinate. -/
example : powMap (6 : ℤ) 2 (U ((6 : ℤ) ^ 2)) = U 6 ^ 2 := by
  rw [powMap_mk_X]

example : powMap (6 : ℤ) 2 (V ((6 : ℤ) ^ 2)) = V 6 ^ 2 := by
  rw [powMap_mk_X]

/-- `powMap 6 2`, then the value at `(U, V) = (2, 3)`: `U ↦ 2 ^ 2` and `V ↦ 3 ^ 2`. -/
example :
    lift (6 : ℤ) (2 : ℤ) 3 (by norm_num) (powMap 6 2 (U ((6 : ℤ) ^ 2) - V ((6 : ℤ) ^ 2))) = -5 := by
  rw [map_sub, powMap_mk_X, powMap_mk_X, map_sub, map_pow, map_pow, lift_U, lift_V]
  norm_num

/-! ### Resolution charts -/

/-- The boundary chart `e = 1, i = 0` fixes both coordinates. -/
example : resolutionChart (6 : ℤ) 1 0 (U ((6 : ℤ) ^ 1)) = U 6 := by
  rw [resolutionChart_U]
  simp

example : resolutionChart (6 : ℤ) 1 0 (V ((6 : ℤ) ^ 1)) = V 6 := by
  rw [resolutionChart_V]
  simp

/-- The chart `e = 4, i = 1` over `t = 2`, then the value at `(U, V) = (1, 2)`:
`U ↦ 2 * 1` and `V ↦ 2 ^ 2 * 2`. -/
example :
    lift (2 : ℤ) (1 : ℤ) 2 (by norm_num)
      (resolutionChart 2 4 1 (U ((2 : ℤ) ^ 4) - V ((2 : ℤ) ^ 4))) = -6 := by
  rw [map_sub, resolutionChart_U, resolutionChart_V, map_sub, map_mul, map_mul, AlgHom.commutes,
    AlgHom.commutes, lift_U, lift_V]
  norm_num

/-! ### Transition maps -/

/-- `transitionUp` sends `U` to the inverse of `V`. -/
example :
    algebraMap (CrossingQuotient ℤ 6) (Localization.Away (V (6 : ℤ))) (V 6) *
      transitionUp 6 (U 6) = 1 := by
  rw [transitionUp_U]
  exact IsLocalization.Away.mul_invSelf _

/-- `transitionDown` sends `V` to the inverse of `U`. -/
example :
    algebraMap (CrossingQuotient ℤ 6) (Localization.Away (U (6 : ℤ))) (U 6) *
      transitionDown 6 (V 6) = 1 := by
  rw [transitionDown_V]
  exact IsLocalization.Away.mul_invSelf _

/-- Evaluating `invSelf x` through `Localization.awayLift g x _` gives `(g x)⁻¹`. -/
private theorem awayLift_invSelf {R K : Type*} [CommRing R] [Field K] (g : R →+* K) (x : R)
    (hx : IsUnit (g x)) :
    Localization.awayLift g x hx (IsLocalization.Away.invSelf x) = (g x)⁻¹ := by
  have h := congrArg (Localization.awayLift g x hx)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, map_one, IsLocalization.Away.lift_eq] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `transitionUp`, then the value at `(U, V) = (2, 3)` over `t = 6`: `V ↦ 6 * 3`. -/
example :
    Localization.awayLift (lift (6 : ℚ) (2 : ℚ) 3 (by norm_num)).toRingHom (V 6) (by simp)
      (transitionUp 6 (V 6)) = 18 := by
  rw [transitionUp_V,
    IsScalarTower.algebraMap_apply ℚ (CrossingQuotient ℚ 6) (Localization.Away (V (6 : ℚ)))]
  simp
  norm_num

/-- `transitionUp`, then the value at `(U, V) = (2, 3)` over `t = 6`: `U ↦ 3⁻¹`. -/
example :
    Localization.awayLift (lift (6 : ℚ) (2 : ℚ) 3 (by norm_num)).toRingHom (V 6) (by simp)
      (transitionUp 6 (U 6)) = 3⁻¹ := by
  rw [transitionUp_U, awayLift_invSelf]
  simp

/-- `transitionDown`, then the value at `(U, V) = (2, 3)` over `t = 6`: `U ↦ 6 * 2`. -/
example :
    Localization.awayLift (lift (6 : ℚ) (2 : ℚ) 3 (by norm_num)).toRingHom (U 6) (by simp)
      (transitionDown 6 (U 6)) = 12 := by
  rw [transitionDown_U,
    IsScalarTower.algebraMap_apply ℚ (CrossingQuotient ℚ 6) (Localization.Away (U (6 : ℚ)))]
  simp
  norm_num

/-- `transitionDown`, then the value at `(U, V) = (2, 3)` over `t = 6`: `V ↦ 2⁻¹`. -/
example :
    Localization.awayLift (lift (6 : ℚ) (2 : ℚ) 3 (by norm_num)).toRingHom (U 6) (by simp)
      (transitionDown 6 (V 6)) = 2⁻¹ := by
  rw [transitionDown_V, awayLift_invSelf]
  simp

end MvPolynomial.CrossingQuotient
