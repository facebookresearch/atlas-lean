/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.TateCurve
import MathlibExt.NumberTheory.ModularForms.JCoefficientBound
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Simproc.Divisors

@[expose] public section

open TateCurve

/-- Consumer exercising the coefficient formulas with the original binders. -/
private theorem exactSource_coeff (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) ∧
      PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  ⟨coeff_tateA4 n, coeff_tateA6 n⟩

/-- The integral Tate model over `ℤ⟦q⟧` has the stated Weierstrass coefficients. -/
example : tatePowerSeries.a₁ = 1 ∧ tatePowerSeries.a₄ = tateA4 ∧
    tatePowerSeries.a₆ = tateA6 :=
  ⟨rfl, rfl, rfl⟩

/-- The integral model is not elliptic over `ℤ⟦q⟧`: the constant coefficient of its
discriminant is `0`, so the discriminant is not a unit. -/
example : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 ∧ ¬ tatePowerSeries.IsElliptic := by
  have h0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, constantCoeff_tateA4, constantCoeff_tateA6]
  refine ⟨h0, fun h => ?_⟩
  have hu := tatePowerSeries.isUnit_Δ.map PowerSeries.constantCoeff
  rw [h0] at hu
  exact not_isUnit_zero hu

/-- `laurentOfInt K` sends `q` to the Laurent variable `q`. -/
example (K : Type*) [CommRing K] :
    laurentOfInt K PowerSeries.X = HahnSeries.single 1 1 := by
  rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

/-- `laurentOfInt` is not an embedding in general: over `ZMod 5` the nonzero constant series `5`
maps to `0`. -/
example : PowerSeries.C (5 : ℤ) ≠ 0 ∧ laurentOfInt (ZMod 5) (PowerSeries.C (5 : ℤ)) = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' := congrArg PowerSeries.constantCoeff h
    rw [PowerSeries.constantCoeff_C, map_zero] at h'
    norm_num at h'
  · have h5 : Int.castRingHom (ZMod 5) 5 = 0 := by decide
    rw [laurentOfInt_apply, PowerSeries.map_C, h5, map_zero, map_zero]

/-- `laurentOfInt K` is injective exactly when `Int.castRingHom K` is. -/
private theorem laurentOfInt_injective_iff (K : Type*) [CommRing K] :
    Function.Injective (laurentOfInt K) ↔ Function.Injective (Int.castRingHom K) := by
  refine ⟨fun h a b hab => ?_, fun h f g hfg => ?_⟩
  · have hC : PowerSeries.C a = PowerSeries.C b := h (by
      rw [laurentOfInt_apply, laurentOfInt_apply, PowerSeries.map_C, PowerSeries.map_C, hab])
    have h' := congrArg PowerSeries.constantCoeff hC
    rwa [PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C] at h'
  · rw [laurentOfInt_apply, laurentOfInt_apply] at hfg
    exact PowerSeries.map_injective _ h (HahnSeries.ofPowerSeries_injective hfg)

/-- In characteristic zero `laurentOfInt K` is injective. -/
example (K : Type*) [CommRing K] [CharZero K] : Function.Injective (laurentOfInt K) :=
  (laurentOfInt_injective_iff K).mpr Int.cast_injective

/-- The Tate curve over `K((q))` is elliptic for every commutative ring `K`. -/
example (K : Type*) [CommRing K] : (tateLaurent K).IsElliptic :=
  inferInstance

/-- Boundary coefficients of the origin coordinate series. -/
example (K : Type*) [CommRing K] :
    (tateOriginX K).coeff (-2) = 1 ∧ (tateOriginY K).coeff (-3) = -1 :=
  ⟨coeff_tateOriginX_neg_two K, coeff_tateOriginY_neg_three K⟩

example : PowerSeries.coeff 1 tateA4 = -5 ∧ PowerSeries.coeff 1 tateA6 = -1 :=
  ⟨coeff_one_tateA4, coeff_one_tateA6⟩

/-- `a₄ = -5q - 45q² - 140q³ - 365q⁴ - ⋯` and `a₆ = -q - 23q² - 154q³ - 647q⁴ - ⋯`. -/
example : PowerSeries.coeff 2 tateA4 = -45 ∧ PowerSeries.coeff 3 tateA4 = -140 ∧
    PowerSeries.coeff 4 tateA4 = -365 ∧ PowerSeries.coeff 2 tateA6 = -23 ∧
    PowerSeries.coeff 3 tateA6 = -154 ∧ PowerSeries.coeff 4 tateA6 = -647 := by
  simp [coeff_tateA4, coeff_tateA6, tateB, Nat.divisors_ofNat]

/-- `E₆ = 1 - 504q - 16632q² - 122976q³ - ⋯`. -/
example : PowerSeries.coeff 1 eisenstein6 = -504 ∧ PowerSeries.coeff 2 eisenstein6 = -16632 ∧
    PowerSeries.coeff 3 eisenstein6 = -122976 := by
  simp [eisenstein6, Nat.divisors_ofNat]

/-- The invariant `c₄ = 1 - 48a₄` of the integral Tate model is the Eisenstein series
`E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
example : tatePowerSeries.c₄ = ModularCurve.eisenstein4 := by
  ext n
  have h : tatePowerSeries.c₄ = 1 - PowerSeries.C 48 * tateA4 := by
    rw [show (PowerSeries.C (48 : ℤ)) = (48 : PowerSeries ℤ) from map_ofNat _ 48]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄]
    ring
  rw [h, map_sub, PowerSeries.coeff_C_mul, coeff_tateA4, ModularCurve.eisenstein4,
    PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [hn, ite_false, zero_sub, mul_neg, neg_neg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

/-- The invariant `c₆ = -1 + 72a₄ - 864a₆` of the integral Tate model is `-E₆`. -/
example : tatePowerSeries.c₆ = -eisenstein6 := by
  ext n
  have h : tatePowerSeries.c₆ =
      -1 + PowerSeries.C 72 * tateA4 - PowerSeries.C 864 * tateA6 := by
    rw [show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72,
      show (PowerSeries.C (864 : ℤ)) = (864 : PowerSeries ℤ) from map_ofNat _ 864]
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  rw [h, map_sub, map_add, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_tateA4, coeff_tateA6, eisenstein6, map_neg, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [hn, ite_false, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_zero,
      zero_add, sub_neg_eq_add, neg_mul, neg_neg]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by linear_combination 72 * twelve_mul_tateB d

/-- The principal parts are `T⁻² + T⁻¹` for `X` and `-T⁻³ - 2T⁻² - T⁻¹` for `Y`. -/
example (K : Type*) [CommRing K] :
    (tateOriginX K).coeff (-1) = 1 ∧ (tateOriginY K).coeff (-2) = -2 ∧
      (tateOriginY K).coeff (-1) = -1 := by
  simp [tateOriginX, tateOriginY, PowerSeries.coeff_coe]

/-- `X` has a pole of exact order two at the origin. -/
example (K : Type*) [CommRing K] [Nontrivial K] : (tateOriginX K).order = -2 := by
  have hne : (tateOriginX K).coeff (-2) ≠ 0 := by
    rw [coeff_tateOriginX_neg_two]
    exact one_ne_zero
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne) (not_lt.mp fun hlt => ?_)
  exact HahnSeries.ne_zero_of_coeff_ne_zero hne
    (HahnSeries.coeff_order_eq_zero.mp (coeff_tateOriginX_of_lt K hlt))

/-- `Y` has a pole of exact order three at the origin. -/
example (K : Type*) [CommRing K] [Nontrivial K] : (tateOriginY K).order = -3 := by
  have hne : (tateOriginY K).coeff (-3) ≠ 0 := by
    rw [coeff_tateOriginY_neg_three]
    exact neg_ne_zero.mpr one_ne_zero
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne) (not_lt.mp fun hlt => ?_)
  exact HahnSeries.ne_zero_of_coeff_ne_zero hne
    (HahnSeries.coeff_order_eq_zero.mp (coeff_tateOriginY_of_lt K hlt))

/-- Regular coefficients of `X`, as `qᴹ`-coefficients of the `Tᵏ`-coefficient for
`k = 0, 1, 2, 3` and `M = 1, 2, 3`: the `T⁰` and `T¹` rows vanish, the `T²` row is `σ₃(M)`
and the `T³` row is `-σ₃(M)`. -/
example (K : Type*) [CommRing K] :
    PowerSeries.coeff 1 ((tateOriginX K).coeff 0) = 0 ∧
      PowerSeries.coeff 2 ((tateOriginX K).coeff 0) = 0 ∧
      PowerSeries.coeff 3 ((tateOriginX K).coeff 0) = 0 ∧
      PowerSeries.coeff 1 ((tateOriginX K).coeff 1) = 0 ∧
      PowerSeries.coeff 2 ((tateOriginX K).coeff 1) = 0 ∧
      PowerSeries.coeff 3 ((tateOriginX K).coeff 1) = 0 ∧
      PowerSeries.coeff 1 ((tateOriginX K).coeff 2) = 1 ∧
      PowerSeries.coeff 2 ((tateOriginX K).coeff 2) = 9 ∧
      PowerSeries.coeff 3 ((tateOriginX K).coeff 2) = 28 ∧
      PowerSeries.coeff 1 ((tateOriginX K).coeff 3) = -1 ∧
      PowerSeries.coeff 2 ((tateOriginX K).coeff 3) = -9 ∧
      PowerSeries.coeff 3 ((tateOriginX K).coeff 3) = -28 := by
  simp [tateOriginX, PowerSeries.coeff_coe, Nat.divisors_ofNat, Nat.choose]
  norm_num

/-- Regular coefficients of `Y`, as `qᴹ`-coefficients of the `Tᵏ`-coefficient for
`k = 0, 1, 2, 3` and `M = 1, 2, 3`: the `T⁰` row vanishes, the `T¹` row is `σ₃(M)` and the
`T²` row is `-σ₃(M)`. -/
example (K : Type*) [CommRing K] :
    PowerSeries.coeff 1 ((tateOriginY K).coeff 0) = 0 ∧
      PowerSeries.coeff 2 ((tateOriginY K).coeff 0) = 0 ∧
      PowerSeries.coeff 3 ((tateOriginY K).coeff 0) = 0 ∧
      PowerSeries.coeff 1 ((tateOriginY K).coeff 1) = 1 ∧
      PowerSeries.coeff 2 ((tateOriginY K).coeff 1) = 9 ∧
      PowerSeries.coeff 3 ((tateOriginY K).coeff 1) = 28 ∧
      PowerSeries.coeff 1 ((tateOriginY K).coeff 2) = -1 ∧
      PowerSeries.coeff 2 ((tateOriginY K).coeff 2) = -9 ∧
      PowerSeries.coeff 3 ((tateOriginY K).coeff 2) = -28 ∧
      PowerSeries.coeff 1 ((tateOriginY K).coeff 3) = 1 ∧
      PowerSeries.coeff 2 ((tateOriginY K).coeff 3) = 13 ∧
      PowerSeries.coeff 3 ((tateOriginY K).coeff 3) = 64 := by
  simp [tateOriginY, PowerSeries.coeff_coe, Nat.divisors_ofNat, Nat.choose]
  norm_num
