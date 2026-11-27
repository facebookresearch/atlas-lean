/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities
import Mathlib.RingTheory.PowerSeries.Expand

/-! # Tests for `MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities`

An inhabited instance over `𝔽₂`: the root `α = x⁻¹ + x⁻² + x⁻⁴ + x⁻⁸ + ⋯` of `α² + α = x⁻¹`,
which has order `1` and satisfies `α = x α² / (x α² + 1)`, that is `A = C = x`, `B = 0`, `D = 1`.
At the convergent `P/Q = 0/1` (`n = 0`) both closeness conditions hold, and each identity gives
`v(b₁) = -1`.
-/

namespace MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities

open MetaMathlibExt Polynomial

/-- A nonzero polynomial has a nonzero image in `K((x⁻¹))`. -/
theorem polyToLaurentInv_eq_zero {K : Type*} [Field K] (p : K[X]) (h : polyToLaurentInv p = 0) :
    p = 0 := by
  by_contra hp
  have hcoeff : (polyToLaurentInv p).coeff (-(p.natDegree : ℤ)) = p.leadingCoeff := by
    rw [polyToLaurentInv, aeval_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single p.natDegree]
    · simp [laurentInvVar, HahnSeries.single_pow, Algebra.smul_def, LaurentSeries.algebraMap_apply,
        HahnSeries.C_apply, HahnSeries.single_mul_single]
    · intro i _ hi
      simp [laurentInvVar, HahnSeries.single_pow, Algebra.smul_def, LaurentSeries.algebraMap_apply,
        HahnSeries.C_apply, HahnSeries.single_mul_single, Ne.symm hi]
    · simp
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact leadingCoeff_ne_zero.mpr hp hcoeff.symm

open Classical in
/-- The power series `T + T² + T⁴ + T⁸ + ⋯` over `𝔽₂`. -/
noncomputable def twoPowSeries : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ k : ℕ, n = 2 ^ k then 1 else 0

open Classical in
theorem coeff_twoPowSeries (n : ℕ) :
    PowerSeries.coeff n twoPowSeries = if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
  simp [twoPowSeries, PowerSeries.coeff_mk]

theorem exists_double_eq_two_pow_iff {m : ℕ} :
    (∃ k : ℕ, m + m = 2 ^ k) ↔ (m ≠ 0 ∧ ∃ k : ℕ, m = 2 ^ k) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk; omega
    | succ j =>
      rw [pow_succ] at hk
      exact ⟨by have := Nat.two_pow_pos j; omega, j, by omega⟩
  · rintro ⟨-, k, hk⟩
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

theorem exists_odd_eq_two_pow_iff {m : ℕ} : (∃ k : ℕ, 2 * m + 1 = 2 ^ k) ↔ m = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk; omega
    | succ j => rw [pow_succ] at hk; omega
  · rintro rfl
    exact ⟨0, rfl⟩

/-- Over `𝔽₂`, `f = T + T² + T⁴ + ⋯` satisfies `f² + T = f`. -/
theorem twoPowSeries_sq_add_X : twoPowSeries ^ 2 + PowerSeries.X = twoPowSeries := by
  have key : ∀ (p : ℕ) (hp : p ≠ 0), p = 2 → twoPowSeries.expand p hp = twoPowSeries ^ p →
      twoPowSeries ^ 2 = twoPowSeries.expand 2 two_ne_zero := by
    rintro p hp rfl h
    exact h.symm
  rw [key _ _ (ZMod.card 2) (FiniteField.PowerSeries.expand_card twoPowSeries)]
  ext n
  rw [map_add, PowerSeries.coeff_expand, PowerSeries.coeff_X]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h2 : (2 * m) / 2 = m := by omega
    have hne : 2 * m ≠ 1 := by omega
    simp only [dvd_mul_right, h2, hne, ↓reduceIte, add_zero, coeff_twoPowSeries]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · have hiff : (∃ k : ℕ, 2 * m = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
        rw [two_mul, exists_double_eq_two_pow_iff]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      by_cases hp : ∃ k : ℕ, m = 2 ^ k
      · simp [hp, hiff.mpr hp]
      · simp [hp, mt hiff.mp hp]
  · have hnd : ¬ 2 ∣ 2 * m + 1 := by omega
    simp only [hnd, ↓reduceIte, zero_add, coeff_twoPowSeries, exists_odd_eq_two_pow_iff]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [show m ≠ 0 by omega]

/-- The fixed point `α = x⁻¹ + x⁻² + x⁻⁴ + ⋯ ∈ 𝔽₂((x⁻¹))`. -/
noncomputable def alpha : LaurentSeries (ZMod 2) :=
  HahnSeries.ofPowerSeries ℤ (ZMod 2) twoPowSeries

theorem alpha_sq : alpha ^ 2 = alpha - HahnSeries.single (1 : ℤ) (1 : ZMod 2) := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ (ZMod 2)) twoPowSeries_sq_add_X
  rw [map_add, map_pow, HahnSeries.ofPowerSeries_X] at h
  exact eq_sub_of_add_eq h

theorem alpha_coeff_of_nonpos (i : ℤ) (hi : i ≤ 0) : alpha.coeff i = 0 := by
  rw [alpha, PowerSeries.coeff_coe]
  split_ifs with h
  · rfl
  · have hi0 : i.natAbs = 0 := by omega
    have hnot : ¬ ∃ k : ℕ, (0 : ℕ) = 2 ^ k := fun ⟨k, hk⟩ => by
      have := Nat.two_pow_pos k
      omega
    simp [hi0, coeff_twoPowSeries, hnot]

theorem alpha_coeff_one : alpha.coeff 1 = 1 := by
  have h : ∃ k : ℕ, (1 : ℕ) = 2 ^ k := ⟨0, rfl⟩
  rw [alpha, PowerSeries.coeff_coe]
  simp [coeff_twoPowSeries, h]

theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  have h1 := alpha_coeff_one
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

/-- `α` has order `1`. -/
theorem alpha_order : alpha.order = 1 := by
  have h1 : alpha.coeff 1 ≠ 0 := by
    rw [alpha_coeff_one]
    exact one_ne_zero
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1)
  by_contra! hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr alpha_ne_zero
    (alpha_coeff_of_nonpos _ (by omega))

/-- `α - 1` has order `0`. -/
theorem alpha_sub_one_order : (alpha - 1).order = 0 := by
  have h0 : (alpha - 1).coeff 0 ≠ 0 := by
    simp [HahnSeries.coeff_sub, alpha_coeff_of_nonpos 0 le_rfl, HahnSeries.coeff_one]
  have hne : alpha - 1 ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h0
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0)
  by_contra! hlt
  apply HahnSeries.coeff_order_eq_zero.not.mpr hne
  simp [HahnSeries.coeff_sub, alpha_coeff_of_nonpos _ hlt.le, HahnSeries.coeff_one, hlt.ne]

theorem polyToLaurentInv_zero : polyToLaurentInv (0 : (ZMod 2)[X]) = 0 := by
  simp [polyToLaurentInv]

theorem polyToLaurentInv_one : polyToLaurentInv (1 : (ZMod 2)[X]) = 1 := by
  simp [polyToLaurentInv]

/-- `α` is irrational: a relation `Q α = P` gives `x P² - x Q P + Q² = 0`, so `x` divides `Q` and
then `P`, and cancelling `x` gives a relation with a denominator of smaller degree. -/
theorem alpha_irrational : LaurentIsIrrational alpha := by
  have hUT := laurentInvVar_mul_single_one (K := ZMod 2)
  have hU : laurentInvVar (ZMod 2) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  suffices h : ∀ d : ℕ, ∀ P Q : (ZMod 2)[X], Q.natDegree = d → Q ≠ 0 →
      polyToLaurentInv Q * alpha ≠ polyToLaurentInv P from
    fun P Q hQ => h _ P Q rfl hQ
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P Q hd hQ h
    have hpoly : X * P ^ 2 - X * Q * P + Q ^ 2 = 0 := by
      apply polyToLaurentInv_eq_zero
      simp only [polyToLaurentInv, map_add, map_sub, map_mul, map_pow, aeval_X] at h ⊢
      rw [← h]
      linear_combination (laurentInvVar (ZMod 2) * (aeval (laurentInvVar (ZMod 2)) Q) ^ 2) *
        alpha_sq - (aeval (laurentInvVar (ZMod 2)) Q) ^ 2 * hUT
    obtain ⟨Q₁, rfl⟩ : X ∣ Q :=
      prime_X.dvd_of_dvd_pow (n := 2) ⟨Q * P - P ^ 2, by linear_combination hpoly⟩
    have hQ₁ : Q₁ ≠ 0 := by
      rintro rfl
      simp at hQ
    obtain ⟨P₁, rfl⟩ : X ∣ P := by
      refine prime_X.dvd_of_dvd_pow (n := 2) ⟨Q₁ * P - Q₁ ^ 2, ?_⟩
      apply mul_left_cancel₀ (X_ne_zero (R := ZMod 2))
      linear_combination hpoly
    have hdeg : Q₁.natDegree < d := by
      rw [← hd, natDegree_X_mul hQ₁]
      omega
    apply ih _ hdeg P₁ Q₁ rfl hQ₁
    apply mul_left_cancel₀ hU
    simp only [polyToLaurentInv, map_mul, aeval_X] at h ⊢
    linear_combination h

/-- `α = x α² / (x α² + 1)`, the fixed-point equation with `A = C = x`, `B = 0`, `D = 1`. -/
theorem alpha_fix : alpha = (polyToLaurentInv X * alpha ^ Fintype.card (ZMod 2) +
      polyToLaurentInv (0 : (ZMod 2)[X])) /
    (polyToLaurentInv X * alpha ^ Fintype.card (ZMod 2) + polyToLaurentInv (1 : (ZMod 2)[X])) := by
  have hUT := laurentInvVar_mul_single_one (K := ZMod 2)
  have hU : laurentInvVar (ZMod 2) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hUα : laurentInvVar (ZMod 2) * alpha ≠ 0 := mul_ne_zero hU alpha_ne_zero
  have hden : laurentInvVar (ZMod 2) * alpha ^ 2 + 1 = laurentInvVar (ZMod 2) * alpha := by
    rw [alpha_sq]
    linear_combination -hUT
  rw [ZMod.card, polyToLaurentInv_X, polyToLaurentInv_zero, polyToLaurentInv_one, add_zero, hden,
    eq_div_iff hUα]
  ring

/-- `P/Q = 0/1` is the convergent `P₀/Q₀`, since `b₀ = 0`. -/
theorem alpha_conv : polyToLaurentInv (0 : (ZMod 2)[X]) * laurentConvDen alpha (0 + 1) =
    polyToLaurentInv (1 : (ZMod 2)[X]) * laurentConvNum alpha (0 + 1) := by
  have hb0 : laurentPartialQuotient alpha 0 = 0 := by
    ext i
    simp only [laurentPartialQuotient, laurentCompleteQuotient, laurentPolyPart_coeff,
      HahnSeries.coeff_zero]
    split_ifs with h
    · exact alpha_coeff_of_nonpos i h
    · rfl
  simp [laurentConvDen, laurentConvNum, hb0, polyToLaurentInv_zero, polyToLaurentInv_one]

/-- The closeness condition of clause (i) holds: `v(α - x/x) = 0 < 1 = v(α - 0/1)`. -/
theorem alpha_close_one : (alpha - polyToLaurentInv X / polyToLaurentInv X).order <
    (alpha - polyToLaurentInv (0 : (ZMod 2)[X]) / polyToLaurentInv (1 : (ZMod 2)[X])).order := by
  have hU : laurentInvVar (ZMod 2) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [polyToLaurentInv_X, div_self hU, polyToLaurentInv_zero, polyToLaurentInv_one, zero_div,
    sub_zero, alpha_order, alpha_sub_one_order]
  norm_num

/-- The closeness condition of clause (ii) holds: `α² + 1/x = α`, so
`v(α² + 1/x) = 1 < 2 = 2 v(α - 0/1)`. -/
theorem alpha_close_two :
    (alpha ^ Fintype.card (ZMod 2) +
        polyToLaurentInv (1 : (ZMod 2)[X]) / polyToLaurentInv X).order <
      Fintype.card (ZMod 2) *
        (alpha - polyToLaurentInv (0 : (ZMod 2)[X]) /
          polyToLaurentInv (1 : (ZMod 2)[X])).order := by
  have hUT := laurentInvVar_mul_single_one (K := ZMod 2)
  have hinv : 1 / laurentInvVar (ZMod 2) = HahnSeries.single (1 : ℤ) (1 : ZMod 2) := by
    rw [one_div]
    exact inv_eq_of_mul_eq_one_right hUT
  rw [ZMod.card, polyToLaurentInv_X, polyToLaurentInv_zero, polyToLaurentInv_one, zero_div,
    sub_zero, hinv, alpha_sq, sub_add_cancel, alpha_order]
  norm_num

-- Clause (i) at `P/Q = 0/1`: `S₁ = x`, `R₁ = 0` and `Δ = x`, so `v(x α²) = 1` gives `v(b₁) = -1`.
example : (laurentPartialQuotient alpha 1).order = -1 := by
  have hU : laurentInvVar (ZMod 2) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hUord : (laurentInvVar (ZMod 2)).order = -1 := HahnSeries.order_single one_ne_zero
  have h := (laurentMobius_order_identities X 0 X 1 (by simp [X_ne_zero]) X_ne_zero alpha
    alpha_irrational alpha_fix 0 0 1 isCoprime_one_right one_ne_zero alpha_conv).1 alpha_close_one
  simp only [mul_zero, mul_one, zero_mul, zero_add, sub_zero, ZMod.card,
    polyToLaurentInv_X, polyToLaurentInv_zero, natDegree_X] at h
  rw [HahnSeries.order_mul hU (pow_ne_zero 2 alpha_ne_zero), HahnSeries.order_pow, alpha_order,
    hUord] at h
  norm_num at h
  omega

-- Clause (ii) at `P/Q = 0/1`: `S₂ = 1`, `R₂ = 0` and `Δ = x`, so `v(α) = 1` gives `v(b₁) = -1`.
example : (laurentPartialQuotient alpha 1).order = -1 := by
  have h := (laurentMobius_order_identities X 0 X 1 (by simp [X_ne_zero]) X_ne_zero alpha
    alpha_irrational alpha_fix 0 0 1 isCoprime_one_right one_ne_zero alpha_conv).2 alpha_close_two
  simp only [ZMod.card, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow,
    mul_zero, mul_one, zero_mul, zero_add, sub_zero, polyToLaurentInv_zero, polyToLaurentInv_one,
    one_mul, natDegree_one, natDegree_X, alpha_order] at h
  omega

end MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities
