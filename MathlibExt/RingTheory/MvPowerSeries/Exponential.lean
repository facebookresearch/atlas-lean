/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Exp.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
reuse Mathlib's exponential and lawful substitution, restrict the exponential
API to zero constant coefficient, and restate the finite coefficient laws.
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Exponential of a multivariate formal power series

For a commutative ℚ-algebra, `expOfConstantCoeffZero w hw` substitutes `w` into
Mathlib's `PowerSeries.exp`. The hypothesis `hw` makes this formal substitution
lawful. Each coefficient is the coefficient of the finite sum `expTrunc N w`
when its total degree is less than `N`. No analytic convergence is asserted.

The finite sum is defined for arbitrary `w`. The source's degreewise constructor
represents a formal exponential on the zero constant coefficient domain; the
coefficient theorem below identifies it with canonical substitution on that domain.
-/

@[expose] public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

/-- The finite sum `∑ n < N, wⁿ/n!`, defined without a constant coefficient restriction. -/
noncomputable def expTrunc (N : ℕ) (w : MvPowerSeries σ R) : MvPowerSeries σ R :=
  ∑ n ∈ range N, ((n.factorial : ℚ)⁻¹) • w ^ n

/-- The formal exponential of a series with zero constant coefficient, obtained
by substituting it into Mathlib's canonical exponential power series. -/
noncomputable def expOfConstantCoeffZero (w : MvPowerSeries σ R)
    (hw : constantCoeff w = 0) : MvPowerSeries σ R :=
  substAlgHom (hasSubst_of_constantCoeff_zero (fun _ : Unit => hw)) (PowerSeries.exp R)

/-- The exponential API is the canonical univariate exponential substituted at `w`. -/
theorem expOfConstantCoeffZero_eq_subst (w : MvPowerSeries σ R)
    (hw : constantCoeff w = 0) :
    expOfConstantCoeffZero w hw = PowerSeries.subst w (PowerSeries.exp R) := by
  exact substAlgHom_apply _ _

/-- A coefficient of the exponential is computed by any truncation extending past its degree.
This is the exact finite-sum formula used by the source's degreewise constructor. -/
theorem coeff_expOfConstantCoeffZero (w : MvPowerSeries σ R) (hw : constantCoeff w = 0)
    (d : σ →₀ ℕ) {N : ℕ} (hN : d.degree < N) :
    coeff d (expOfConstantCoeffZero w hw) = coeff d (expTrunc N w) := by
  classical
  rw [expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hw)]
  have hpow {n : ℕ} (hn : d.degree < n) : coeff d (w ^ n) = 0 :=
    coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hw) (by omega)
  rw [finsum_eq_sum_of_support_subset _ (s := range N)]
  · simp only [expTrunc, map_sum, PowerSeries.coeff_exp, one_div]
    apply sum_congr rfl
    intro n _
    rw [map_rat_smul]
    simp [Algebra.smul_def, smul_eq_mul]
  · intro n hn
    by_contra h
    have hn' : N ≤ n := by simpa using h
    exact hn (by
      dsimp
      rw [hpow (lt_of_lt_of_le hN hn'), mul_zero])

/-- In particular, the coefficient of degree `d.degree` uses exactly the terms `n ≤ d.degree`. -/
theorem coeff_expOfConstantCoeffZero_degree (w : MvPowerSeries σ R)
    (hw : constantCoeff w = 0) (d : σ →₀ ℕ) :
    coeff d (expOfConstantCoeffZero w hw) = coeff d (expTrunc (d.degree + 1) w) :=
  coeff_expOfConstantCoeffZero w hw d (Nat.lt_succ_self _)

/-- The constant coefficient of the formal exponential is one. -/
@[simp] theorem constantCoeff_expOfConstantCoeffZero (w : MvPowerSeries σ R)
    (hw : constantCoeff w = 0) : constantCoeff (expOfConstantCoeffZero w hw) = 1 := by
  rw [expOfConstantCoeffZero_eq_subst,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero hw]
  simp

/-- The exponential of the zero series is one. -/
@[simp] theorem expOfConstantCoeffZero_zero :
    expOfConstantCoeffZero (0 : MvPowerSeries σ R) (map_zero _) = 1 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

/-- Applying a coefficient ring homomorphism commutes with the formal exponential. -/
theorem map_expOfConstantCoeffZero {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (w : MvPowerSeries σ R) (hw : constantCoeff w = 0) :
    map f (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero (map f w) (by rw [constantCoeff_map, hw, map_zero]) := by
  rw [expOfConstantCoeffZero_eq_subst, expOfConstantCoeffZero_eq_subst,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hw), PowerSeries.map_exp]

/-- Substituting a variable recovers the canonical exponential in that variable. -/
@[simp] theorem expOfConstantCoeffZero_X (i : σ) :
    expOfConstantCoeffZero (X i : MvPowerSeries σ R) (constantCoeff_X i) =
      (PowerSeries.exp R).toMvPowerSeries i := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.toMvPowerSeries_eq_subst]

private theorem sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ)
    (F : ℕ → ℕ → M) (h : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ n ∈ range N, ∑ p ∈ antidiagonal n, F p.1 p.2 =
      ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
  rw [← sum_product' (range N) (range N) F]
  have h1 : ∑ p ∈ range N ×ˢ range N, F p.1 p.2 =
      ∑ p ∈ (range N ×ˢ range N) with p.1 + p.2 < N, F p.1 p.2 := by
    rw [sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · exact h p.1 p.2 (by omega)
  rw [h1, ← sum_fiberwise_of_maps_to (t := range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2)
    (fun p hp => mem_range.2 (mem_filter.1 hp).2)]
  refine sum_congr rfl fun n hn => sum_congr ?_ fun _ _ => rfl
  have hn' := mem_range.1 hn
  ext p
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_range]
  omega

omit [Algebra ℚ R] in
private theorem coeff_mul_congr {f f' g g' : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (hf : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e f = coeff e f')
    (hg : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e g = coeff e g') :
    coeff d (f * g) = coeff d (f' * g') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have h := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h
  rw [hf p.1 (by omega), hg p.2 (by omega)]

omit [Algebra ℚ R] in
private theorem coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {d : σ →₀ ℕ} {i j : ℕ}
    (h : d.degree < i + j) : coeff d (a ^ i * b ^ j) = 0 := by
  classical
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have h' := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h'
  by_cases h1 : p.1.degree < i
  · rw [coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      (by simpa using ha) (by omega), zero_mul]
  · rw [coeff_eq_zero_of_constantCoeff_nilpotent (f := b) (d := p.2) (n := j) (m := 1)
      (by simpa using hb) (by omega), mul_zero]

private theorem add_pow_div (a b : MvPowerSeries σ R) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹) • (a + b) ^ n =
      ∑ p ∈ antidiagonal n,
        ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • (a ^ p.1 * b ^ p.2) := by
  rw [(Commute.all a b).add_pow', smul_sum]
  refine sum_congr rfl fun p hp => ?_
  have hn := mem_antidiagonal.1 hp
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [hn, ← Nat.choose_symm_of_eq_add hn.symm] at h
  have h' : ((n.choose p.1 : ℕ) : ℚ) * p.1.factorial * p.2.factorial = n.factorial := by
    exact_mod_cast h
  have h1 : (p.1.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

/-- The formal exponential carries sums of series with zero constant coefficient to products. -/
theorem expOfConstantCoeffZero_add {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    expOfConstantCoeffZero (a + b) (by rw [map_add, ha, hb, add_zero]) =
      expOfConstantCoeffZero a ha * expOfConstantCoeffZero b hb := by
  ext d
  rw [coeff_mul_congr (f' := expTrunc (d.degree + 1) a)
    (g' := expTrunc (d.degree + 1) b)
    (fun e he => coeff_expOfConstantCoeffZero a ha e (by omega))
    (fun e he => coeff_expOfConstantCoeffZero b hb e (by omega)),
    coeff_expOfConstantCoeffZero_degree]
  unfold expTrunc
  rw [sum_mul_sum, map_sum, map_sum]
  simp only [add_pow_div, map_sum, smul_mul_smul_comm]
  refine sum_triangle (d.degree + 1)
    (fun i j => coeff d
      (((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) • (a ^ i * b ^ j))) ?_
  intro i j hij
  rw [map_rat_smul, coeff_pow_mul_pow_eq_zero ha hb (by omega), smul_zero]

end MvPowerSeries
