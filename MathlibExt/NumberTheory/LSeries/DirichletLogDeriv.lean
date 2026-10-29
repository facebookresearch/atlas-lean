/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletXi
import MathlibExt.Analysis.Complex.RectangleResidue
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The logarithmic derivative of Dirichlet `L`-functions

We collect estimates for `-L'/L(s, χ)` near the line `Re s = 1` that underlie zero-free regions.

## Main definitions

* `DirichletCharacter.logDerivConstAtZero χ`: the constant `b(χ)` in the Laurent expansion
  `L'/L(s, χ) = 1/s + b(χ) + O(s)` at `s = 0`.

## Main statements

* `DirichletCharacter.neg_logDeriv_LFunction_eq_LSeries_vonMangoldt`:
  `-L'/L(s, χ) = ∑ χ(n) Λ(n) n⁻ˢ` for `Re s > 1`.
* `DirichletCharacter.re_neg_logDeriv_three_four_one_nonneg`: the `3`-`4`-`1` inequality
  `3 Re(-ζ'/ζ(σ)) + 4 Re(-L'/L(σ + iγ, χ)) + Re(-L'/L(σ + 2iγ, χ²)) ≥ 0`.
* `DirichletCharacter.re_neg_logDeriv_riemannZeta_add_LFunction_nonneg`:
  `Re(-ζ'/ζ(σ)) + Re(-L'/L(σ, χ)) ≥ 0`.
* `DirichletCharacter.LFunction_changeLevel_eq_zero_iff`,
  `DirichletCharacter.analyticOrderAt_LFunction_changeLevel`: on `Re s > 0`, changing the level
  of a nonprincipal character changes neither the zeros of `L(s, χ)` nor their orders.
* `DirichletCharacter.neg_re_logDeriv_LFunction_changeLevel_le`: on `Re s > 1`, changing the level
  to `N` moves `-Re L'/L` by at most `log N`.
* `DirichletCharacter.logDerivConstAtZero_eq_logDeriv`: if `L(s, χ) = s E(s)` near `0` with `E`
  analytic and nonvanishing at `0`, then `b(χ) = E'(0)/E(0)`.
* `DirichletCharacter.exists_neg_re_logDeriv_LFunction_le`: **the Hadamard bound**
  `-Re L'/L(s, χ) ≤ ½ log (q (|t| + 2)) + C - ∑_ρ m_ρ Re (1 / (s - ρ))` for primitive `χ ≠ 1`,
  `1 < Re s ≤ 2`, and any finite set of zeros `ρ` with `Re ρ > 0`, counted with multiplicity at
  most their order.
-/

@[expose] public section

open Filter Topology

namespace DirichletCharacter

section LSeries

variable {N : ℕ} [NeZero N]

/-- `-L'/L(s, χ) = ∑ χ(n) Λ(n) n⁻ˢ` on `Re s > 1`. -/
theorem neg_logDeriv_LFunction_eq_LSeries_vonMangoldt (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (LFunction χ) s =
      LSeries ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : LFunction χ =ᶠ[𝓝 s] LSeries (fun n => χ n) :=
    eventually_of_mem (hopen.mem_nhds hs) fun w hw => LFunction_eq_LSeries χ hw
  rw [LSeries_twist_vonMangoldt_eq χ hs, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, neg_div]

/-- **The `3`-`4`-`1` inequality** for `σ > 1`:
`0 ≤ 3 Re(-ζ'/ζ(σ)) + 4 Re(-L'/L(σ + iγ, χ)) + Re(-L'/L(σ + 2iγ, χ²))`. -/
theorem re_neg_logDeriv_three_four_one_nonneg (χ : DirichletCharacter ℂ N) {σ : ℝ} (γ : ℝ)
    (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re
      + 4 * (-logDeriv (LFunction χ) ((σ : ℂ) + γ * Complex.I)).re
      + (-logDeriv (LFunction (χ ^ 2)) ((σ : ℂ) + 2 * γ * Complex.I)).re := by
  have hZ : ∀ Z : ℂ, ‖Z‖ ≤ 1 → 0 ≤ (3 + 4 * Z + Z ^ 2).re := by
    intro Z hZ
    have h := Complex.sq_norm Z
    rw [Complex.normSq_apply] at h
    have h1 : ‖Z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Z]
    simp only [Complex.add_re, Complex.mul_re, pow_two]
    norm_num
    nlinarith [sq_nonneg (Z.re + 1)]
  have hs1 : 1 < ((σ : ℂ) + γ * Complex.I).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * γ * Complex.I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries_vonMangoldt χ hs1,
    neg_logDeriv_LFunction_eq_LSeries_vonMangoldt (χ ^ 2) hs2, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0]
  have H := (((ArithmeticFunction.LSeriesSummable_vonMangoldt hs0).LSeriesHasSum.mul_left 3).add
    ((LSeriesSummable_twist_vonMangoldt χ hs1).LSeriesHasSum.mul_left 4)).add
    (LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2).LSeriesHasSum
  have HR := Complex.hasSum_re H
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at HR
  refine HR.nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < n := by positivity
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((n : ℂ) ^ ((γ : ℂ) * Complex.I))⁻¹ := ⟨_, rfl⟩
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_inv, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hr]; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have e0 : (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ) = (r : ℂ) := by
    rw [hr, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hnpos.le]; push_cast; ring
  have e1 : χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + γ * Complex.I)
      = r * (χ n * w) := by
    rw [Complex.cpow_add _ _ hn', ← e0, hw]; field_simp
  have e2 : (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (n : ℂ) ^ ((σ : ℂ) + 2 * γ * Complex.I) = r * (χ n * w) ^ 2 := by
    rw [MulChar.pow_apply' _ two_ne_zero,
      show (σ : ℂ) + 2 * γ * Complex.I = σ + ((2 : ℕ) : ℂ) * (γ * Complex.I) by push_cast; ring,
      Complex.cpow_add _ _ hn', Complex.cpow_nat_mul, ← e0, hw]
    field_simp
  rw [e0, e1, e2]
  have hZ1 : ‖χ n * w‖ ≤ 1 := by
    rw [norm_mul, hwn, mul_one]; exact norm_le_one χ n
  have h3 := hZ _ hZ1
  generalize χ n * w = Z at h3 ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at h3
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
  linarith only [mul_nonneg hr0 h3]

/-- The `1`-`1` inequality: `0 ≤ Re(-ζ'/ζ(σ)) + Re(-L'/L(σ, χ))` for `σ > 1`. -/
theorem re_neg_logDeriv_riemannZeta_add_LFunction_nonneg (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 1 < σ) :
    0 ≤ (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re
      + (-logDeriv (LFunction χ) (σ : ℂ)).re := by
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries_vonMangoldt χ hs0, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0]
  have H := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs0).LSeriesHasSum.add
    (LSeriesSummable_twist_vonMangoldt χ hs0).LSeriesHasSum
  have HR := Complex.hasSum_re H
  simp only [Complex.add_re] at HR
  refine HR.nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply]
  have hnpos : (0 : ℝ) < n := by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hr]; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have e0 : (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ) = (r : ℂ) := by
    rw [hr, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hnpos.le]; push_cast; ring
  have e1 : χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ) = r * χ n := by
    rw [← e0]; ring
  rw [e0, e1, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h1 : -1 ≤ (χ n).re := by
    have := norm_le_one χ n
    have := Complex.abs_re_le_norm (χ n)
    linarith [neg_abs_le (χ n).re]
  have := mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 + (χ n).re)
  linarith

end LSeries

/-! ### Changing the level -/

section ChangeLevel

/-- The extra Euler factors `∏_{p ∣ N} (1 - χ(p) p⁻ʷ)` do not vanish on `Re w > 0`. -/
theorem prod_one_sub_mul_cpow_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M) (N : ℕ) {w : ℂ}
    (hw : 0 < w.re) : ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-w)) ≠ 0 := by
  intro h
  obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hnorm : ‖χ p * (p : ℂ) ^ (-w)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos]
    have h1 : (p : ℝ) ^ (-w).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by simp; linarith)
    have h3 := norm_le_one χ p
    calc ‖χ p‖ * (p : ℝ) ^ (-w).re ≤ 1 * (p : ℝ) ^ (-w).re := by gcongr
      _ < 1 := by linarith
  have hu1 : χ p * (p : ℂ) ^ (-w) = 1 := by linear_combination -hp0
  rw [hu1, norm_one] at hnorm
  exact lt_irrefl _ hnorm

variable {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N) {χ : DirichletCharacter ℂ M}
include h

/-- On `Re w > 0`, `L(w, changeLevel h χ) = 0 ↔ L(w, χ) = 0` for `χ ≠ 1`. -/
theorem LFunction_changeLevel_eq_zero_iff (hχ : χ ≠ 1) {w : ℂ} (hw : 0 < w.re) :
    LFunction (changeLevel h χ) w = 0 ↔ LFunction χ w = 0 := by
  rw [LFunction_changeLevel h χ (Or.inl hχ), mul_eq_zero,
    or_iff_left (prod_one_sub_mul_cpow_ne_zero χ N hw)]

/-- On `Re w > 0`, `L(·, changeLevel h χ)` and `L(·, χ)` vanish to the same order at `w`, for
`χ ≠ 1`. -/
theorem analyticOrderAt_LFunction_changeLevel (hχ : χ ≠ 1) {w : ℂ} (hw : 0 < w.re) :
    analyticOrderAt (LFunction (changeLevel h χ)) w = analyticOrderAt (LFunction χ) w := by
  have hLeq : LFunction (changeLevel h χ) = fun w => LFunction χ w *
      ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-w)) :=
    funext fun w => LFunction_changeLevel h χ (Or.inl hχ)
  have hL1a : AnalyticAt ℂ (LFunction χ) w := (differentiable_LFunction hχ).analyticAt w
  have hEa : AnalyticAt ℂ (fun w => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-w))) w := by
    refine Differentiable.analyticAt (fun w => ?_) w
    have hfac : ∀ p ∈ N.primeFactors,
        DifferentiableAt ℂ (fun w : ℂ => 1 - χ p * (p : ℂ) ^ (-w)) w := by
      intro p hp
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
        ((differentiableAt_id.neg).const_cpow (Or.inl hp0)))
    have := DifferentiableAt.finsetProd hfac
    simpa [Finset.prod_fn] using this
  have hE0 : analyticOrderAt (fun w => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-w))) w = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (prod_one_sub_mul_cpow_ne_zero χ N hw))
  have hmul := analyticOrderAt_mul hL1a hEa
  rw [hE0, add_zero] at hmul
  rw [hLeq]
  exact hmul

/-- Changing the level to `N` moves `-Re L'/L` by at most `log N` on `Re s > 1` (for any `χ`,
including the trivial character). -/
theorem neg_re_logDeriv_LFunction_changeLevel_le {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv (LFunction (changeLevel h χ)) s).re ≤
      -(logDeriv (LFunction χ) s).re + Real.log N := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  set E : ℂ → ℂ := fun w => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-w)) with hE
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : LFunction (changeLevel h χ) =ᶠ[𝓝 s] fun w => LFunction χ w * E w :=
    eventually_of_mem (hopen.mem_nhds hs) fun w hw =>
      LFunction_changeLevel h χ (Or.inr (by rintro rfl; simp at hw))
  have hfun : logDeriv (LFunction (changeLevel h χ)) s =
      logDeriv (fun w => LFunction χ w * E w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hfac : ∀ p ∈ N.primeFactors, ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos]
    have h1 : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
    have h3 := norm_le_one χ p
    calc ‖χ p‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ ≤ 1 / 2 := by linarith
  have hne : ∀ p ∈ N.primeFactors, 1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp h
    have := hfac p hp
    have hu : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [hu, norm_one] at this; norm_num at this
  have hderiv : ∀ p ∈ N.primeFactors, HasDerivAt (fun w : ℂ => 1 - χ p * (p : ℂ) ^ (-w))
      (χ p * (p : ℂ) ^ (-s) * Complex.log p) s := by
    intro p hp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have := (((hasDerivAt_id' s).neg.const_cpow (c := (p : ℂ)) (Or.inl hp0)).const_mul
      (χ p)).const_sub 1
    convert this using 1
    simp only [Pi.neg_apply]
    ring
  have hEs : E s ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hEd : DifferentiableAt ℂ E s := by
    rw [hE]; exact DifferentiableAt.fun_finsetProd fun p hp => (hderiv p hp).differentiableAt
  have hLs := LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hLd := differentiableAt_LFunction χ s (Or.inl hs1)
  rw [hfun, logDeriv_fun_mul s hLs hEs hLd hEd]
  have hlogE : logDeriv E s = ∑ p ∈ N.primeFactors,
      χ p * (p : ℂ) ^ (-s) * Complex.log p / (1 - χ p * (p : ℂ) ^ (-s)) := by
    rw [hE, logDeriv_fun_prod hne (fun p hp => (hderiv p hp).differentiableAt)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [logDeriv_apply, (hderiv p hp).deriv]
  rw [hlogE, Complex.add_re, Complex.re_sum]
  have hbd : ∀ p ∈ N.primeFactors, -(χ p * (p : ℂ) ^ (-s) * Complex.log p /
      (1 - χ p * (p : ℂ) ^ (-s))).re ≤ Real.log p := by
    intro p hp
    have hu := hfac p hp
    have h1u : 1 / 2 ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
      rw [norm_one] at this; linarith
    have hlp : ‖Complex.log p‖ = Real.log p := by
      rw [← Complex.natCast_log, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
    have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hab := Complex.abs_re_le_norm (χ p * (p : ℂ) ^ (-s) * Complex.log p /
      (1 - χ p * (p : ℂ) ^ (-s)))
    rw [norm_div, norm_mul, hlp, le_div_iff₀ (by linarith)] at hab
    have hab' := neg_abs_le (χ p * (p : ℂ) ^ (-s) * Complex.log p /
      (1 - χ p * (p : ℂ) ^ (-s))).re
    have hm1 : ‖χ p * (p : ℂ) ^ (-s)‖ * Real.log p ≤ (1 / 2) * Real.log p :=
      mul_le_mul_of_nonneg_right hu hlp0
    have hm2 : (1 / 2) * Real.log p ≤ Real.log p * ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
      nlinarith
    have hpos : 0 < ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by linarith
    have key : |(χ p * (p : ℂ) ^ (-s) * Complex.log p /
        (1 - χ p * (p : ℂ) ^ (-s))).re| ≤ Real.log p := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_right hc hpos
      linarith
    linarith
  have hsum : ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
    rw [← Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    · rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd hN0 (Nat.prod_primeFactors_dvd N)
  have := Finset.sum_le_sum hbd
  rw [Finset.sum_neg_distrib] at this
  linarith

end ChangeLevel

/-! ### The Hadamard bound -/

/-- **The Hadamard bound for `-Re L'/L`.** There is an absolute constant `C` such that for every
primitive nonprincipal `χ` modulo `N`, every `s` with `1 < Re s ≤ 2`, and every finite set `S` of
points with `Re ρ > 0`, each counted `m ρ` times with `m ρ` at most the order of vanishing of
`L(s, χ)` at `ρ`,
`-Re L'/L(s, χ) ≤ ½ log (N (|Im s| + 2)) + C - ∑_{ρ ∈ S} m ρ Re (1 / (s - ρ))`. -/
theorem exists_neg_re_logDeriv_LFunction_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → ∀ (S : Finset ℂ) (m : ℂ → ℕ),
        (∀ ρ ∈ S, 0 < ρ.re ∧ (m ρ : ℕ∞) ≤ analyticOrderAt (LFunction χ) ρ) →
        -(logDeriv (LFunction χ) s).re ≤
          Real.log (N * (|s.im| + 2)) / 2 + C - ∑ ρ ∈ S, (m ρ : ℝ) * (1 / (s - ρ)).re := by
  classical
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  refine ⟨|C|, fun N _ ψ hψ hψ1 s hs1 hs2 S m hS => ?_⟩
  set f := xi ψ with hf
  have hd : Differentiable ℂ f := differentiable_xi hψ1
  have hX0 : f 0 ≠ 0 := xi_zero_ne_zero hψ hψ1
  have hfin := Complex.analyticOrderAt_ne_top_of_differentiable hd hX0
  set M : ℂ → ℕ := fun w => (analyticOrderAt f w).toNat with hM
  let z : (Σ w : ℂ, Fin (M w)) → ℂ := Sigma.fst
  have hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w :=
    Complex.card_sigma_fin_analyticOrderAt hd hX0
  obtain ⟨A, B, hAB⟩ := exists_xi_eq_exp_mul_tprod hψ hψ1 hz
  have hRe := hasSum_re_one_div_of_xi_eq_exp_mul_tprod hψ hψ1 hz hAB
  have hzero : ∀ n, f (z n) = 0 := Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz
  have hz0 : ∀ n, z n ≠ 0 := fun n h => hX0 (h ▸ hzero n)
  have hzre : ∀ n, (z n).re ≤ 1 := fun n => ((xi_eq_zero_iff hψ hψ1 (z n)).mp (hzero n)).2.2.le
  have hsum := Complex.summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one hd
    (hasGrowthOrderLE_xi hψ1) hX0 hz
  have hm := Complex.summable_one_div_sub_add_one_div hz0 hsum s
  have hfs : f s ≠ 0 := by
    rw [hf, Ne, xi_eq_zero_iff hψ hψ1]
    exact fun h => by linarith [h.2.2]
  -- the log-derivative of the product
  have hLDs : logDeriv f s = B + ∑' n, (1 / (s - z n) + 1 / z n) :=
    Complex.logDeriv_eq_add_tsum_of_eq_exp_mul_tprod hz0 hsum hAB hzero (hd s) hfs
  -- the gamma factor
  obtain ⟨a, ha, hapar, hgf⟩ : ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ (1 - ψ (-1)) / 2 = (a : ℂ) ∧
      ∀ w, ψ.gammaFactor w = Complex.Gammaℝ (w + a) := by
    rcases ψ.even_or_odd with h | h
    · refine ⟨0, Or.inl rfl, ?_, fun w => ?_⟩
      · rw [show ψ (-1) = 1 from h]; simp
      · rw [h.gammaFactor_def]; simp
    · refine ⟨1, Or.inr rfl, ?_, fun w => ?_⟩
      · rw [show ψ (-1) = -1 from h]; norm_num
      · rw [h.gammaFactor_def]; simp
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> rw [h]; norm_num
  have ha1 : a ≤ 1 := by rcases ha with h | h <;> rw [h]; norm_num
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun w : ℂ => (N : ℂ) ^ ((w + a) / 2) *
      ((Real.pi : ℂ) ^ (-(w + a) / 2) * Complex.Gamma ((w + a) / 2)) := ⟨_, rfl⟩
  have hxiEq : ∀ w : ℂ, 0 < w.re → f w = G w * LFunction ψ w := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have hg : ψ.gammaFactor w ≠ 0 := by
      rw [hgf]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hGw : G w = (N : ℂ) ^ ((w + a) / 2) * ψ.gammaFactor w := by
      rw [hG, hgf, Complex.Gammaℝ_def]
    rw [hf, xi, hapar, hGw, LFunction_eq_completed_div_gammaFactor ψ w (Or.inl hw0),
      mul_assoc, mul_div_cancel₀ _ hg]
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : f =ᶠ[𝓝 s] fun w => G w * LFunction ψ w :=
    eventually_of_mem (hopen.mem_nhds hs1) fun w hw => hxiEq w (lt_trans one_pos hw)
  have hLs : LFunction ψ s ≠ 0 := LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) hs1.le
  have hLd : DifferentiableAt ℂ (LFunction ψ) s := differentiableAt_LFunction ψ s (Or.inr hψ1)
  have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hure : ((s + a) / 2).re = (s.re + a) / 2 := by simp
  have huim : ((s + a) / 2).im = s.im / 2 := by simp
  have hupos : 0 < ((s + a) / 2).re := by rw [hure]; linarith
  have hGm0 : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, (w + a) / 2 ≠ -m := by
    intro w hw m hm
    have h1 := congrArg Complex.re hm
    have hwre : ((w + a) / 2).re = (w.re + a) / 2 := by simp
    rw [hwre] at h1
    simp at h1
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGm : ∀ m : ℕ, (s + a) / 2 ≠ -m := hGm0 s (by linarith)
  have hlin : HasDerivAt (fun w : ℂ => (w + a) / 2) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).add_const (a : ℂ)).div_const 2
  have hlin' : HasDerivAt (fun w : ℂ => -(w + a) / 2) (-1 / 2) s := by
    simpa using (((hasDerivAt_id s).add_const (a : ℂ)).neg).div_const 2
  have h1 := hlin.const_cpow (c := (N : ℂ)) (Or.inl hNz)
  have h2 := hlin'.const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
  have hΓd : DifferentiableAt ℂ Complex.Gamma ((s + a) / 2) :=
    Complex.differentiableAt_Gamma _ hGm
  have h3 : HasDerivAt (fun w : ℂ => Complex.Gamma ((w + a) / 2))
      (deriv Complex.Gamma ((s + a) / 2) * (1 / 2)) s :=
    hΓd.hasDerivAt.comp s hlin
  have hΓ0 : Complex.Gamma ((s + a) / 2) ≠ 0 := Complex.Gamma_ne_zero hGm
  have hNs : (N : ℂ) ^ ((s + a) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hNz]
  have hπs : (Real.pi : ℂ) ^ (-(s + a) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
  have hGd := h1.mul (h2.mul h3)
  rw [show ((fun x : ℂ => (N : ℂ) ^ ((x + a) / 2)) * ((fun x : ℂ => (Real.pi : ℂ) ^
    (-(x + a) / 2)) * fun w : ℂ => Complex.Gamma ((w + a) / 2))) = G by
      rw [hG]; rfl] at hGd
  have hGs : G s ≠ 0 := by rw [hG]; exact mul_ne_zero hNs (mul_ne_zero hπs hΓ0)
  have hLf : logDeriv f s = logDeriv G s + logDeriv (LFunction ψ) s := by
    rw [← logDeriv_fun_mul s hGs hLs hGd.differentiableAt hLd, logDeriv_apply, logDeriv_apply,
      hev.deriv_eq, hev.eq_of_nhds]
  have hLG : logDeriv G s = Complex.log N / 2 - Complex.log Real.pi / 2
      + Complex.digamma ((s + a) / 2) / 2 := by
    rw [logDeriv_apply, hGd.deriv, Complex.digamma_def, logDeriv_apply, hG]
    simp only [Pi.mul_apply]
    field_simp
    ring
  -- the zero terms
  have hT1 : HasSum (fun n => (1 / (s - z n)).re)
      ((∑' n, (1 / (s - z n) + 1 / z n)).re + B.re) := by
    have := (Complex.hasSum_re hm.hasSum).sub hRe
    simp only [Complex.add_re, add_sub_cancel_right, sub_neg_eq_add] at this
    exact this
  have hnn : ∀ n, 0 ≤ (1 / (s - z n)).re := fun n => by
    rw [one_div, Complex.inv_re, Complex.sub_re]
    exact div_nonneg (by linarith [hzre n]) (Complex.normSq_nonneg _)
  -- each zero of `L` in `S` is a zero of `ξ` of at least the same order
  have hGdiff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ G w := by
    intro w hw
    have hl : DifferentiableAt ℂ (fun w : ℂ => (w + a) / 2) w := by fun_prop
    have hl' : DifferentiableAt ℂ (fun w : ℂ => -(w + a) / 2) w := by fun_prop
    rw [hG]
    exact (hl.const_cpow (Or.inl hNz)).mul ((hl'.const_cpow (Or.inl hpi)).mul
      ((Complex.differentiableAt_Gamma _ (hGm0 w hw)).comp w hl))
  have hopen0 : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmM : ∀ ρ ∈ S, m ρ ≤ M ρ := by
    intro ρ hρ
    obtain ⟨hρre, hρord⟩ := hS ρ hρ
    have hGa : AnalyticAt ℂ G ρ :=
      DifferentiableOn.analyticAt (fun w hw => (hGdiff w hw).differentiableWithinAt)
        (hopen0.mem_nhds hρre)
    have hLa : AnalyticAt ℂ (LFunction ψ) ρ := (differentiable_LFunction hψ1).analyticAt ρ
    have hGρ : G ρ ≠ 0 := by
      rw [hG]
      exact mul_ne_zero (by simp [Complex.cpow_eq_zero_iff, hNz])
        (mul_ne_zero (by simp [Complex.cpow_eq_zero_iff, hpi])
          (Complex.Gamma_ne_zero (hGm0 ρ hρre)))
    have hford : (m ρ : ℕ∞) ≤ analyticOrderAt f ρ := by
      have hev0 : f =ᶠ[𝓝 ρ] G * LFunction ψ :=
        eventually_of_mem (hopen0.mem_nhds hρre) fun w hw => hxiEq w hw
      rw [analyticOrderAt_congr hev0, analyticOrderAt_mul hGa hLa,
        analyticOrderAt_eq_zero.mpr (Or.inr hGρ), zero_add]
      exact hρord
    rw [← ENat.natCast_toNat (hfin ρ)] at hford
    exact_mod_cast hford
  have hxT : ∑ ρ ∈ S, (m ρ : ℝ) * (1 / (s - ρ)).re ≤
      (∑' n, (1 / (s - z n) + 1 / z n)).re + B.re := by
    let I : Finset (Σ w : ℂ, Fin (M w)) := S.sigma fun ρ =>
      if h : m ρ ≤ M ρ then (Finset.univ : Finset (Fin (m ρ))).map (Fin.castLEEmb h) else ∅
    have hI : ∑ n ∈ I, (1 / (s - z n)).re = ∑ ρ ∈ S, (m ρ : ℝ) * (1 / (s - ρ)).re := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [dite_eq_left (hmM ρ hρ), Finset.sum_map]
      simp only [z, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := sum_le_hasSum I (fun j _ => hnn j) hT1
    rwa [hI] at this
  -- the digamma term
  have hu0 : (s + a) / 2 ≠ 0 := fun h => by rw [h] at hupos; simp at hupos
  have harg : |Complex.arg ((s + a) / 2)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hupos)
  have hCu := hC _ hu0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
  have hun1 : 1 / 2 ≤ ‖(s + a) / 2‖ :=
    le_trans (by rw [hure]; linarith) ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hun2 : ‖(s + a) / 2‖ ≤ |s.im| + 2 := by
    calc ‖(s + a) / 2‖ ≤ |((s + a) / 2).re| + |((s + a) / 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re + a) / 2 + |s.im| / 2 := by
          rw [hure, huim, abs_of_pos (by linarith), abs_div, abs_two]
      _ ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hdg : (Complex.digamma ((s + a) / 2)).re ≤ Real.log (|s.im| + 2) + 2 * |C| := by
    have h3 : (Complex.digamma ((s + a) / 2) - Complex.log ((s + a) / 2)).re ≤ 2 * |C| := by
      calc _ ≤ ‖Complex.digamma ((s + a) / 2) - Complex.log ((s + a) / 2)‖ :=
            Complex.re_le_norm _
        _ ≤ C / ‖(s + a) / 2‖ := hCu
        _ ≤ |C| / ‖(s + a) / 2‖ := by gcongr; exact le_abs_self C
        _ ≤ |C| / (1 / 2) := by gcongr
        _ = 2 * |C| := by ring
    rw [Complex.sub_re, Complex.log_re] at h3
    have := Real.log_le_log (by linarith) hun2
    linarith
  have hLL : logDeriv (LFunction ψ) s = logDeriv f s - logDeriv G s := by
    rw [hLf]; ring
  rw [hLL, hLDs, hLG]
  have hlogN : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [Complex.log_re, Complex.norm_natCast]
  have hlogπ : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, hlogN, hlogπ]
  have hπ1 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNl : Real.log (N * (|s.im| + 2)) = Real.log N + Real.log (|s.im| + 2) :=
    Real.log_mul hN0.ne' (by positivity)
  linarith

/-! ### The constant term of `L'/L` at `0` -/

section LogDerivConst

variable {N : ℕ} [NeZero N]

/-- **The constant `b(χ)`**: the constant term of the logarithmic derivative of `L(s, χ)` at
`s = 0`, i.e. `lim_{s → 0} (L'(s, χ)/L(s, χ) - 1/s)`, the limit taken over `s ≠ 0`. It is
meaningful when `L(s, χ)` has a simple zero at `0` (an even primitive nonprincipal `χ`), see
`DirichletCharacter.logDerivConstAtZero_eq_logDeriv`; otherwise the limit need not exist and the
value is junk. -/
noncomputable def logDerivConstAtZero (χ : DirichletCharacter ℂ N) : ℂ :=
  limUnder (𝓝[≠] (0 : ℂ)) fun s => logDeriv (LFunction χ) s - 1 / s

/-- If `L(s, χ) = s E(s)` near `0`, with `E` analytic and nonvanishing at `0`, then
`L'/L(s, χ) - 1/s → E'(0)/E(0)` as `s → 0`, `s ≠ 0`. -/
theorem tendsto_logDeriv_LFunction_sub_one_div {χ : DirichletCharacter ℂ N} {E : ℂ → ℂ}
    (hE : AnalyticAt ℂ E 0) (hE0 : E 0 ≠ 0)
    (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), LFunction χ s = s * E s) :
    Tendsto (fun s => logDeriv (LFunction χ) s - 1 / s) (𝓝[≠] (0 : ℂ))
      (𝓝 (logDeriv E 0)) := by
  have hL := Complex.eventually_logDeriv_eq_of_eq_zpow_mul (f := LFunction χ) (k := 1) hE hE0
    (h.mono fun s hs => by rw [hs, sub_zero, zpow_one])
  have hc : ContinuousAt (logDeriv E) 0 :=
    (hE.deriv.continuousAt.div hE.continuousAt hE0 :
      ContinuousAt (fun s => deriv E s / E s) 0)
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hL] with s hs
  rw [hs]
  simp

/-- If `L(s, χ) = s E(s)` near `0`, with `E` analytic and nonvanishing at `0`, then
`b(χ) = E'(0)/E(0)`. -/
theorem logDerivConstAtZero_eq_logDeriv {χ : DirichletCharacter ℂ N} {E : ℂ → ℂ}
    (hE : AnalyticAt ℂ E 0) (hE0 : E 0 ≠ 0)
    (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), LFunction χ s = s * E s) :
    χ.logDerivConstAtZero = logDeriv E 0 :=
  (tendsto_logDeriv_LFunction_sub_one_div hE hE0 h).limUnder_eq

end LogDerivConst

end DirichletCharacter
