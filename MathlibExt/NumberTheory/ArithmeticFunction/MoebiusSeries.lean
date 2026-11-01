/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues

/-!
# The Möbius series at integers `h ≥ 2`

For an integer `h ≥ 2` the real series `∑ μ(d) / d ^ h` converges absolutely and sums to
`1 / ζ(h)`. At `h = 2` this is `6 / π ^ 2`.

## Main statements

* `riemannZeta_natCast_eq_ofReal_tsum`: `ζ(h)` is the real `p`-series `∑ 1 / n ^ h`.
* `one_le_re_riemannZeta_natCast`: `1 ≤ ζ(h)` for `h ≥ 2`.
* `ArithmeticFunction.summable_moebius_div_pow`: `∑ μ(d) / d ^ h` converges.
* `ArithmeticFunction.tsum_moebius_div_pow`: `∑ μ(d) / d ^ h = 1 / ζ(h)`.
* `ArithmeticFunction.tsum_moebius_div_sq`: `∑ μ(d) / d ^ 2 = 6 / π ^ 2`.
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

/-- At an integer `h ≥ 2`, `riemannZeta h` is the cast of the real series `∑ 1 / n ^ h`. -/
theorem riemannZeta_natCast_eq_ofReal_tsum (h : ℕ) (hh : 2 ≤ h) :
    riemannZeta (h : ℂ) = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ h : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < h), Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]

/-- At an integer `h ≥ 2`, the real part of `riemannZeta h` is the real series
`∑ 1 / n ^ h`. -/
theorem re_riemannZeta_natCast (h : ℕ) (hh : 2 ≤ h) :
    (riemannZeta (h : ℂ)).re = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ h := by
  rw [riemannZeta_natCast_eq_ofReal_tsum h hh, Complex.ofReal_re]

/-- At an integer `h ≥ 2`, `1 ≤ ζ(h)`. -/
theorem one_le_re_riemannZeta_natCast (h : ℕ) (hh : 2 ≤ h) :
    1 ≤ (riemannZeta (h : ℂ)).re := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ h) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  rw [re_riemannZeta_natCast h hh]
  simpa using hsum.le_tsum 1 (fun j _ => by positivity)

namespace ArithmeticFunction

/-- The real Möbius series `∑ μ(d) / d ^ h` converges absolutely for `h ≥ 2`. -/
theorem summable_moebius_div_pow (h : ℕ) (hh : 2 ≤ h) :
    Summable (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ h) := by
  refine Summable.of_norm_bounded (Real.summable_one_div_nat_pow.mpr (by omega : 1 < h))
    fun d => ?_
  have hnn : (0 : ℝ) ≤ (d : ℝ) ^ h := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnn]
  gcongr
  exact_mod_cast abs_moebius_le_one

/-- `∑ μ(d) / d ^ h = 1 / ζ(h)` for every integer `h ≥ 2`. -/
theorem tsum_moebius_div_pow (h : ℕ) (hh : 2 ≤ h) :
    ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ h = 1 / (riemannZeta (h : ℂ)).re := by
  have hs : 1 < ((h : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < h)
  have hmul := LSeries_zeta_mul_Lseries_moebius (s := (h : ℂ)) hs
  rw [LSeries_zeta_eq_riemannZeta hs] at hmul
  have hcast : LSeries (fun n : ℕ => ((μ n : ℤ) : ℂ)) (h : ℂ)
      = ((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ h : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, zero_pow (by omega : h ≠ 0)]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast]
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
        Complex.ofReal_intCast]
  rw [hcast, riemannZeta_natCast_eq_ofReal_tsum h hh] at hmul
  have hprod : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ h) * (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ h) = 1 := by
    have h' := congrArg Complex.re hmul
    rw [← Complex.ofReal_mul, Complex.ofReal_re] at h'
    simpa using h'
  have hZ := one_le_re_riemannZeta_natCast h hh
  rw [re_riemannZeta_natCast h hh] at hZ ⊢
  rw [eq_div_iff (by positivity)]
  linarith

/-- `∑ μ(d) / d ^ 2 = 6 / π ^ 2`. -/
theorem tsum_moebius_div_sq : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = 6 / π ^ 2 := by
  rw [tsum_moebius_div_pow 2 le_rfl, re_riemannZeta_natCast 2 le_rfl, hasSum_zeta_two.tsum_eq]
  field_simp

end ArithmeticFunction
