/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import MathlibExt.Analysis.Complex.VerticalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import MathlibExt.Analysis.Complex.TaylorRemainder
import MathlibExt.Analysis.Complex.VerticalIntegral.ContourShift
import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel
import MathlibExt.NumberTheory.ArithmeticFunction.DivisorBounds
import MathlibExt.NumberTheory.LSeries.Perron
import MathlibExt.NumberTheory.LSeries.PerronError
import MathlibExt.NumberTheory.LSeries.RamanujanSigma
import MathlibExt.NumberTheory.LSeries.RiemannZetaBounds

/-!
# The weighted second moment of the divisor function

Let `d(n) = σ₀(n)` be the number of divisors of `n`. Ramanujan's identity
`∑ d(n)² n^{-s} = ζ(s)⁴ / ζ(2s)` and Perron's formula with the weight `log³(x / n)` give,
after shifting the line of integration to `re s = 1 / 2`, an asymptotic expansion
`∑_{n ≤ x} d(n)² log³(x / n) = x P(log x) + O(√x)` with `P` a cubic polynomial whose leading
coefficient is `6 / π²`.

## Main statements

* `ArithmeticFunction.LSeriesSummable_sigma_zero_sq`: `∑ d(n)² n^{-s}` converges absolutely
  for `re s > 1`.
* `hasVerticalIntegral_riemannZeta_pow_four_div_riemannZeta_two_mul`: the Perron
  representation `(1 / 2πi) ∫_(4) ζ(s)⁴ / ζ(2s) · x^s / s⁴ ds = (∑_{n ≤ x} d(n)² log³(x/n)) / 6`.
* `one_div_four_le_norm_riemannZeta_of_two_le_re`: `‖ζ(w)‖ ≥ 1 / 4` for `re w ≥ 2`.
* `exists_norm_riemannZeta_pow_four_div_riemannZeta_two_mul_le`:
  `ζ(s)⁴ / ζ(2s) = O(|t|^{5/2})` on the strip `1 / 2 ≤ re s ≤ 4`, `|t| ≥ 1`.
* `ArithmeticFunction.exists_polynomial_degree_eq_three_sum_sigma_zero_sq_mul_log_pow_isBigO`:
  `∑_{n ≤ x} d(n)² log³(x / n) = x P(log x) + O(√x)` with `deg P = 3`.
-/

@[expose] public section

open Asymptotics Complex Filter
open scoped Real Topology

namespace ArithmeticFunction

/-- The Dirichlet series `∑ d(n)² n^{-s}` converges absolutely for `re s > 1`. -/
theorem LSeriesSummable_sigma_zero_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((sigma 0 n : ℕ) : ℂ) ^ 2) s := by
  obtain ⟨C, -, hC⟩ := exists_sigma_zero_le_mul_rpow (ε := (s.re - 1) / 4) (by linarith)
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1 + (s.re - 1) / 2) (by linarith)
    ⟨C ^ 2, fun n _ => ?_⟩
  rw [norm_pow, Complex.norm_natCast, show 1 + (s.re - 1) / 2 - 1 = (s.re - 1) / 4 * 2 by ring,
    Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two, ← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hC n) 2

end ArithmeticFunction

/-- **Perron representation of `∑ d(n)² log³(x / n)`.** For `x > 0`,
`(1 / 2πi) ∫_(4) ζ(s)⁴ / ζ(2s) · x^s / s⁴ ds = (∑_{n ≤ x} d(n)² log³(x / n)) / 6`. -/
theorem hasVerticalIntegral_riemannZeta_pow_four_div_riemannZeta_two_mul {x : ℝ} (hx : 0 < x) :
    HasVerticalIntegral 4
      (fun s : ℂ => riemannZeta s ^ 4 / riemannZeta (2 * s) * (x : ℂ) ^ s / s ^ 4)
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) ^ 2 * (Real.log (x / n) : ℂ) ^ 3) / 6) := by
  have hsum : LSeriesSummable (fun n => ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) ^ 2)
      ((4 : ℝ) : ℂ) := ArithmeticFunction.LSeriesSummable_sigma_zero_sq (by norm_num)
  have h := hsum.hasVerticalIntegral_LSeries_mul_cpow_div_pow_succ (k := 3) (by norm_num)
    (by norm_num) hx
  have hfac : ((Nat.factorial 3 : ℕ) : ℂ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  refine h.congr_line fun t => ?_
  rw [ArithmeticFunction.LSeries_sigma_zero_sq (by simp)]

/-- For every `w` with `2 ≤ re w`, `1 / 4 ≤ ‖ζ (w)‖`: the Dirichlet series gives
`‖ζ (w) - 1‖ ≤ ∑_{n ≥ 2} n ^ (-2) = π² / 6 - 1`. -/
theorem one_div_four_le_norm_riemannZeta_of_two_le_re {w : ℂ} (hw : 2 ≤ w.re) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta w‖ := by
  have hw1 : 1 < w.re := by linarith
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) :=
    Complex.summable_one_div_nat_cpow.mpr hw1
  have hfirst : ∑ i ∈ Finset.range 2, 1 / ((i : ℕ) : ℂ) ^ w = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [Complex.zero_cpow hw0]
  have hzw : riemannZeta w = 1 + ∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℂ) ^ w := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw1, ← Summable.sum_add_tsum_nat_add 2 hsummable, hfirst]
  -- the real comparison series `∑_{i ≥ 0} (i + 2) ^ (-2)`, summing to `π² / 6 - 1`
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have hshift : Summable (fun i : ℕ => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff 2).mpr hsum2
  have htail : ∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℝ) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
    have h := hsum2.sum_add_tsum_nat_add 2
    rw [hasSum_zeta_two.tsum_eq] at h
    have h2 : ∑ i ∈ Finset.range 2, 1 / ((i : ℕ) : ℝ) ^ 2 = 1 := by
      norm_num [Finset.sum_range_succ]
    rw [h2] at h
    linarith
  have hzeta2 : HasSum (fun i : ℕ => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    rw [← htail]
    exact hshift.hasSum
  have hbound : ‖∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℂ) ^ w‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    refine tsum_of_norm_bounded hzeta2 fun i => ?_
    have hn1 : (1 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      push_cast
      linarith
    have hmono : ((i + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) ^ w.re :=
      Real.rpow_le_rpow_of_exponent_le hn1 hw
    have hnat : ((i + 2 : ℕ) : ℝ) ^ (2 : ℝ) = ((i + 2 : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega) w]
    refine one_div_le_one_div_of_le ?_ ?_
    · have : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) := by linarith
      positivity
    · rw [← hnat]; exact hmono
  have hpi : Real.pi ^ 2 / 6 - 1 < 0.655 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hrev : (1 : ℝ) - ‖∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℂ) ^ w‖
      ≤ ‖1 + ∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℂ) ^ w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-∑' i : ℕ, 1 / (((i + 2 : ℕ)) : ℂ) ^ w)
    simpa [sub_neg_eq_add] using h
  rw [hzw]
  linarith

/-- A real polynomial of degree `3` with prescribed values `∑_{j < 4} b j * y ^ j / j !`. -/
private theorem exists_polynomial_degree_eq_three_eval_eq {b : ℕ → ℝ} (hb : b 3 ≠ 0) :
    ∃ P : Polynomial ℝ, P.degree = 3 ∧
      ∀ y : ℝ, P.eval y = ∑ j ∈ Finset.range 4, b j * y ^ j / (j.factorial : ℝ) := by
  refine ⟨∑ j ∈ Finset.range 4, Polynomial.C (b j / (j.factorial : ℝ)) * Polynomial.X ^ j,
    ?_, fun y => ?_⟩
  · refine Polynomial.degree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · refine Polynomial.degree_sum_le _ _ |>.trans (Finset.sup_le fun j hj => ?_)
      exact (Polynomial.degree_C_mul_X_pow_le j _).trans
        (by exact_mod_cast Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    · simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
      norm_num
      exact hb
  · rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

/-- **The growth of `ζ⁴ (s) / ζ (2 s)` on a strip.** There is a constant `C > 0` such that for
every `s` with `1 / 2 ≤ re s ≤ 4` and `|im s| ≥ 1`,
`‖ζ (s) ^ 4 / ζ (2 s)‖ ≤ C * |im s| ^ (5 / 2)`.

The numerator is controlled by the convexity bound, the denominator by `1 / 4 ≤ ‖ζ‖` on
`re ≥ 2` and by the zero-free region `‖ζ (σ + i t)‖ ≫ log ^ (-7) |t|` otherwise. -/
theorem exists_norm_riemannZeta_pow_four_div_riemannZeta_two_mul_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
      ‖riemannZeta s ^ 4 / riemannZeta (2 * s)‖ ≤ C * |s.im| ^ (5 / 2 : ℝ) := by
  obtain ⟨C₁, T₀, hC₁0, hT₀0, hconv⟩ := exists_pos_norm_riemannZeta_le_mul_abs_im_rpow_half
  obtain ⟨c₁, c₂, hc₁0, hc₂0, hzf⟩ := exists_pos_div_log_pow_seven_lt_norm_riemannZeta
  -- ## `ζ` is bounded on the compact low-ordinate box `1 / 2 ≤ σ ≤ 4`, `1 ≤ |t| ≤ T₀`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 4 → 1 ≤ |z.im| → |z.im| ≤ T₀ →
      ‖riemannZeta z‖ ≤ B := by
    have hclosed : IsClosed {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 4 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T₀} := by
      have hEq : {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 4 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T₀} =
          {z : ℂ | 1 / 2 ≤ z.re} ∩ ({z : ℂ | z.re ≤ 4} ∩
            ({z : ℂ | 1 ≤ |z.im|} ∩ {z : ℂ | |z.im| ≤ T₀})) := rfl
      rw [hEq]
      exact (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im.abs).inter
            (isClosed_le Complex.continuous_im.abs continuous_const)))
    have hsub : {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 4 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T₀} ⊆
        Metric.closedBall (0 : ℂ) (4 + T₀) := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hz
      have hre : |z.re| ≤ 4 := abs_le.mpr ⟨by linarith, h2⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hz' := Complex.norm_le_abs_re_add_abs_im z
      linarith
    have hcompact : IsCompact {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 4 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T₀} :=
      (isCompact_closedBall (0 : ℂ) (4 + T₀)).of_isClosed_subset hclosed hsub
    have hcont : ContinuousOn riemannZeta
        {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 4 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T₀} := by
      intro z hz
      have hz1 : z ≠ 1 := by
        intro h
        have h3 := hz.2.2.1
        rw [h] at h3
        norm_num at h3
      exact (differentiableAt_riemannZeta hz1).continuousAt.continuousWithinAt
    obtain ⟨B, hBd⟩ := hcompact.exists_bound_of_continuousOn hcont
    exact ⟨B, fun z h1 h2 h3 h4 => hBd z ⟨h1, h2, h3, h4⟩⟩
  -- ## One constant `A` dominating both the convexity constant and the compact bound
  obtain ⟨A, hA0, hAC₁, hAB⟩ : ∃ A : ℝ, 0 < A ∧ C₁ ≤ A ∧ B ≤ A :=
    ⟨C₁ + |B| + 1, by linarith [abs_nonneg B], by linarith [abs_nonneg B],
      by linarith [le_abs_self B]⟩
  -- ## The numerator: `‖ζ (s)‖ ≤ A |t| ^ (1 / 2)` on the whole strip
  have hnum : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 4 → 1 ≤ |z.im| →
      ‖riemannZeta z‖ ≤ A * |z.im| ^ (1 / 2 : ℝ) := by
    intro z h1 h2 h3
    have hrp1 : (1 : ℝ) ≤ |z.im| ^ (1 / 2 : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num) h3 (by norm_num : (0:ℝ) ≤ 1/2)
    rcases le_or_gt T₀ |z.im| with h | h
    · calc ‖riemannZeta z‖ ≤ C₁ * |z.im| ^ (1 / 2 : ℝ) := hconv z h1 h
        _ ≤ A * |z.im| ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hAC₁ (by linarith)
    · calc ‖riemannZeta z‖ ≤ B := hB z h1 h2 h3 h.le
        _ ≤ A := hAB
        _ = A * 1 := (mul_one A).symm
        _ ≤ A * |z.im| ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hrp1 hA0.le
  -- ## `log ^ 7 (max (e ^ 2) (2 t)) ≤ 17 ^ 7 * t ^ (1 / 2)`, which is what absorbs the log
  have hgrowth : ∀ t : ℝ, 1 ≤ t →
      Real.log (max (Real.exp 2) (2 * t)) ^ 7 ≤ 17 ^ 7 * t ^ (1 / 2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hu1 : (1 : ℝ) ≤ t ^ (1 / 14 : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num) ht (by norm_num : (0:ℝ) ≤ 1/14)
    have hlogu : Real.log (t ^ (1 / 14 : ℝ)) ≤ t ^ (1 / 14 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have hlogt : Real.log t = 14 * Real.log (t ^ (1 / 14 : ℝ)) := by
      rw [Real.log_rpow ht0]; ring
    have he8 : Real.exp 2 ≤ 8 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have hTle : max (Real.exp 2) (2 * t) ≤ 16 * t := max_le (by linarith) (by linarith)
    have hT0 : (0 : ℝ) < max (Real.exp 2) (2 * t) :=
      lt_of_lt_of_le (Real.exp_pos 2) (le_max_left _ _)
    have hlog16 : Real.log 16 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h2 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have hlogT : Real.log (max (Real.exp 2) (2 * t)) ≤ 3 + Real.log t := by
      calc Real.log (max (Real.exp 2) (2 * t)) ≤ Real.log (16 * t) := Real.log_le_log hT0 hTle
        _ = Real.log 16 + Real.log t := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 3 + Real.log t := by linarith
    have hlogTnn : 0 ≤ Real.log (max (Real.exp 2) (2 * t)) := by
      have h := Real.log_le_log (Real.exp_pos 2) (le_max_left (Real.exp 2) (2 * t))
      rw [Real.log_exp] at h
      linarith
    have hbnd : Real.log (max (Real.exp 2) (2 * t)) ≤ 17 * t ^ (1 / 14 : ℝ) := by
      rw [hlogt] at hlogT
      linarith
    have hu7 : (t ^ (1 / 14 : ℝ)) ^ 7 = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (t ^ (1 / 14 : ℝ)) 7, ← Real.rpow_mul ht0.le]
      norm_num
    calc Real.log (max (Real.exp 2) (2 * t)) ^ 7 ≤ (17 * t ^ (1 / 14 : ℝ)) ^ 7 :=
          pow_le_pow_left₀ hlogTnn hbnd 7
      _ = 17 ^ 7 * (t ^ (1 / 14 : ℝ)) ^ 7 := by ring
      _ = 17 ^ 7 * t ^ (1 / 2 : ℝ) := by rw [hu7]
  -- ## The constant
  obtain ⟨C, hC0, hCge, hCc₂⟩ : ∃ C : ℝ, 0 < C ∧ 4 * A ^ 4 ≤ C ∧ A ^ 4 * 17 ^ 7 ≤ C * c₂ := by
    have hc₂ne : c₂ ≠ 0 := ne_of_gt hc₂0
    have hA4 : (0 : ℝ) < A ^ 4 := pow_pos hA0 4
    have hq : (0 : ℝ) < A ^ 4 * 17 ^ 7 / c₂ := div_pos (mul_pos hA4 (by norm_num)) hc₂0
    refine ⟨4 * A ^ 4 + A ^ 4 * 17 ^ 7 / c₂, by linarith, by linarith, ?_⟩
    have hEq : (4 * A ^ 4 + A ^ 4 * 17 ^ 7 / c₂) * c₂ = 4 * A ^ 4 * c₂ + A ^ 4 * 17 ^ 7 := by
      field_simp
    have hpos : (0 : ℝ) < 4 * A ^ 4 * c₂ := mul_pos (by linarith) hc₂0
    rw [hEq]
    linarith
  refine ⟨C, hC0, ?_⟩
  intro s h1 h2 h3
  -- ## Abbreviations
  have hre2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have him2 : (2 * s).im = 2 * s.im := by simp [Complex.mul_im]
  have ht0 : (0 : ℝ) < |s.im| := by linarith
  have hp1 : (1 : ℝ) ≤ |s.im| ^ (1 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num) h3 (by norm_num : (0:ℝ) ≤ 1/2)
  have hp4 : (0 : ℝ) ≤ (|s.im| ^ (1 / 2 : ℝ)) ^ 4 := by positivity
  have hp5 : |s.im| ^ (5 / 2 : ℝ) = (|s.im| ^ (1 / 2 : ℝ)) ^ 5 := by
    rw [← Real.rpow_natCast (|s.im| ^ (1 / 2 : ℝ)) 5, ← Real.rpow_mul ht0.le]
    norm_num
  have hzs : ‖riemannZeta s‖ ≤ A * |s.im| ^ (1 / 2 : ℝ) := hnum s h1 h2 h3
  -- ## The shared final step, parametrised by whichever lower bound the branch supplies
  have key : ∀ D : ℝ, 0 < D → D ≤ ‖riemannZeta (2 * s)‖ →
      A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 ≤ C * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 * D →
      ‖riemannZeta s ^ 4 / riemannZeta (2 * s)‖ ≤ C * |s.im| ^ (5 / 2 : ℝ) := by
    intro D hD0 hDle hcalc
    have hzpos : 0 < ‖riemannZeta (2 * s)‖ := lt_of_lt_of_le hD0 hDle
    rw [norm_div, norm_pow, hp5, div_le_iff₀ hzpos]
    calc ‖riemannZeta s‖ ^ 4 ≤ (A * |s.im| ^ (1 / 2 : ℝ)) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) hzs 4
      _ = A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 := by ring
      _ ≤ C * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 * D := hcalc
      _ ≤ C * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 * ‖riemannZeta (2 * s)‖ :=
          mul_le_mul_of_nonneg_left hDle (mul_nonneg hC0.le (by positivity))
  rcases le_or_gt 1 s.re with hσ | hσ
  -- ### `Re (2 s) ≥ 2`: `‖ζ (2 s)‖ ≥ 1 / 4`
  · refine key (1 / 4) (by norm_num)
      (one_div_four_le_norm_riemannZeta_of_two_le_re (by rw [hre2]; linarith)) ?_
    have hstep : C * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 * (1 / 4)
        = C * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 * |s.im| ^ (1 / 2 : ℝ) / 4 := by ring
    rw [hstep, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    calc A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 * 4 = 4 * A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 := by
          ring
      _ ≤ C * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 := mul_le_mul_of_nonneg_right hCge hp4
      _ = C * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 * 1 := (mul_one _).symm
      _ ≤ C * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 * |s.im| ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hp1 (mul_nonneg hC0.le hp4)
  -- ### `Re (2 s) < 2`: the zero-free region gives `‖ζ (2 s)‖ > c₂ / log ^ 7 T`
  · have hTmax : Real.exp 2 ≤ max (Real.exp 2) (2 * |s.im|) := le_max_left _ _
    have hL2 : (2 : ℝ) ≤ Real.log (max (Real.exp 2) (2 * |s.im|)) := by
      have h := Real.log_le_log (Real.exp_pos 2) hTmax
      rwa [Real.log_exp] at h
    have hL0 : (0 : ℝ) < Real.log (max (Real.exp 2) (2 * |s.im|)) := by linarith
    have hL7 : (0 : ℝ) < Real.log (max (Real.exp 2) (2 * |s.im|)) ^ 7 := by positivity
    have himabs : |(2 * s).im| = 2 * |s.im| := by
      rw [him2, abs_mul]
      norm_num
    have hlow : c₂ / Real.log (max (Real.exp 2) (2 * |s.im|)) ^ 7 ≤ ‖riemannZeta (2 * s)‖ :=
      le_of_lt (hzf _ hTmax (2 * s) (by rw [himabs]; linarith)
        (by rw [himabs]; exact le_max_right _ _)
        (by rw [hre2]
            have hcc : (0:ℝ) < c₁ / Real.log (max (Real.exp 2) (2 * |s.im|)) ^ 9 := by
              positivity
            linarith)
        (by rw [hre2]; linarith))
    refine key _ (by positivity) hlow ?_
    have hgr := hgrowth |s.im| h3
    rw [mul_div_assoc', le_div_iff₀ hL7]
    calc A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4
          * Real.log (max (Real.exp 2) (2 * |s.im|)) ^ 7
        ≤ A ^ 4 * (|s.im| ^ (1 / 2 : ℝ)) ^ 4 * (17 ^ 7 * |s.im| ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hgr (by positivity)
      _ = A ^ 4 * 17 ^ 7 * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 := by ring
      _ ≤ C * c₂ * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 :=
          mul_le_mul_of_nonneg_right hCc₂ (by positivity)
      _ = C * (|s.im| ^ (1 / 2 : ℝ)) ^ 5 * c₂ := by ring

namespace ArithmeticFunction

/-- **The weighted second moment of the divisor function.** There is a real polynomial `P` of
degree `3` with
`∑_{n ≤ x} d (n) ^ 2 * log (x / n) ^ 3 = x * P (log x) + O (x ^ (1 / 2))`. -/
theorem exists_polynomial_degree_eq_three_sum_sigma_zero_sq_mul_log_pow_isBigO :
    ∃ P : Polynomial ℝ, P.degree = 3 ∧
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3)
          - x * P.eval (Real.log x)) =O[atTop] fun x : ℝ => Real.sqrt x := by
  -- ## The pole-free numerator `G (s) = (s - 1) ^ 4 ζ (s) ^ 4 / (ζ (2 s) s ^ 4)`
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun s => riemannZeta₁ s ^ 4 * (2 * s - 1) /
      (riemannZeta₁ (2 * s) * s ^ 4) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = {s : ℂ | 1 / 2 ≤ s.re} := ⟨_, rfl⟩
  have hz1ne : ∀ w : ℂ, 1 ≤ w.re → riemannZeta₁ w ≠ 0 := by
    intro w hw
    rcases eq_or_ne w 1 with rfl | hw1
    · simp
    · have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw
      rw [riemannZeta_eq_inv_sub_mul hw1] at hz
      exact fun h => hz (by rw [h, mul_zero])
  have hGd : ∀ s ∈ U, DifferentiableAt ℂ G s := by
    intro s hs
    rw [hUdef] at hs
    have hs' : 1 / 2 ≤ s.re := hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs'
    have h2 : riemannZeta₁ (2 * s) ≠ 0 := hz1ne _ (by simp; linarith)
    rw [hGdef]
    have hA : DifferentiableAt ℂ (fun s : ℂ => riemannZeta₁ s ^ 4 * (2 * s - 1)) s :=
      ((differentiable_riemannZeta₁ s).pow 4).mul (by fun_prop)
    have hB : DifferentiableAt ℂ (fun s : ℂ => riemannZeta₁ (2 * s) * s ^ 4) s :=
      ((differentiable_riemannZeta₁.comp (differentiable_id.const_mul (2 : ℂ))) s).mul
        (by fun_prop)
    exact hA.div hB (mul_ne_zero h2 (pow_ne_zero 4 hs0))
  have hU1 : U ∈ nhds (1 : ℂ) := by
    refine Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) fun s hs => ?_
    rw [hUdef]
    exact le_of_lt (show (1 / 2 : ℝ) < s.re from hs)
  obtain ⟨b, g, hg, hGg⟩ := DifferentiableOn.exists_eq_sum_add_pow_mul
    (fun s hs => (hGd s hs).differentiableWithinAt) hU1 4
  -- ## The leading coefficient `b 0 = G 1 = 1 / ζ (2) = 6 / π ^ 2`
  have hb0 : b 0 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have h1 := hGg 1 (by rw [hUdef]; norm_num)
    have hz2 : riemannZeta₁ 2 = (Real.pi : ℂ) ^ 2 / 6 := by
      have h := riemannZeta_eq_inv_sub_mul (s := 2) (by norm_num)
      rw [riemannZeta_two] at h
      norm_num at h
      exact h.symm
    simp only [hGdef, riemannZeta₁_one, one_pow, mul_one, one_mul, hz2, sub_self,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one, mul_zero,
      add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h1
    rw [← h1]
    push_cast
    ring
  -- ## The analytic core: `‖S / 6 - ∑ b j * x (log x) ^ (3 - j) / (3 - j)!‖ ≤ K √x`
  have hmain : ∃ K : ℝ, ∀ x : ℝ, 1 < x →
      ‖(((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3) / 6 : ℝ) : ℂ)
        - ∑ j ∈ Finset.range 4,
            b j * ((x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ) : ℝ) : ℂ)‖
        ≤ K * Real.sqrt x := by
    obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_pow_four_div_riemannZeta_two_mul_le
    -- `G` is bounded on the low segment of the line `Re s = 1 / 2`
    obtain ⟨BG, hBG⟩ : ∃ BG : ℝ, ∀ t : ℝ, |t| ≤ 1 →
        ‖G (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ BG := by
      have hcont : ContinuousOn (fun t : ℝ => G (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          (Set.Icc (-1) 1) := by
        intro t _
        exact ((hGd _ (by rw [hUdef]; simp)).continuousAt.comp
          (by fun_prop :
            Continuous fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).continuousAt
          ).continuousWithinAt
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      exact ⟨B, fun t ht => hB t (Set.mem_Icc.mpr (abs_le.mp ht))⟩
    -- ## Three real-variable facts about `u ^ (5 / 2) / u ^ 4` and `(1 + u) ^ (-3 / 2)`
    have hquarter : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-2 : ℝ) ≤ -(3 / 2))
      have h2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
      linarith
    have r1 : ∀ u : ℝ, 1 ≤ u → u ^ (5 / 2 : ℝ) / u ^ 4 ≤ 1 / u := by
      intro u hu
      have hu0 : 0 < u := by linarith
      have h := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (5 / 2 : ℝ) ≤ 3)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      calc u ^ (5 / 2 : ℝ) / u ^ 4 ≤ u ^ 3 / u ^ 4 := div_le_div_of_nonneg_right h (by positivity)
        _ = 1 / u := by field_simp
    have r2 : ∀ u : ℝ, 1 ≤ u → u ^ (5 / 2 : ℝ) / u ^ 4 ≤ 4 * (1 + u) ^ (-(3 / 2 : ℝ)) := by
      intro u hu
      have hu0 : 0 < u := by linarith
      have e : u ^ (5 / 2 : ℝ) / u ^ 4 = u ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast u 4, ← Real.rpow_sub hu0]
        norm_num
      have h1 : (2 * u) ^ (-(3 / 2 : ℝ)) ≤ (1 + u) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      rw [Real.mul_rpow (by norm_num) hu0.le] at h1
      have hp : 0 < u ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
      rw [e]
      nlinarith [hquarter, h1, hp]
    have r3 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 1 / 4 ≤ (1 + u) ^ (-(3 / 2 : ℝ)) := by
      intro u hu0 hu1
      exact hquarter.trans (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num))
    obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∫ t : ℝ, (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
    have hJint : MeasureTheory.Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
      integrable_one_add_norm (by norm_num)
    refine ⟨(64 * max BG 0 + 4 * C) * J / (2 * Real.pi), fun x hx => ?_⟩
    have hx0 : (0 : ℝ) < x := by linarith
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    -- ## The integrand, its principal part and its holomorphic part
    obtain ⟨Fp, hFp⟩ : ∃ Fp : ℂ → ℂ, Fp = fun s => G s * (x : ℂ) ^ s / (s - 1) ^ 4 :=
      ⟨_, rfl⟩
    obtain ⟨Kk, hKk⟩ : ∃ Kk : ℕ → ℂ → ℂ, Kk = fun k s => (x : ℂ) ^ s / (s - 1) ^ (k + 1) :=
      ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, Q = fun s => ∑ j ∈ Finset.range 4, b j * Kk (3 - j) s :=
      ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ, D = fun s => g s * (x : ℂ) ^ s := ⟨_, rfl⟩
    have hDeq : ∀ s ∈ U, s ≠ 1 → D s = Fp s - Q s := by
      intro s hs hs1
      have h := hGg s hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      simp only [hD, hFp, hQ, hKk, Finset.sum_range_succ, Finset.sum_range_zero] at h ⊢
      norm_num at h ⊢
      rw [h]
      field_simp
      ring
    have hFeq : ∀ s : ℂ, s ≠ 1 → 2 * s ≠ 1 →
        riemannZeta s ^ 4 / riemannZeta (2 * s) * (x : ℂ) ^ s / s ^ 4 = Fp s := by
      intro s h1 h2
      rw [riemannZeta_eq_inv_sub_mul h1, riemannZeta_eq_inv_sub_mul h2, hFp, hGdef]
      simp only [div_eq_mul_inv, mul_inv, inv_inv, inv_pow, mul_pow]
      ring
    -- ## Regularity
    have hcpow : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      fun s => differentiableAt_id.const_cpow (Or.inl hxC)
    have hKc : ∀ k : ℕ, ∀ s : ℂ, s ≠ 1 → ContinuousAt (Kk k) s := by
      intro k s hs
      rw [hKk]
      change ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / (s - 1) ^ (k + 1)) s
      have hden : DifferentiableAt ℂ (fun s : ℂ => (s - 1) ^ (k + 1)) s := by fun_prop
      exact ((hcpow s).div hden (pow_ne_zero _ (sub_ne_zero.mpr hs))).continuousAt
    have hQc : ∀ s : ℂ, s ≠ 1 → ContinuousAt Q s := by
      intro s hs
      rw [hQ]
      exact tendsto_finsetSum _ fun j _ => continuousAt_const.mul (hKc _ s hs)
    have hFpc : ∀ s ∈ U, s ≠ 1 → ContinuousAt Fp s := by
      intro s hs hs1
      rw [hFp]
      have hden : DifferentiableAt ℂ (fun s : ℂ => (s - 1) ^ 4) s := by fun_prop
      exact (((hGd s hs).mul (hcpow s)).div hden
        (pow_ne_zero _ (sub_ne_zero.mpr hs1))).continuousAt
    have hDd : DifferentiableOn ℂ D U := by
      rw [hD]
      exact hg.mul fun s _ => (hcpow s).differentiableWithinAt
    -- ## Each side integral of `D` splits as the `Fp` part minus the `Q` part
    have hside : ∀ (a c : ℝ) (φ : ℝ → ℂ), ContinuousOn φ (Set.uIcc a c) →
        (∀ v ∈ Set.uIcc a c, φ v ∈ U) → (∀ v ∈ Set.uIcc a c, φ v ≠ 1) →
        (∫ v in a..c, D (φ v)) = (∫ v in a..c, Fp (φ v)) - ∫ v in a..c, Q (φ v) := by
      intro a c φ hφ hmem hne
      have hF : IntervalIntegrable (fun v => Fp (φ v)) MeasureTheory.volume a c :=
        (ContinuousOn.comp (t := {s | s ∈ U ∧ s ≠ 1})
          (fun s hs => (hFpc s hs.1 hs.2).continuousWithinAt) hφ
          (fun v hv => ⟨hmem v hv, hne v hv⟩)).intervalIntegrable
      have hQi : IntervalIntegrable (fun v => Q (φ v)) MeasureTheory.volume a c :=
        (ContinuousOn.comp (t := {s | s ≠ 1})
          (fun s hs => (hQc s hs).continuousWithinAt) hφ
          (fun v hv => hne v hv)).intervalIntegrable
      rw [← intervalIntegral.integral_sub hF hQi]
      exact intervalIntegral.integral_congr fun v hv => hDeq _ (hmem v hv) (hne v hv)
    -- ## On a vertical line the `Q` part splits into the four kernels
    have hKline : ∀ k : ℕ, ∀ c : ℝ, c ≠ 1 →
        Continuous fun t : ℝ => Kk k ((c : ℂ) + (t : ℂ) * Complex.I) := by
      intro k c hc
      refine continuous_iff_continuousAt.mpr fun t => ?_
      refine (hKc k _ fun h => hc ?_).comp (by fun_prop : Continuous
        fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I).continuousAt
      have := congrArg Complex.re h
      simpa using this
    -- ## Cauchy–Goursat for the holomorphic part on `[1/2, 4] × [-T, T]`
    have hGour : ∀ T : ℝ, 0 < T →
        (∫ σ in (1 / 2 : ℝ)..4, D ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - (∫ σ in (1 / 2 : ℝ)..4, D ((σ : ℂ) + (T : ℂ) * Complex.I))
          + Complex.I • (∫ y in (-T)..T, D (((4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          - Complex.I • (∫ y in (-T)..T, D (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
      intro T hT
      refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn D ⟨1 / 2, -T⟩ ⟨4, T⟩
        (hDd.mono fun s hs => ?_)
      obtain ⟨h1, -⟩ := hs
      change s.re ∈ Set.uIcc (1 / 2 : ℝ) 4 at h1
      rw [Set.uIcc_of_le (by norm_num)] at h1
      rw [hUdef]
      exact h1.1
    -- ## Size of `Fp` on the strip away from the real axis
    have hFpb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
        ‖Fp s‖ ≤ C * x ^ s.re * (|s.im| ^ (5 / 2 : ℝ) / |s.im| ^ 4) := by
      intro s h1 h2 h3
      have hs1 : s ≠ 1 := by
        rintro rfl
        norm_num at h3
      have hs2 : 2 * s ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, one_im, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or] at this
        rw [this] at h3
        norm_num at h3
      have hu : (0 : ℝ) < |s.im| := by linarith
      rw [← hFeq s hs1 hs2, norm_div, norm_mul, norm_pow,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hn : |s.im| ^ 4 ≤ ‖s‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm s) 4
      have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg hx0.le _
      calc ‖riemannZeta s ^ 4 / riemannZeta (2 * s)‖ * x ^ s.re / ‖s‖ ^ 4
          ≤ C * |s.im| ^ (5 / 2 : ℝ) * x ^ s.re / |s.im| ^ 4 :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (hC s h1 h2 h3) hxp)
              (by positivity) hn
        _ = C * x ^ s.re * (|s.im| ^ (5 / 2 : ℝ) / |s.im| ^ 4) := by ring
    -- ## The horizontal sides vanish as `T → ∞`
    have hhor : ∀ (f : ℂ → ℂ) (M : ℝ), (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
        ‖f s‖ ≤ M / |s.im|) →
        Tendsto (fun T : ℝ => (∫ σ in (1 / 2 : ℝ)..4, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - ∫ σ in (1 / 2 : ℝ)..4, f ((σ : ℂ) + (T : ℂ) * Complex.I)) atTop (nhds 0) :=
      fun f M hf => tendsto_horizontal_sides_of_norm_le_div_abs_im (by norm_num) hf
    have hHf := hhor Fp (C * x ^ (4 : ℝ)) fun s h1 h2 h3 => by
      have hu : (0 : ℝ) < |s.im| := by linarith
      calc ‖Fp s‖ ≤ C * x ^ s.re * (|s.im| ^ (5 / 2 : ℝ) / |s.im| ^ 4) := hFpb s h1 h2 h3
        _ ≤ C * x ^ (4 : ℝ) * (1 / |s.im|) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx.le h2) hC0.le) (r1 _ h3)
            (by positivity) (by positivity)
        _ = C * x ^ (4 : ℝ) / |s.im| := by ring
    have hKb : ∀ k : ℕ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
        ‖Kk k s‖ ≤ x ^ (4 : ℝ) / |s.im| := by
      intro k s h1 h2 h3
      have hu : (0 : ℝ) < |s.im| := by linarith
      have hn : |s.im| ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        simpa using this
      have hn' : |s.im| ≤ ‖s - 1‖ ^ (k + 1) := by
        calc |s.im| ≤ |s.im| ^ (k + 1) := le_self_pow₀ h3 (by omega)
          _ ≤ ‖s - 1‖ ^ (k + 1) := pow_le_pow_left₀ hu.le hn _
      rw [hKk]
      simp only
      rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hx.le h2) hu hn'
    have hHq := hhor Q ((∑ j ∈ Finset.range 4, ‖b j‖) * x ^ (4 : ℝ)) fun s h1 h2 h3 => by
      rw [hQ]
      simp only
      calc ‖∑ j ∈ Finset.range 4, b j * Kk (3 - j) s‖
          ≤ ∑ j ∈ Finset.range 4, ‖b j‖ * (x ^ (4 : ℝ) / |s.im|) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hKb _ s h1 h2 h3) (norm_nonneg _)
        _ = (∑ j ∈ Finset.range 4, ‖b j‖) * x ^ (4 : ℝ) / |s.im| := by
            rw [← Finset.sum_mul]; ring
    -- ## On `Re s = 1 / 2` the kernels reflect to Perron kernels with base `1 / x < 1`
    have hq : ∀ k : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (k + 1)) atTop (nhds 0) := by
      intro k
      rcases k with _ | k
      · have hδ : PerronKernel.perronStep x⁻¹ = 0 :=
          PerronKernel.perronStep_of_lt_one (inv_lt_one_of_one_lt₀ hx)
        have hL : 0 < |Real.log x⁻¹| := abs_pos.mpr (Real.log_neg (by positivity)
          (inv_lt_one_of_one_lt₀ hx)).ne
        simp only [zero_add, pow_one]
        refine squeeze_zero_norm'
          (a := fun T => x⁻¹ ^ (1 / 2 : ℝ) / |Real.log x⁻¹| / T) ?_
          (tendsto_const_nhds.div_atTop tendsto_id)
        filter_upwards [eventually_gt_atTop 0] with T hT
        have h := PerronKernel.norm_truncated_sub_perronStep_lt (x := x⁻¹) (c := 1 / 2)
          (R := T) (by positivity) (inv_lt_one_of_one_lt₀ hx).ne (by norm_num) hT
        rw [hδ, Complex.ofReal_zero, sub_zero] at h
        refine h.le.trans ?_
        calc x⁻¹ ^ (1 / 2 : ℝ) * min 1 (1 / (T * |Real.log x⁻¹|))
            ≤ x⁻¹ ^ (1 / 2 : ℝ) * (1 / (T * |Real.log x⁻¹|)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
          _ = x⁻¹ ^ (1 / 2 : ℝ) / |Real.log x⁻¹| / T := by ring
      · exact hasVerticalIntegral_cpow_div_pow_succ_of_le_one (k := k + 1) (by omega)
          (by norm_num) (by positivity) (inv_le_one_of_one_le₀ hx.le)
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]
      exact hpi.ne
    have hrefl : ∀ (k : ℕ) (T : ℝ),
        (∫ t in (-T)..T, Kk k (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          = (x : ℂ) * (-1) ^ (k + 1) * ∫ t in (-T)..T,
            ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (k + 1) := by
      intro k T
      have hpt : ∀ t : ℝ, Kk k (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          = (x : ℂ) * (-1) ^ (k + 1) * (fun t : ℝ =>
            ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (k + 1)) (-t) := by
        intro t
        simp only
        set w : ℂ := ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I with hw
        have hw1 : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1 = -w := by
          rw [hw]; push_cast; ring
        have e : (x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = x * ((x : ℂ) ^ w)⁻¹ := by
          have h := Complex.cpow_add (x := (x : ℂ)) 1 (-w) hxC
          rw [Complex.cpow_one, Complex.cpow_neg] at h
          rw [← h]
          congr 1
          rw [hw]; push_cast; ring
        have hinv : ((x⁻¹ : ℝ) : ℂ) ^ w = ((x : ℂ) ^ w)⁻¹ := by
          rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg]
        have hm : ((-1 : ℂ) ^ (k + 1))⁻¹ = (-1) ^ (k + 1) := by
          rw [← inv_pow, inv_neg, inv_one]
        rw [hKk]
        simp only
        rw [hw1, neg_pow, e, hinv, div_eq_mul_inv, mul_inv, hm]
        ring
      rw [intervalIntegral.integral_congr fun t _ => hpt t, intervalIntegral.integral_const_mul]
      congr 1
      have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t : ℝ =>
        ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (k + 1))
      rw [neg_neg] at h
      exact h
    have hKhalf : ∀ k : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        Kk k (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
      intro k
      have h := (hq k).const_mul ((x : ℂ) * (-1) ^ (k + 1))
      rw [mul_zero] at h
      refine h.congr fun T => ?_
      rw [hrefl, Complex.real_smul, Complex.real_smul]
      ring
    -- ## On `Re s = 4`: Perron for `Fp`, the shifted pole kernel for each `Kk`
    have hL4 : Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        Fp (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop
        (nhds (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3) / 6 : ℝ) : ℂ))
        := by
      have h := hasVerticalIntegral_riemannZeta_pow_four_div_riemannZeta_two_mul hx0
      unfold HasVerticalIntegral at h
      have hv : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) ^ 2 * (Real.log (x / n) : ℂ) ^ 3) / 6
          = (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3) / 6 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hv] at h
      refine h.congr fun T => ?_
      congr 1
      refine intervalIntegral.integral_congr fun t _ => hFeq _ (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h
        norm_num at this
      · have := congrArg Complex.re h
        norm_num at this
    have hM4 : ∀ j : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        Kk (3 - j) (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop
        (nhds ((x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ) : ℝ) : ℂ)) := by
      intro j
      have h := hasVerticalIntegral_cpow_div_sub_one_pow_succ (k := 3 - j) hx
        (c := 4) (by norm_num)
      have hv : (x : ℂ) * (Real.log x : ℂ) ^ (3 - j) / ((3 - j).factorial : ℂ)
          = ((x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hv] at h
      rw [hKk]
      exact h
    have hQ4 : HasVerticalIntegral 4 Q (∑ j ∈ Finset.range 4,
        b j * ((x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ) : ℝ) : ℂ)) := by
      rw [hQ]
      exact HasVerticalIntegral.finset_sum (Finset.range 4) (f := fun j s => b j * Kk (3 - j) s)
        (fun j _ => HasVerticalIntegral.const_mul (hM4 j) (b j))
        fun j _ R => ((hKline (3 - j) 4 (by norm_num)).const_mul (b j)).intervalIntegrable _ _
    have hQh : HasVerticalIntegral (1 / 2) Q 0 := by
      have h := HasVerticalIntegral.finset_sum (Finset.range 4) (c := 1 / 2)
        (f := fun j s => b j * Kk (3 - j) s) (v := fun _ => 0)
        (fun j _ => by simpa using HasVerticalIntegral.const_mul (hKhalf (3 - j)) (b j))
        fun j _ R => ((hKline (3 - j) (1 / 2) (by norm_num)).const_mul (b j)).intervalIntegrable _ _
      rw [hQ]
      simpa using h
    -- ## The rectangle identity, rewritten side by side from `D` to `Fp - Q`
    have hmemU : ∀ s : ℂ, 1 / 2 ≤ s.re → s ∈ U := fun s h => by rw [hUdef]; exact h
    have hclaim : ∀ T : ℝ, 1 ≤ T →
        (1 / (2 * Real.pi)) • (∫ t in (-T)..T, Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          = (1 / (2 * Real.pi)) • (∫ t in (-T)..T, Fp (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            - (1 / (2 * Real.pi)) • (∫ t in (-T)..T, Q (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            + (1 / (2 * Real.pi)) • (∫ t in (-T)..T, Q (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            - ((1 / (2 * Real.pi) : ℝ) : ℂ) * Complex.I *
              (((∫ σ in (1 / 2 : ℝ)..4, Fp ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
                - ∫ σ in (1 / 2 : ℝ)..4, Fp ((σ : ℂ) + (T : ℂ) * Complex.I))
              - ((∫ σ in (1 / 2 : ℝ)..4, Q ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
                - ∫ σ in (1 / 2 : ℝ)..4, Q ((σ : ℂ) + (T : ℂ) * Complex.I))) := by
      intro T hT
      have G0 := hGour T (by linarith)
      have hre : ∀ v ∈ Set.uIcc (1 / 2 : ℝ) 4, 1 / 2 ≤ v := fun v hv => by
        rw [Set.uIcc_of_le (by norm_num)] at hv; exact hv.1
      have e1 := hside (1 / 2) 4 (fun σ : ℝ => (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (by fun_prop) (fun v hv => hmemU _ (by simpa using hre v hv))
        (fun v _ h => by
          have := congrArg Complex.im h
          simp at this
          linarith)
      have e2 := hside (1 / 2) 4 (fun σ : ℝ => (σ : ℂ) + (T : ℂ) * Complex.I)
        (by fun_prop) (fun v hv => hmemU _ (by simpa using hre v hv))
        (fun v _ h => by
          have := congrArg Complex.im h
          simp at this
          linarith)
      have e3 := hside (-T) T (fun y : ℝ => ((4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        (by fun_prop) (fun v _ => hmemU _ (by norm_num))
        (fun v _ h => by
          have := congrArg Complex.re h
          norm_num at this)
      have e4 := hside (-T) T (fun y : ℝ => ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        (by fun_prop) (fun v _ => hmemU _ (by norm_num))
        (fun v _ h => by
          have := congrArg Complex.re h
          norm_num at this)
      rw [e1, e2, e3, e4] at G0
      simp only [Complex.real_smul, smul_eq_mul] at G0 ⊢
      set A1 := ∫ t in (-T)..T, Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      set A4 := ∫ t in (-T)..T, Fp (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      set B1 := ∫ t in (-T)..T, Q (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      set B4 := ∫ t in (-T)..T, Q (((4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      set r : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
      linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) (Complex.I * r) * G0
    -- ## Hence the left-line integral of `Fp` converges to `S / 6 - main term`
    have hlim := (((hL4.sub hQ4).add hQh).sub
      ((tendsto_const_nhds (x := ((1 / (2 * Real.pi) : ℝ) : ℂ) * Complex.I)).mul
        (hHf.sub hHq))).congr' ((eventually_ge_atTop 1).mono fun T hT => (hclaim T hT).symm)
    simp only [add_zero, sub_zero, mul_zero] at hlim
    -- ## The left line: `‖Fp (1/2 + i t)‖ ≤ √x · B (1 + |t|) ^ (-3/2)`, uniformly in `x`
    have hM0 : (0 : ℝ) ≤ max BG 0 := le_max_right _ _
    have hB0 : (0 : ℝ) ≤ 64 * max BG 0 + 4 * C := by positivity
    have hpt : ∀ t : ℝ, ‖Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.sqrt x * ((64 * max BG 0 + 4 * C) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) := by
      intro t
      have hφ0 : (0 : ℝ) ≤ (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by positivity
      have hsq : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
      rw [Real.norm_eq_abs]
      rw [Real.norm_eq_abs] at hφ0
      by_cases ht : |t| ≤ 1
      · have hφ := r3 |t| (abs_nonneg t) ht
        have hn : 1 / 2 ≤ ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1‖ := by
          have := Complex.abs_re_le_norm (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1)
          norm_num at this ⊢
          linarith
        have hG := (hBG t ht).trans (le_max_left BG 0)
        rw [hFp]
        simp only
        rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
        rw [hre, ← Real.sqrt_eq_rpow]
        calc ‖G (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * Real.sqrt x
              / ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1‖ ^ 4
            ≤ max BG 0 * Real.sqrt x / (1 / 2) ^ 4 :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hG hsq) (by norm_num)
                (pow_le_pow_left₀ (by norm_num) hn 4)
          _ ≤ Real.sqrt x * ((64 * max BG 0 + 4 * C) * (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
              have h1 := mul_nonneg (mul_nonneg hsq hM0) (sub_nonneg.mpr hφ)
              have h2 := mul_nonneg (mul_nonneg hsq hC0.le) hφ0
              norm_num
              nlinarith [h1, h2]
      · rw [not_le] at ht
        have him : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        have hre : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
        have h := hFpb (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (by rw [hre])
          (by rw [hre]; norm_num)
          (by rw [him]; exact ht.le)
        rw [hre, him, ← Real.sqrt_eq_rpow] at h
        have h2 := r2 |t| ht.le
        have h3 := mul_nonneg (mul_nonneg hsq hM0) hφ0
        refine h.trans ?_
        calc C * Real.sqrt x * (|t| ^ (5 / 2 : ℝ) / |t| ^ 4)
            ≤ C * Real.sqrt x * (4 * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ Real.sqrt x * ((64 * max BG 0 + 4 * C) * (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
              nlinarith [h3]
    have hLb : ∀ T : ℝ, 0 ≤ T →
        ‖(1 / (2 * Real.pi)) • ∫ t in (-T)..T, Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (64 * max BG 0 + 4 * C) * J / (2 * Real.pi) * Real.sqrt x := by
      intro T hT
      have hint : IntervalIntegrable (fun t : ℝ => Real.sqrt x *
          ((64 * max BG 0 + 4 * C) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)))) MeasureTheory.volume (-T) T :=
        ((hJint.const_mul _).const_mul _).intervalIntegrable
      have h1 := intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall fun t _ => hpt t) hint
      have h2 : (∫ t in (-T)..T, Real.sqrt x *
          ((64 * max BG 0 + 4 * C) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))))
          ≤ Real.sqrt x * ((64 * max BG 0 + 4 * C) * J) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hB0) (Real.sqrt_nonneg x)
        rw [intervalIntegral.integral_of_le (by linarith), hJ]
        exact MeasureTheory.setIntegral_le_integral hJint
          (Filter.Eventually.of_forall fun t => by positivity)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc 1 / (2 * Real.pi) * ‖∫ t in (-T)..T, Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ 1 / (2 * Real.pi) * (Real.sqrt x * ((64 * max BG 0 + 4 * C) * J)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = (64 * max BG 0 + 4 * C) * J / (2 * Real.pi) * Real.sqrt x := by ring
    exact le_of_tendsto hlim.norm ((eventually_ge_atTop 0).mono fun T hT => hLb T hT)
  -- ## Taking real parts
  obtain ⟨K, hK⟩ := hmain
  obtain ⟨P, hP3, hPev⟩ := exists_polynomial_degree_eq_three_eval_eq
    (b := fun k => 6 * (b (3 - k)).re) (by
      simp only [Nat.sub_self, hb0, Complex.ofReal_re]
      positivity)
  refine ⟨P, hP3, IsBigO.of_bound (6 * K) ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  have h := hK x hx
  set S : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 * Real.log (x / n) ^ 3 with hS
  set w : ℂ := ((S / 6 : ℝ) : ℂ) - ∑ j ∈ Finset.range 4,
    b j * ((x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ) : ℝ) : ℂ) with hw
  have hre : w.re = S / 6 - ∑ j ∈ Finset.range 4,
      (b j).re * (x * Real.log x ^ (3 - j) / ((3 - j).factorial : ℝ)) := by
    simp only [hw, Complex.sub_re, Complex.ofReal_re, Complex.re_sum, Complex.re_mul_ofReal]
  have heq : S - x * P.eval (Real.log x) = 6 * w.re := by
    rw [hPev, hre]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    ring
  have hwn := Complex.abs_re_le_norm w
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
  norm_num
  linarith

end ArithmeticFunction
