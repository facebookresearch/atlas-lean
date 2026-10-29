/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Contour estimates for the explicit formulas

The explicit formulas for `ψ(x)` and for `ψ(x, χ)` integrate `F(s) = -L'/L(s) x^s / s` around a
rectangle `[-U, c] × [-T, T]` and compare the zero sum `∑_{|γ| < T} x^ρ/ρ` at two heights. This
file contains the estimates that do not depend on the `L`-function:

* the horizontal sides: if `‖F(σ ± iT)‖ ≤ (a - bσ) x^σ / T`, then the side contributes at most
  `x^c (a / log x + b / log² x) / T`;
* moving the truncation height of `∑_{|γ| < T} x^ρ/ρ` over points with `Re ρ ≤ 1`;
* the sum over the trivial zeros `a - 2m`, `m ≥ 1`.

## Main statements

* `norm_intervalIntegral_le_of_norm_le_sub_mul_rpow`: the bound for a horizontal side.
* `norm_tsum_ite_cpow_div_sub_tsum_ite_cpow_div_le`: moving the truncation height.
* `tendsto_sum_cpow_sub_two_mul_div_two_mul_sub`: `∑_{m=1}^{M} x^{a-2m}/(2m-a)` converges.
-/

@[expose] public section

open Filter Topology

/-- **A horizontal side of the contour.** For `x > 1`, if `‖f σ‖ ≤ (a - bσ) x^σ / T` on
`(-U, c]`, with `b, c ≥ 0` and `a + bU ≥ 0`, then
`‖∫_{-U}^{c} f‖ ≤ x^c (a / log x + b / log² x) / T`. -/
theorem norm_intervalIntegral_le_of_norm_le_sub_mul_rpow {x : ℝ} (hx : 1 < x) {T a b c U : ℝ}
    (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 ≤ c) (hUc : -U ≤ c) (hab : 0 ≤ a + b * U) {f : ℝ → ℂ}
    (hf : ∀ σ ∈ Set.Ioc (-U) c, ‖f σ‖ ≤ (a - b * σ) * x ^ σ / T) :
    ‖∫ σ in (-U)..c, f σ‖ ≤ x ^ c * (a / Real.log x + b / Real.log x ^ 2) / T := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  set g : ℝ → ℝ := fun σ => (a - b * σ) * x ^ σ / T with hg
  set Φ : ℝ → ℝ := fun σ => x ^ σ * ((a - b * σ) / Real.log x + b / Real.log x ^ 2) / T
    with hΦ
  have hderiv : ∀ σ : ℝ, HasDerivAt Φ (g σ) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => x ^ σ) (x ^ σ * Real.log x) σ :=
      (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => (a - b * σ) / Real.log x + b / Real.log x ^ 2)
        (-b / Real.log x) σ := by
      have := (((hasDerivAt_id σ).const_mul b).const_sub a).div_const (Real.log x)
      simpa using this.add_const (b / Real.log x ^ 2)
    refine ((h1.mul h2).div_const T).congr_deriv ?_
    change _ = (a - b * σ) * x ^ σ / T
    field_simp
    ring
  have hgc : Continuous g := by
    have : Continuous (fun σ : ℝ => x ^ σ) :=
      continuous_const.rpow continuous_id (fun _ => Or.inl hx0.ne')
    simp only [hg]
    fun_prop
  have hint : ∫ σ in (-U)..c, g σ = Φ c - Φ (-U) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
      (hgc.intervalIntegrable _ _)
  have hΦa : 0 ≤ Φ (-U) := by
    simp only [hΦ]
    have : 0 ≤ a - b * -U := by linarith
    positivity
  have hΦc : Φ c ≤ x ^ c * (a / Real.log x + b / Real.log x ^ 2) / T := by
    simp only [hΦ]
    have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
    gcongr
    linarith [mul_nonneg hb hc]
  have hmain := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hUc
    (Eventually.of_forall (fun σ hσ => hf σ hσ)) (hgc.intervalIntegrable _ _)
  rw [hint] at hmain
  linarith

/-- **Moving the truncation height of a zero sum.** Let `z` be a family of points with
`Re z n ≤ 1`, and `x > 1`. If only finitely many `n` have `|Im z n| < max R T`, and every finite
set of indices with `min R T ≤ |Im z n| < max R T` has at most `B` elements, then the truncated
sums `∑_{|Im z n| < R} x^{z n}/z n` and `∑_{|Im z n| < T} x^{z n}/z n` differ by at most
`B x / min R T`. -/
theorem norm_tsum_ite_cpow_div_sub_tsum_ite_cpow_div_le {ι : Type*} (z : ι → ℂ)
    (hre : ∀ n, (z n).re ≤ 1) {x : ℝ} (hx : 1 < x) {R T : ℝ} (hRT : 0 < min R T)
    (hfin : {n | |(z n).im| < max R T}.Finite) {B : ℝ}
    (hB : ∀ F : Finset ι, (∀ n ∈ F, min R T ≤ |(z n).im| ∧ |(z n).im| < max R T) →
      (F.card : ℝ) ≤ B) :
    ‖(∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0)) -
        ∑' n, (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0)‖ ≤ B * (x / min R T) := by
  classical
  have hx0 : 0 < x := by linarith
  set NF := hfin.toFinset with hNF
  have hsupp : ∀ V : ℝ, V ≤ max R T →
      ∑' n, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) =
        ∑ n ∈ NF, (if |(z n).im| < V then (x : ℂ) ^ z n / z n else 0) := by
    intro V hV
    refine tsum_eq_sum fun n hn => ite_eq_right ?_
    intro h
    apply hn
    rw [hNF, Set.Finite.mem_toFinset]
    exact lt_of_lt_of_le h hV
  rw [hsupp R (le_max_left _ _), hsupp T (le_max_right _ _), ← Finset.sum_sub_distrib]
  set d : ι → ℂ := fun n => (if |(z n).im| < R then (x : ℂ) ^ z n / z n else 0) -
    (if |(z n).im| < T then (x : ℂ) ^ z n / z n else 0) with hd
  have hdz : ∀ n, d n ≠ 0 → min R T ≤ |(z n).im| ∧ |(z n).im| < max R T := by
    intro n hn
    by_contra hc
    apply hn
    simp only [hd]
    rcases not_and_or.mp hc with h | h
    · push Not at h
      rw [ite_eq_left (lt_of_lt_of_le h (min_le_left _ _)),
        ite_eq_left (lt_of_lt_of_le h (min_le_right _ _)), sub_self]
    · push Not at h
      rw [ite_eq_right (not_lt.mpr ((le_max_left _ _).trans h)),
        ite_eq_right (not_lt.mpr ((le_max_right _ _).trans h)), sub_self]
  have hdnorm : ∀ n, ‖d n‖ ≤ x / min R T := by
    intro n
    by_cases hn : d n = 0
    · rw [hn, norm_zero]; exact div_nonneg hx0.le hRT.le
    obtain ⟨h1, -⟩ := hdz n hn
    have hzn : min R T ≤ ‖z n‖ := h1.trans (Complex.abs_im_le_norm _)
    have hpow : ‖(x : ℂ) ^ z n‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      calc x ^ (z n).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (hre n)
        _ = x := Real.rpow_one x
    have hval : ‖(x : ℂ) ^ z n / z n‖ ≤ x / min R T := by
      rw [norm_div]
      exact div_le_div₀ hx0.le hpow hRT hzn
    simp only [hd] at hn ⊢
    split_ifs at hn ⊢
    · simp at hn
    · rwa [sub_zero]
    · rwa [zero_sub, norm_neg]
    · simp at hn
  set W : Finset ι := NF.filter (fun n => d n ≠ 0) with hW
  have hsum_eq : ∑ n ∈ NF, d n = ∑ n ∈ W, d n := by
    rw [hW, Finset.sum_filter_ne_zero]
  have hWcard : (W.card : ℝ) ≤ B := hB W fun n hn => hdz n (Finset.mem_filter.mp hn).2
  rw [hsum_eq]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => hdnorm n).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hWcard (div_nonneg hx0.le hRT.le)

/-- **The trivial zeros in the explicit formulas.** For `x > 1` and `a ≤ 1`, the partial sums
`∑_{m=1}^{M} x^{a-2m}/(2m - a)` converge to `∑_{m ≥ 0} x^{a-2(m+1)}/(2(m+1) - a)`. -/
theorem tendsto_sum_cpow_sub_two_mul_div_two_mul_sub {x a : ℝ} (hx : 1 < x) (ha1 : a ≤ 1) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
        (x : ℂ) ^ ((a : ℂ) - 2 * m) / (2 * m - (a : ℂ))) atTop
      (𝓝 (∑' m : ℕ, (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) / (2 * ((m : ℂ) + 1) - a))) := by
  have hx0 : 0 < x := by linarith
  set g : ℕ → ℂ := fun m => (x : ℂ) ^ ((a : ℂ) - 2 * ((m : ℂ) + 1)) / (2 * ((m : ℂ) + 1) - a)
    with hg
  have hr0 : 0 ≤ x ^ (-2 : ℝ) := by positivity
  have hr1 : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hbound : ∀ m : ℕ, ‖g m‖ ≤ (x ^ (-2 : ℝ)) ^ m := by
    intro m
    have hden : 1 ≤ ‖(2 * ((m : ℂ) + 1) - a)‖ := by
      have h := Complex.re_le_norm (2 * ((m : ℂ) + 1) - a)
      have : (2 * ((m : ℂ) + 1) - a).re = 2 * ((m : ℝ) + 1) - a := by simp
      rw [this] at h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [hg]
    simp only
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : ((a : ℂ) - 2 * ((m : ℂ) + 1)).re = a - 2 * ((m : ℝ) + 1) := by simp
    rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have h1 : x ^ (a - 2 * ((m : ℝ) + 1)) ≤ x ^ ((-2 : ℝ) * m) :=
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    calc x ^ (a - 2 * ((m : ℝ) + 1)) / ‖(2 * ((m : ℂ) + 1) - a)‖
        ≤ x ^ (a - 2 * ((m : ℝ) + 1)) := div_le_self (by positivity) hden
      _ ≤ x ^ ((-2 : ℝ) * m) := h1
  have hsum : Summable g :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1) hbound
  have ht := hsum.hasSum.tendsto_sum_nat
  refine ht.congr fun M => ?_
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    simp only [hg]
    push_cast
    ring_nf
