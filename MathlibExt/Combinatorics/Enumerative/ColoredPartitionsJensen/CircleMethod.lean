/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`PartitionsJensen/CircleMethod.lean`
(ChironTheCentaur/rh-lab-partitions-jensen, commit 57beb8dbff7b84e125931fe2e53080f325f4f108):
Copyright (c) 2026 Sky (GitHub: ChironTheCentaur). All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sky (GitHub: ChironTheCentaur)
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.EtaTransform
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# coefficients of `F(q)^r` and the minor arc

`F = partGen` (see `EtaTransform`). Here:

* `coef r n` (`= C_r(n)`): the Taylor coefficients of `F(q)^r` at `0`.
* `hasSum_coef`: `F(q)^r = ∑ₙ C_r(n) qⁿ` on `‖q‖ < 1`.
* `coef_eq_integral`: the Cauchy formula on the circle `|q| = e^{−y}`, any `y > 0`:
  `C_r(n) = (2π)⁻¹ ∫_{−π}^{π} F(e^{−(y+iθ)})^r e^{n(y+iθ)} dθ`.
* `norm_partGen_le`: `‖F(q)‖ ≤ ‖F(‖q‖)‖ · exp(−(‖q‖/(1−‖q‖) − Re(q/(1−q))))` on `‖q‖ < 1`
  (the `m = 1` Lambert term of `log F`; no complex logarithm of `F` is taken).
* `minorArc_saving`: for `q = e^{−(y+iθ)}`, `0 < y ≤ 1/2`, `y ≤ |θ| ≤ π`, the saving is `≥ 1/(8y)`.
* `minorArc`, `minorArc_pow`: `‖F(e^{−(y+iθ)})^r‖ ≤ F(e^{−y})^r e^{−r/(8y)}` on that range.
-/

noncomputable section

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

open Complex Filter Topology Metric
open scoped Real NNReal

/-! ### Analyticity and coefficients -/

lemma tendsto_eulerP {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) atTop (𝓝 (eulerP q)) := by
  have hmul : Multipliable fun n : ℕ ↦ 1 + -q ^ (n + 1) :=
    multipliable_one_add_of_summable (summable_norm_pow_succ hq)
  simpa [eulerP, sub_eq_add_neg] using hmul.hasProd.tendsto_prod_nat

lemma differentiableOn_partGen_pow (r : ℕ) :
    DifferentiableOn ℂ (fun q ↦ partGen q ^ r) (ball (0 : ℂ) 1) := by
  have h : DifferentiableOn ℂ eulerP (ball (0 : ℂ) 1) :=
      ModularForm.differentiableOn_tprod_one_sub_pow
  refine (h.inv fun q hq ↦ eulerP_ne_zero ?_).pow r
  simpa using hq

lemma hasFPowerSeriesOnBall_partGen_pow (r : ℕ) {R : ℝ≥0} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall (fun q ↦ partGen q ^ r)
      (cauchyPowerSeries (fun q ↦ partGen q ^ r) 0 R) 0 R :=
  ((differentiableOn_partGen_pow r).mono (closedBall_subset_ball hR1)).hasFPowerSeriesOnBall hR0

lemma cauchyPowerSeries_partGen_pow (r : ℕ) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    cauchyPowerSeries (fun q ↦ partGen q ^ r) 0 R =
      cauchyPowerSeries (fun q ↦ partGen q ^ r) 0 (1 / 2) := by
  have h1 := (hasFPowerSeriesOnBall_partGen_pow r (R := ⟨R, hR0.le⟩) (NNReal.coe_pos.1 hR0)
    hR1).hasFPowerSeriesAt
  have h2 := (hasFPowerSeriesOnBall_partGen_pow r (R := ⟨1 / 2, by norm_num⟩)
    (NNReal.coe_pos.1 (by change (0 : ℝ) < 1 / 2; norm_num))
    (by change (1 / 2 : ℝ) < 1; norm_num)).hasFPowerSeriesAt
  exact h1.eq_formalMultilinearSeries h2

/-- `C_r(n)`: the `n`-th Taylor coefficient of `F(q)^r` at `q = 0`. -/
def coef (r n : ℕ) : ℂ := (cauchyPowerSeries (fun q ↦ partGen q ^ r) 0 (1 / 2)).coeff n

/- **Power series.** `F(q)^r = ∑ₙ C_r(n) qⁿ` for `‖q‖ < 1`. -/
private theorem hasSum_coef (r : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n ↦ coef r n * q ^ n) (partGen q ^ r) := by
  obtain ⟨R, hqR, hR1⟩ := exists_between hq
  have hR0 : 0 < R := (norm_nonneg q).trans_lt hqR
  have h := (hasFPowerSeriesOnBall_partGen_pow r (R := ⟨R, hR0.le⟩) (NNReal.coe_pos.1 hR0)
    hR1).hasSum (y := q) (by
      rw [mem_eball_zero_iff]
      exact ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 (show (‖q‖₊ : ℝ) < R from hqR)))
  change HasSum (fun n ↦ (cauchyPowerSeries (fun q ↦ partGen q ^ r) 0 R n) fun _ ↦ q)
    (partGen (0 + q) ^ r) at h
  rw [cauchyPowerSeries_partGen_pow r hR0 hR1] at h
  simpa [coef, FormalMultilinearSeries.apply_eq_pow_smul_coeff, mul_comm] using h

/-- The circle integrand `θ ↦ F(e^{−(y+iθ)})^r e^{n(y+iθ)}`. -/
def circleIntegrand (r n : ℕ) (y θ : ℝ) : ℂ :=
  partGen (cexp (-(y + θ * I))) ^ r * cexp (n * (y + θ * I))

lemma circleIntegrand_periodic (r n : ℕ) (y : ℝ) :
    Function.Periodic (circleIntegrand r n y) (2 * π) := by
  intro θ
  have h1 : cexp (-((y : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * I)) = cexp (-((y : ℂ) + (θ : ℂ) * I)) := by
    rw [show -((y : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * I) = -((y : ℂ) + (θ : ℂ) * I) + (-1 : ℤ) * (2 * π
        * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h2 : cexp ((n : ℂ) * ((y : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * I)) =
      cexp ((n : ℂ) * ((y : ℂ) + (θ : ℂ) * I)) := by
    rw [show (n : ℂ) * ((y : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * I) =
        (n : ℂ) * ((y : ℂ) + (θ : ℂ) * I) + ((n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [circleIntegrand, h1, h2]

/-- **Cauchy coefficient formula** on `|q| = e^{−y}`, any `y > 0`:
`C_r(n) = (2π)⁻¹ ∫_{−π}^{π} F(e^{−(y+iθ)})^r e^{n(y+iθ)} dθ`. -/
theorem coef_eq_integral (r n : ℕ) {y : ℝ} (hy : 0 < y) :
    coef r n = (2 * π)⁻¹ * ∫ θ in (-π)..π,
      partGen (cexp (-(y + θ * I))) ^ r * cexp (n * (y + θ * I)) := by
  set R : ℝ := Real.exp (-y) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  -- the `[0, 2π]` form
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 R) θ • ((1 : ℂ) / (circleMap 0 R θ - 0)) ^ n •
      (circleMap 0 R θ - 0)⁻¹ • partGen (circleMap 0 R θ) ^ r = I * circleIntegrand r n y (-θ) := by
    intro θ
    have hz : circleMap 0 R θ = cexp (-((y : ℂ) + ((-θ : ℝ) : ℂ) * I)) := by
      rw [circleMap, hR, ofReal_exp, zero_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hzi : (1 : ℂ) / cexp (-((y : ℂ) + ((-θ : ℝ) : ℂ) * I)) = cexp ((y : ℂ) + ((-θ : ℝ) : ℂ) *
        I) := by
      rw [one_div, ← Complex.exp_neg, neg_neg]
    rw [deriv_circleMap, hz, sub_zero, hzi, circleIntegrand, ← Complex.exp_nat_mul]
    have hne : cexp (-((y : ℂ) + ((-θ : ℝ) : ℂ) * I)) ≠ 0 := Complex.exp_ne_zero _
    simp only [smul_eq_mul]
    field_simp
  have h0 : coef r n = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, circleIntegrand r n y (-θ) := by
    have hint : (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 R) θ • ((1 : ℂ) / (circleMap 0 R θ -
        0)) ^ n •
        (circleMap 0 R θ - 0)⁻¹ • partGen (circleMap 0 R θ) ^ r) =
        ∫ θ in (0 : ℝ)..2 * π, I * circleIntegrand r n y (-θ) :=
      intervalIntegral.integral_congr (fun θ _ ↦ hpt θ)
    rw [coef, ← cauchyPowerSeries_partGen_pow r hR0 hR1, FormalMultilinearSeries.coeff,
      show (1 : Fin n → ℂ) = fun _ ↦ 1 from rfl, cauchyPowerSeries_apply, circleIntegral]
    rw [hint, intervalIntegral.integral_const_mul, smul_eq_mul]
    push_cast
    field_simp
  -- shift to `[−π, π]` and reflect
  have hneg : ∫ θ in (0 : ℝ)..2 * π, circleIntegrand r n y (-θ) =
      ∫ θ in (-(2 * π))..0, circleIntegrand r n y θ := by
    rw [intervalIntegral.integral_comp_neg (fun θ ↦ circleIntegrand r n y θ), neg_zero]
  have hshift := (circleIntegrand_periodic r n y).intervalIntegral_add_eq (-(2 * π)) (-π)
  rw [show -(2 * π) + 2 * π = 0 by ring, show -π + 2 * π = π by ring] at hshift
  rw [h0, hneg, hshift]
  rfl

/-! ### The minor arc -/

/- Per factor: `1 − ‖x‖ ≤ ‖1 − x‖ e^{−(‖x‖ − Re x)}` for `‖x‖ < 1`
(the first term of `−log(1−|x|) + log|1−x| = ∑ₖ (|x|ᵏ − Re xᵏ)/k`, all terms `≥ 0`). -/
private lemma one_sub_norm_le {x : ℂ} (hx : ‖x‖ < 1) :
    1 - ‖x‖ ≤ ‖1 - x‖ * Real.exp (-(‖x‖ - x.re)) := by
  have h1x : 1 - x ≠ 0 := by
    intro h
    have : x = 1 := by linear_combination -h
    simp [this] at hx
  have hpos : 0 < 1 - ‖x‖ := by linarith
  have hR := Real.hasSum_pow_div_log_of_abs_lt_one (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg
      _)])
  have hC := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hx)
  have hD := hR.sub hC
  have hre : ∀ k : ℕ, (x ^ (k + 1) / ((k : ℂ) + 1)).re = (x ^ (k + 1)).re / (k + 1) := by
    intro k
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
  have hterm : ∀ k : ℕ, 0 ≤ ‖x‖ ^ (k + 1) / (k + 1) - (x ^ (k + 1) / ((k : ℂ) + 1)).re := by
    intro k
    rw [hre, ← sub_div]
    apply div_nonneg _ (by positivity)
    have := re_le_norm (x ^ (k + 1))
    rw [norm_pow] at this
    linarith
  have hfirst := le_hasSum hD 0 (fun k _ ↦ hterm k)
  rw [hre 0] at hfirst
  simp only [zero_add, pow_one, Nat.cast_zero, div_one, neg_re, log_re] at hfirst
  calc 1 - ‖x‖ = Real.exp (Real.log (1 - ‖x‖)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log ‖1 - x‖ + -(‖x‖ - x.re)) := Real.exp_le_exp.2 (by linarith)
    _ = ‖1 - x‖ * Real.exp (-(‖x‖ - x.re)) := by
        rw [Real.exp_add, Real.exp_log (norm_pos_iff.2 h1x)]

/- **Lambert saving.** For `‖q‖ < 1`,
`‖F(q)‖ ≤ ‖F(‖q‖)‖ · exp(−(‖q‖/(1−‖q‖) − Re(q/(1−q))))`. -/
private theorem norm_partGen_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖partGen q‖ ≤ ‖partGen (‖q‖ : ℂ)‖ * Real.exp (-(‖q‖ / (1 - ‖q‖) - (q / (1 - q)).re)) := by
  set ρ := ‖q‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg q
  have hρq : ‖(ρ : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  set S := ρ / (1 - ρ) - (q / (1 - q)).re with hS
  -- partial sums of the saving
  have hsum : HasSum (fun i : ℕ ↦ ρ ^ (i + 1) - (q ^ (i + 1)).re) S := by
    have h1 : HasSum (fun i : ℕ ↦ ρ ^ (i + 1)) (ρ / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hq).mul_left ρ
      simpa [pow_succ', div_eq_mul_inv] using this
    have h2 : HasSum (fun i : ℕ ↦ q ^ (i + 1)) (q / (1 - q)) := by
      have := (hasSum_geometric_of_norm_lt_one hq).mul_left q
      simpa [pow_succ', div_eq_mul_inv] using this
    exact h1.sub (Complex.hasSum_re h2)
  have hfac : ∀ i : ℕ, ‖1 - (ρ : ℂ) ^ (i + 1)‖ ≤
      ‖1 - q ^ (i + 1)‖ * Real.exp (-(ρ ^ (i + 1) - (q ^ (i + 1)).re)) := by
    intro i
    have hn : ‖q ^ (i + 1)‖ = ρ ^ (i + 1) := by rw [norm_pow]
    have hlt : ‖q ^ (i + 1)‖ < 1 := by
      rw [hn]; exact pow_lt_one₀ hρ0 hq (Nat.succ_ne_zero i)
    have h := one_sub_norm_le hlt
    rw [hn] at h
    have hreal : ‖1 - (ρ : ℂ) ^ (i + 1)‖ = 1 - ρ ^ (i + 1) := by
      rw [show (1 : ℂ) - (ρ : ℂ) ^ (i + 1) = ((1 - ρ ^ (i + 1) : ℝ) : ℂ) by push_cast; ring,
        norm_real, Real.norm_eq_abs, abs_of_nonneg]
      have : ρ ^ (i + 1) < 1 := pow_lt_one₀ hρ0 hq (Nat.succ_ne_zero i)
      linarith
    rw [hreal]; exact h
  have hpart : ∀ N : ℕ, ‖∏ i ∈ Finset.range N, (1 - (ρ : ℂ) ^ (i + 1))‖ ≤
      ‖∏ i ∈ Finset.range N, (1 - q ^ (i + 1))‖ *
        Real.exp (-∑ i ∈ Finset.range N, (ρ ^ (i + 1) - (q ^ (i + 1)).re)) := by
    intro N
    rw [norm_prod, norm_prod, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hfac i)
  have hA := (continuous_norm.tendsto _).comp (tendsto_eulerP hρq)
  have hB := (continuous_norm.tendsto _).comp (tendsto_eulerP hq)
  have hE := (Real.continuous_exp.tendsto _).comp hsum.tendsto_sum_nat.neg
  have key : ‖eulerP (ρ : ℂ)‖ ≤ ‖eulerP q‖ * Real.exp (-S) :=
    le_of_tendsto_of_tendsto' hA (hB.mul hE) hpart
  have hq0 : 0 < ‖eulerP q‖ := norm_pos_iff.2 (eulerP_ne_zero hq)
  have hρ0' : 0 < ‖eulerP (ρ : ℂ)‖ := norm_pos_iff.2 (eulerP_ne_zero hρq)
  rw [partGen, partGen, norm_inv, norm_inv]
  have h1 : ‖eulerP q‖⁻¹ * ‖eulerP (ρ : ℂ)‖ ≤ Real.exp (-S) := by
    rw [inv_mul_le_iff₀ hq0]; exact key
  calc ‖eulerP q‖⁻¹ = (‖eulerP q‖⁻¹ * ‖eulerP (ρ : ℂ)‖) * ‖eulerP (ρ : ℂ)‖⁻¹ := by
        field_simp
    _ ≤ Real.exp (-S) * ‖eulerP (ρ : ℂ)‖⁻¹ := by gcongr
    _ = ‖eulerP (ρ : ℂ)‖⁻¹ * Real.exp (-S) := mul_comm _ _

/- The saving in closed form: for `q = e^{−(y+iθ)}`, `ρ = e^{−y}`, `c = cos θ`,
`ρ/(1−ρ) − Re(q/(1−q)) = ρ(1+ρ)(1−c) / ((1−ρ)((1−ρ)² + 2ρ(1−c)))`. -/
private lemma saving_eq {y θ : ℝ} (hy : 0 < y) :
    Real.exp (-y) / (1 - Real.exp (-y)) - (cexp (-(y + θ * I)) / (1 - cexp (-(y + θ * I)))).re =
      Real.exp (-y) * (1 + Real.exp (-y)) * (1 - Real.cos θ) /
        ((1 - Real.exp (-y)) * ((1 - Real.exp (-y)) ^ 2 + 2 * Real.exp (-y) * (1 - Real.cos θ)))
            := by
  set ρ := Real.exp (-y) with hρ
  set c := Real.cos θ with hc
  set s := Real.sin θ with hs
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.cos_le_one θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hq : cexp (-((y : ℂ) + (θ : ℂ) * I)) = ((ρ * c : ℝ) : ℂ) + ((-(ρ * s) : ℝ) : ℂ) * I := by
    rw [show -((y : ℂ) + (θ : ℂ) * I) = ((-y : ℝ) : ℂ) + ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, exp_mul_I]
    simp only [hρ, hc, hs, ofReal_mul, ofReal_neg, ofReal_exp, ofReal_cos, ofReal_sin,
        Complex.cos_neg,
      Complex.sin_neg]
    ring
  have hD : 0 < (1 - ρ) ^ 2 + 2 * ρ * (1 - c) := by
    have : 0 < (1 - ρ) ^ 2 := by nlinarith
    nlinarith
  rw [hq, div_re]
  simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, sub_im, one_im,
    add_im, mul_im, normSq_apply]
  have hN : (1 - (ρ * c + (-(ρ * s) * 0 - 0 * 1))) * (1 - (ρ * c + (-(ρ * s) * 0 - 0 * 1))) +
      (0 - (0 + (-(ρ * s) * 1 + 0 * 0))) * (0 - (0 + (-(ρ * s) * 1 + 0 * 0))) =
      (1 - ρ) ^ 2 + 2 * ρ * (1 - c) := by
    linear_combination ρ ^ 2 * hsc
  rw [hN]
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  field_simp
  linear_combination (ρ ^ 2 - ρ ^ 3) * hsc

/- **Minor-arc saving.** For `0 < y ≤ 1/2` and `y ≤ |θ| ≤ π`, with `q = e^{−(y+iθ)}`,
`ρ/(1−ρ) − Re(q/(1−q)) ≥ 1/(8y)`. -/
private theorem minorArc_saving {y θ : ℝ} (hy : 0 < y) (hy2 : y ≤ 1 / 2) (hθ1 : y ≤ |θ|)
    (hθ2 : |θ| ≤ π) :
    1 / (8 * y) ≤
      Real.exp (-y) / (1 - Real.exp (-y)) - (cexp (-(y + θ * I)) / (1 - cexp (-(y + θ * I)))).re
          := by
  rw [saving_eq hy]
  set ρ := Real.exp (-y) with hρ
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hρlow : 1 - y ≤ ρ := by linarith [Real.add_one_le_exp (-y)]
  have hρh : 1 / 2 ≤ ρ := by linarith
  set w := 1 - Real.cos θ with hw
  have hcos : Real.cos θ ≤ Real.cos y := by
    rw [← Real.cos_abs θ]; exact Real.cos_le_cos_of_nonneg_of_le_pi hy.le hθ2 hθ1
  have hb := Real.cos_bound (x := y) (by rw [abs_of_pos hy]; linarith)
  rw [abs_of_pos hy] at hb
  have hcy : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have := (abs_le.1 hb).2; linarith
  have hy4 : y ^ 4 * (5 / 96) ≤ y ^ 2 / 4 := by
    have : y ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg y]
  have hwlow : y ^ 2 / 4 ≤ w := by rw [hw]; linarith
  have ha0 : 0 < 1 - ρ := by linarith
  have hay : 1 - ρ ≤ y := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwlow
  have hD : 0 < (1 - ρ) * ((1 - ρ) ^ 2 + 2 * ρ * w) := by positivity
  rw [div_le_div_iff₀ (by positivity) hD]
  -- `(1−ρ)((1−ρ)² + 2ρw) ≤ y(y² + 2ρw) ≤ 8yρ(1+ρ)w`
  have h1 : (1 - ρ) * ((1 - ρ) ^ 2 + 2 * ρ * w) ≤ y * (y ^ 2 + 2 * ρ * w) := by
    have ha2 : (1 - ρ) ^ 2 ≤ y ^ 2 := by nlinarith
    have : 0 ≤ (1 - ρ) ^ 2 + 2 * ρ * w := by positivity
    calc (1 - ρ) * ((1 - ρ) ^ 2 + 2 * ρ * w) ≤ y * ((1 - ρ) ^ 2 + 2 * ρ * w) := by gcongr
      _ ≤ y * (y ^ 2 + 2 * ρ * w) := by gcongr
  have h2 : y * (y ^ 2 + 2 * ρ * w) ≤ 8 * y * (ρ * (1 + ρ) * w) := by
    have h34 : 3 / 4 ≤ ρ * (1 + ρ) := by nlinarith
    have : y ^ 2 + 2 * ρ * w ≤ 8 * (ρ * (1 + ρ) * w) := by
      nlinarith [mul_le_mul_of_nonneg_right h34 hw0.le, mul_le_mul_of_nonneg_right hρ1.le hw0.le]
    calc y * (y ^ 2 + 2 * ρ * w) ≤ y * (8 * (ρ * (1 + ρ) * w)) := by gcongr
      _ = 8 * y * (ρ * (1 + ρ) * w) := by ring
  nlinarith

lemma norm_exp_neg_y_add (y θ : ℝ) : ‖cexp (-((y : ℂ) + (θ : ℂ) * I))‖ = Real.exp (-y) := by
  rw [norm_exp]; simp

/- **Minor arc.** For `0 < y ≤ 1/2`, `y ≤ |θ| ≤ π`: `‖F(e^{−(y+iθ)})‖ ≤ ‖F(e^{−y})‖ e^{−1/(8y)}`.
-/
private theorem minorArc {y θ : ℝ} (hy : 0 < y) (hy2 : y ≤ 1 / 2) (hθ1 : y ≤ |θ|) (hθ2 : |θ| ≤ π) :
    ‖partGen (cexp (-(y + θ * I)))‖ ≤ ‖partGen (cexp (-(y : ℂ)))‖ * Real.exp (-(1 / (8 * y))) := by
  have hn := norm_exp_neg_y_add y θ
  have hq : ‖cexp (-((y : ℂ) + (θ : ℂ) * I))‖ < 1 := by
    rw [hn]; exact Real.exp_lt_one_iff.2 (by linarith)
  have h := norm_partGen_le hq
  rw [hn, ofReal_exp, ofReal_neg] at h
  refine h.trans ?_
  gcongr
  exact minorArc_saving hy hy2 hθ1 hθ2

/-- For `0 < y ≤ 1/2` and `y ≤ |θ| ≤ π`: `‖F(e^{−(y+iθ)})^r‖ ≤ ‖F(e^{−y})‖^r e^{−r/(8y)}`. -/
theorem minorArc_pow (r : ℕ) {y θ : ℝ} (hy : 0 < y) (hy2 : y ≤ 1 / 2) (hθ1 : y ≤ |θ|)
    (hθ2 : |θ| ≤ π) :
    ‖partGen (cexp (-(y + θ * I))) ^ r‖ ≤
      ‖partGen (cexp (-(y : ℂ)))‖ ^ r * Real.exp (-(r / (8 * y))) := by
  rw [norm_pow]
  calc ‖partGen (cexp (-(y + θ * I)))‖ ^ r
      ≤ (‖partGen (cexp (-(y : ℂ)))‖ * Real.exp (-(1 / (8 * y)))) ^ r := by
        gcongr; exact minorArc hy hy2 hθ1 hθ2
    _ = ‖partGen (cexp (-(y : ℂ)))‖ ^ r * Real.exp (-(r / (8 * y))) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

end

end MetaMathlibExt.ColoredPartitionsJensen
