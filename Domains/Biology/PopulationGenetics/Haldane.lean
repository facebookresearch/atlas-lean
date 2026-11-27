/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Haldane's survival probability of a beneficial mutation

A new mutant allele with selective advantage `s` leaves a Poisson(`1 + s`) number of copies in
the next generation (Haldane 1927). Its descendants form a Galton–Watson process, and the
mutant survives with probability `π(s) = 1 - q(s)`, where `q(s)` is the extinction probability.

## Main results

* `pgf_poissonMeasure`, `mean_poissonMeasure`: the Poisson(`r`) generating function is
  `exp (r (x - 1))` and its mean is `r`.
* `one_sub_survivalProb`: `1 - π(s) = exp (-(1 + s) π(s))` for `s ≥ -1`.
* `survivalProb_pos`, `survivalProb_lt_one`: a beneficial mutant (`s > 0`) survives with a
  probability strictly between `0` and `1`.
* `tendsto_survivalProb_div`: Haldane's approximation `π(s) ~ 2 s`, i.e. `π(s) / s → 2` as
  `s → 0⁺`.

## Conventions

`s` is the selective advantage per generation of a single mutant copy in the branching
approximation (mean offspring `1 + s`), not the scaled coefficient `σ = 2Ns` of diffusion
models. The limit is an exact `Tendsto` statement; no `O(s²)` remainder is claimed.

## References

* J. B. S. Haldane, *A mathematical theory of natural and artificial selection, part V:
  selection and mutation*, Proc. Camb. Phil. Soc. 23 (1927), 838–844.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer (1972), ch. I.
-/

@[expose] public section

open MeasureTheory Filter Topology Real ProbabilityTheory MathlibExt.Probability
open scoped NNReal ENNReal Nat

namespace MathlibExt.Biology.PopulationGenetics.Haldane

/-! ### Elementary bounds on `exp (-x)` -/

private lemma nonneg_of_deriv_nonneg (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, 0 ≤ x → 0 ≤ f' x)
    (hzero : f 0 = 0) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (show Differentiable ℝ f from fun y => (hf y).differentiableAt).continuous.continuousOn
    · exact (show Differentiable ℝ f from fun y => (hf y).differentiableAt).differentiableOn
    · intro y hy
      rw [(hf y).deriv]
      exact hf' y (Set.mem_Ici.mp (interior_subset hy))
  simpa [hzero] using hm (Set.mem_Ici.mpr le_rfl) hx hx

private lemma exp_neg_quadratic (x : ℝ) (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hd (y : ℝ) :
      HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y))
        (-1 + y + exp (-y)) y := by
    convert (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      ((hasDerivAt_id y).neg.exp) using 1
    · rfl
    · simp only [id_eq, Pi.neg_apply]
      ring
  have h := nonneg_of_deriv_nonneg _ _ hd (fun y _ => by
    have := Real.add_one_le_exp (-y)
    linarith) (by simp) x hx
  linarith

private lemma exp_neg_cubic (x : ℝ) (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 ≤ exp (-x) := by
  have hd (y : ℝ) :
      HasDerivAt (fun y : ℝ => exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6))
        (-exp (-y) + 1 - y + y ^ 2 / 2) y := by
    convert ((hasDerivAt_id y).neg.exp).sub
      ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        (((hasDerivAt_id y).pow 2).div_const 2)).sub
        (((hasDerivAt_id y).pow 3).div_const 6)) using 1
    · rfl
    · simp only [id_eq, Pi.neg_apply]
      ring
  have h := nonneg_of_deriv_nonneg _ _ hd (fun y hy => by
    have := exp_neg_quadratic y hy
    linarith) (by simp) x hx
  linarith

private lemma root_bounds (s q : ℝ) (hs : 0 < s) (hq : 0 < q)
    (heq : 1 - q = exp (-(1 + s) * q)) :
    s ≤ (1 + s) ^ 2 * q / 2 ∧
      (1 + s) ^ 2 * q / 2 * (1 - (1 + s) * q / 3) ≤ s := by
  have hu : 0 ≤ (1 + s) * q := by positivity
  have hquad := exp_neg_quadratic ((1 + s) * q) hu
  have hcubic := exp_neg_cubic ((1 + s) * q) hu
  rw [← neg_mul, ← heq] at hquad hcubic
  constructor
  · have hm : 0 ≤ q * ((1 + s) ^ 2 * q / 2 - s) := by
      nlinarith only [hquad]
    have := nonneg_of_mul_nonneg_right hm hq
    linarith
  · have hm : 0 ≤ q * (s - (1 + s) ^ 2 * q / 2 * (1 - (1 + s) * q / 3)) := by
      nlinarith only [hcubic]
    have := nonneg_of_mul_nonneg_right hm hq
    linarith

private lemma root_coarse_bound (s q : ℝ) (hs : 0 < s) (hs' : s < 1 / 2)
    (hq : 0 < q) (hq' : q ≤ 1) (heq : 1 - q = exp (-(1 + s) * q)) :
    q ≤ 4 * s / (1 + s) ^ 2 ∧ 0 < 1 - (1 + s) * q / 3 := by
  have hA : 0 < (1 + s) ^ 2 := by positivity
  have hB : 1 / 2 ≤ 1 - (1 + s) * q / 3 := by
    have := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 1 + s by positivity)
    nlinarith
  have hbound := (root_bounds s q hs hq heq).2
  have hm := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ (1 + s) ^ 2 * q / 2 by positivity)
  constructor
  · apply (le_div_iff₀ hA).mpr
    nlinarith only [hm, hbound]
  · linarith

/-! ### The Poisson offspring law -/

/-- The Poisson(`r`) generating function: `∑ e^{-r} r^k / k! x^k = exp (r (x - 1))`. -/
theorem pgf_poissonMeasure (r : ℝ≥0) (x : ℝ) :
    pgf id (poissonMeasure r) x = exp (r * (x - 1)) := by
  have hint : Integrable (fun n : ℕ => x ^ n) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    convert (Real.summable_pow_div_factorial ((r : ℝ) * |x|)).mul_left (exp (-r))
      using 1
    ext n
    simp only [Real.norm_eq_abs, abs_pow, mul_pow]
    ring
  simp only [pgf, id_eq]
  rw [integral_poissonMeasure' hint]
  calc
    ∑' n, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) • x ^ n =
        exp (-r) * ∑' n, ((r : ℝ) * x) ^ n / n.factorial := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [smul_eq_mul, mul_pow]
      ring
    _ = exp (-r) * exp ((r : ℝ) * x) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * x)).tsum_eq]
      rw [← Real.exp_eq_exp_ℝ]
    _ = exp (r * (x - 1)) := by
      rw [← exp_add]
      congr 1
      ring

/-- The Poisson(`r`) law has mean `r`. -/
theorem mean_poissonMeasure (r : ℝ≥0) : GaltonWatson.mean (poissonMeasure r) = r := by
  have hsum : HasSum (fun n : ℕ => (n : ℝ) * (exp (-r) * r ^ n / (n)!)) r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero]
    have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
    rw [mul_one] at h
    convert h using 1
    funext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * (exp (-r) * r ^ n / (n)!) := fun n => by positivity
  rw [GaltonWatson.mean, lintegral_countable']
  simp_rw [poissonMeasure_singleton]
  calc ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (exp (-r) * r ^ n / (n)!)
      = ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (exp (-r) * r ^ n / (n)!)) := by
        refine tsum_congr fun n => ?_
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]
    _ = r := ENNReal.ofReal_coe_nnreal

/-- Haldane's survival probability `π(s) = 1 - q(s)` of a mutant with selective advantage `s`
per generation, whose number of copies in the next generation is Poisson with mean `1 + s`.
The model needs `s ≥ -1`; for `s < -1` the mean is truncated to `0` (`Real.toNNReal`), the
mutant leaves no copies, and `π(s) = 0`. -/
noncomputable def survivalProb (s : ℝ) : ℝ :=
  1 - GaltonWatson.extinctionProb (poissonMeasure (1 + s).toNNReal)

/-- `π(s)` solves Haldane's equation `1 - π = exp (-(1 + s) π)`. -/
theorem one_sub_survivalProb {s : ℝ} (hs : -1 ≤ s) :
    1 - survivalProb s = exp (-(1 + s) * survivalProb s) := by
  have hfix := (GaltonWatson.isLeast_extinctionProb (poissonMeasure (1 + s).toNNReal)).1.2
  rw [pgf_poissonMeasure, Real.coe_toNNReal _ (by linarith)] at hfix
  rw [survivalProb, sub_sub_cancel]
  conv_lhs => rw [← hfix]
  congr 1
  ring

/-- A beneficial mutant survives with positive probability. -/
theorem survivalProb_pos {s : ℝ} (hs : 0 < s) : 0 < survivalProb s := by
  set ν := poissonMeasure (1 + s).toNNReal
  have hr : ((1 + s).toNNReal : ℝ) = 1 + s := Real.coe_toNNReal _ (by linarith)
  have h1 : ν {1} ≠ 1 := by
    rw [poissonMeasure_singleton]
    refine (ENNReal.ofReal_lt_one.2 ?_).ne
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    have := Real.add_one_le_exp ((1 + s).toNNReal : ℝ)
    rw [exp_neg, inv_mul_lt_iff₀ (exp_pos _)]
    linarith
  have hm : ¬ GaltonWatson.mean ν ≤ 1 := by
    rw [mean_poissonMeasure, ← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hr]
    simp only [NNReal.coe_one]
    linarith
  have hq := (GaltonWatson.isLeast_extinctionProb ν).1.1
  have hne : GaltonWatson.extinctionProb ν ≠ 1 :=
    fun h => hm ((GaltonWatson.extinctionProb_eq_one_iff ν h1).1 h)
  rw [survivalProb, sub_pos]
  exact lt_of_le_of_ne hq.2 hne

/-- The survival probability is less than `1`: the mutant leaves no copies with positive
probability `exp (-(1 + s))`. (For `s < -1`, outside the model, `π(s) = 0`.) -/
theorem survivalProb_lt_one (s : ℝ) : survivalProb s < 1 := by
  have hfix := (GaltonWatson.isLeast_extinctionProb (poissonMeasure (1 + s).toNNReal)).1.2
  rw [pgf_poissonMeasure] at hfix
  rw [survivalProb, sub_lt_self_iff, ← hfix]
  exact exp_pos _

/-- The survival probability is non-negative. -/
theorem survivalProb_nonneg (s : ℝ) : 0 ≤ survivalProb s := by
  rw [survivalProb, sub_nonneg]
  exact (GaltonWatson.isLeast_extinctionProb _).1.1.2

/-- Analytic core of Haldane's approximation: if `0 < p s ≤ 1` and
`1 - p s = exp (-(1 + s) p s)` for every `s > 0`, then `p s / s → 2` as `s → 0⁺`. -/
private theorem tendsto_div_of_one_sub_eq_exp (p : ℝ → ℝ) (hpos : ∀ s, 0 < s → 0 < p s)
    (hle : ∀ s, 0 < s → p s ≤ 1) (heq : ∀ s, 0 < s → 1 - p s = exp (-(1 + s) * p s)) :
    Tendsto (fun s => p s / s) (𝓝[>] 0) (𝓝 2) := by
  have hspos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 / 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun s : ℝ => (1 + s) ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hs).pow 2
  have hp : Tendsto p (𝓝[>] 0) (𝓝 0) := by
    have hupper : Tendsto (fun s : ℝ => 4 * s / (1 + s) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      convert ((tendsto_const_nhds (x := (4 : ℝ))).mul hs).div hA (by norm_num) using 1
      norm_num
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [hspos] with s hs'
      exact (hpos s hs').le
    · filter_upwards [hspos, hsmall] with s hs' hsmall'
      exact (root_coarse_bound s (p s) hs' hsmall' (hpos s hs')
        (hle s hs') (heq s hs')).1
  have hlower : Tendsto (fun s : ℝ => 2 / (1 + s) ^ 2)
      (𝓝[>] 0) (𝓝 2) := by
    convert (tendsto_const_nhds (x := (2 : ℝ))).div hA (by norm_num) using 1
    norm_num
  have hB : Tendsto (fun s : ℝ => 1 - (1 + s) * p s / 3)
      (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub
      (((tendsto_const_nhds.add hs).mul hp).div_const 3)
  have hupper : Tendsto
      (fun s : ℝ => 2 / ((1 + s) ^ 2 * (1 - (1 + s) * p s / 3)))
      (𝓝[>] 0) (𝓝 2) := by
    convert (tendsto_const_nhds (x := (2 : ℝ))).div (hA.mul hB) (by norm_num) using 1
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hspos] with s hs'
    have hApos : 0 < (1 + s) ^ 2 := by positivity
    apply (div_le_div_iff₀ hApos hs').mpr
    have := (root_bounds s (p s) hs' (hpos s hs') (heq s hs')).1
    nlinarith only [this]
  · filter_upwards [hspos, hsmall] with s hs' hsmall'
    have hBpos := (root_coarse_bound s (p s) hs' hsmall' (hpos s hs')
      (hle s hs') (heq s hs')).2
    have hApos : 0 < (1 + s) ^ 2 := by positivity
    apply (div_le_div_iff₀ hs' (mul_pos hApos hBpos)).mpr
    have := (root_bounds s (p s) hs' (hpos s hs') (heq s hs')).2
    nlinarith only [this]

/-- Haldane's approximation (Haldane 1927): `π(s) / s → 2` as `s → 0⁺`. -/
theorem tendsto_survivalProb_div :
    Tendsto (fun s => survivalProb s / s) (𝓝[>] 0) (𝓝 2) :=
  tendsto_div_of_one_sub_eq_exp survivalProb (fun _ hs => survivalProb_pos hs)
    (fun s _ => (survivalProb_lt_one s).le)
    (fun _ hs => one_sub_survivalProb (by linarith))

end MathlibExt.Biology.PopulationGenetics.Haldane
