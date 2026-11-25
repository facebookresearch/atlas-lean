/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Binomial
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Superspreading: negative-binomial offspring and extinction

Lloyd-Smith, Schreiber, Kopp and Getz (2005) model the number of secondary cases caused by one
infected individual as negative binomial with mean `R` (the reproductive number) and
dispersion `k > 0` (small `k` = strong individual variation, "superspreading"):

`P(Z = n) = C(k + n - 1, n) p^k (1 - p)^n`, `p = k / (k + R)`,

where `C(a, n) = Ring.choose a n` is the generalized binomial coefficient
(`C(k + n - 1, n) = Γ(k + n) / (Γ(k) n!)`). Its generating function is
`G_k(s) = (1 + (R / k) (1 - s))^{-k}`. The epidemic, started by one case, is a Galton–Watson
process with this offspring law, so the probability `q_k` of stochastic extinction (no major
outbreak) is the least fixed point of `G_k` in `[0, 1]` (`isLeast_extinctionProb_nbOffspring`,
from the Galton–Watson file).

## Main definitions

* `nbPmf R k n`: the negative-binomial probability of `n` offspring.
* `nbPgf R k s`: `(1 + (R / k) (1 - s))^{-k}`.
* `nbOffspring R k`: the negative-binomial offspring law as a measure on `ℕ`.

## Main results

* `hasSum_nbPmf_mul_pow`: `∑ₙ P(Z = n) sⁿ = G_k(s)` for `s ∈ [0, 1]` (the pgf identity).
* `pgf_nbOffspring`: the generating function of `nbOffspring R k` is `nbPgf R k` on `[0, 1]`.
* `nbPgf_antitone`: for fixed `R ≥ 0` and `s ∈ [0, 1]`, `G_k(s)` is nonincreasing in `k > 0`.
* `extinctionProb_le_of_pgf_le`: a Galton–Watson comparison principle, a pointwise smaller
  offspring generating function on `[0, 1]` gives a smaller extinction probability.
* `extinctionProb_nbOffspring_antitone`: **the extinction probability `q_k` is nonincreasing in
  the dispersion `k`**: more individual variation (smaller `k`) makes extinction more likely at
  the same `R` (Lloyd-Smith et al. 2005).
* `tendsto_nbPgf_atTop`: as `k → ∞`, `G_k(s) → e^{-R (1 - s)}`, the Poisson generating function.
* `nbPgf_one_dispersion`: `k = 1` is the geometric case `G_1(s) = 1 / (1 + R (1 - s))`.

Strict monotonicity in `k` (for `R > 1`) and the identification of the mean as `R` are not
formalized here.

## References

* J. O. Lloyd-Smith, S. J. Schreiber, P. E. Kopp, W. M. Getz, *Superspreading and the effect
  of individual variation on disease emergence*, Nature 438 (2005), 355–359.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer (1972), ch. I.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MathlibExt.Biology.Epidemiology.Superspreading

open MathlibExt.Probability MathlibExt.Probability.GaltonWatson

/-- The **negative-binomial offspring probability** with mean `R` and dispersion `k`:
`P(Z = n) = C(k + n - 1, n) p^k (1 - p)^n` with `p = k / (k + R)` (Lloyd-Smith et al. 2005).
Meaningful for `k > 0`, `R ≥ 0`. -/
noncomputable def nbPmf (R k : ℝ) (n : ℕ) : ℝ :=
  Ring.choose (k + n - 1) n * (k / (k + R)) ^ k * (R / (k + R)) ^ n

/-- The **negative-binomial generating function** `G_k(s) = (1 + (R / k) (1 - s))^{-k}`. -/
noncomputable def nbPgf (R k s : ℝ) : ℝ :=
  (1 + R / k * (1 - s)) ^ (-k)

/-- The negative-binomial offspring law as a measure on `ℕ`. -/
noncomputable def nbOffspring (R k : ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (nbPmf R k n) • Measure.dirac n

/-- The negative-binomial probabilities are nonnegative for `k > 0`, `R ≥ 0`. -/
theorem nbPmf_nonneg {R k : ℝ} (hk : 0 < k) (hR : 0 ≤ R) (n : ℕ) : 0 ≤ nbPmf R k n := by
  have hc : 0 ≤ Ring.choose (k + n - 1) n := by
    rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
    have he : k + n - 1 - n + 1 = k := by ring
    rw [he]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (ascPochhammer_pos n k hk).le
  exact mul_nonneg
    (mul_nonneg hc (Real.rpow_nonneg (div_nonneg hk.le (by linarith)) _))
    (pow_nonneg (div_nonneg hR (by linarith)) _)

/-- **Generating-function identity**: for `k > 0`, `R ≥ 0` and `s ∈ [0, 1]`,
`∑ₙ P(Z = n) sⁿ = (1 + (R / k) (1 - s))^{-k}`. -/
theorem hasSum_nbPmf_mul_pow {R k : ℝ} (hk : 0 < k) (hR : 0 ≤ R) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : HasSum (fun n => nbPmf R k n * s ^ n) (nbPgf R k s) := by
  have hd : 0 < k + R := by linarith
  let x := R / (k + R) * s
  have hx0 : 0 ≤ x := mul_nonneg (div_nonneg hR hd.le) hs.1
  have hx1 : x < 1 := by
    have hr : R / (k + R) < 1 := (div_lt_one hd).2 (by linarith)
    exact (mul_le_of_le_one_right (div_nonneg hR hd.le) hs.2).trans_lt hr
  have hxb : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq, abs_of_nonneg hx0] using hx1
  have hseries : HasSum (fun n : ℕ => Ring.choose (k + n - 1) n * x ^ n)
      (1 / (1 - x) ^ k) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
      using (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero k).hasSum hxb
  have hb : 0 < 1 + R / k * (1 - s) := by
    have : 0 ≤ R / k * (1 - s) :=
      mul_nonneg (div_nonneg hR hk.le) (sub_nonneg.mpr hs.2)
    linarith
  have he : (k / (k + R)) / (1 - x) = (1 + R / k * (1 - s))⁻¹ := by
    dsimp [x]
    field_simp
    ring
  have hvalue : (k / (k + R)) ^ k * (1 / (1 - x) ^ k) = nbPgf R k s := by
    rw [mul_one_div, ← Real.div_rpow (div_nonneg hk.le hd.le) (by linarith), he,
      ← Real.rpow_neg_eq_inv_rpow]
    rfl
  rw [← hvalue]
  convert (hseries.mul_left ((k / (k + R)) ^ k)) using 1
  · ext n
    simp only [nbPmf, x, mul_pow]
    ring

/-- The negative-binomial offspring law is a probability measure (`k > 0`, `R ≥ 0`). -/
theorem isProbabilityMeasure_nbOffspring {R k : ℝ} (hk : 0 < k) (hR : 0 ≤ R) :
    IsProbabilityMeasure (nbOffspring R k) := by
  have hsum : HasSum (nbPmf R k) 1 := by
    simpa [nbPgf] using hasSum_nbPmf_mul_pow hk hR (s := 1) (by simp)
  constructor
  rw [nbOffspring, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (nbPmf_nonneg hk hR) hsum.summable,
    hsum.tsum_eq, ENNReal.ofReal_one]

/-- The generating function of the negative-binomial offspring law is `nbPgf` on `[0, 1]`. -/
theorem pgf_nbOffspring {R k : ℝ} (hk : 0 < k) (hR : 0 ≤ R) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : pgf id (nbOffspring R k) s = nbPgf R k s := by
  have := isProbabilityMeasure_nbOffspring hk hR
  have hi : Integrable (fun n : ℕ => s ^ n) (nbOffspring R k) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1 n)]
      exact pow_le_one₀ hs.1 hs.2
  simp only [pgf, id_eq]
  rw [nbOffspring, integral_sum_measure hi]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  simp only [ENNReal.toReal_ofReal (nbPmf_nonneg hk hR _)]
  exact (hasSum_nbPmf_mul_pow hk hR hs).tsum_eq

private theorem dispersion_log_monotone (x : ℝ) (hx : 0 ≤ x) :
    MonotoneOn (fun k : ℝ => k * Real.log (1 + x / k)) (Ioi 0) := by
  have hd (k : ℝ) (hk : 0 < k) :
      HasDerivAt (fun k : ℝ => k * Real.log (1 + x / k))
        (Real.log (1 + x / k) - x / (k + x)) k := by
    have hb : 0 < 1 + x / k := by positivity
    convert (hasDerivAt_id k).mul
      ((((hasDerivAt_const k x).div (hasDerivAt_id k) hk.ne').const_add 1).log hb.ne')
      using 1
    · rfl
    · dsimp
      field_simp [hk.ne']
      ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro k hk
    exact (hd k hk).continuousAt.continuousWithinAt
  · intro k hk
    exact (hd k (interior_subset hk)).hasDerivWithinAt
  · intro k hk
    have hk0 : 0 < k := interior_subset hk
    have hb : 0 < 1 + x / k := by positivity
    have he : 1 - (1 + x / k)⁻¹ = x / (k + x) := by field_simp; ring
    have hlog := Real.one_sub_inv_le_log_of_pos hb
    rw [he] at hlog
    exact sub_nonneg.mpr hlog

/-- **Monotonicity in the dispersion**: for `R ≥ 0`, `s ∈ [0, 1]` and `0 < k₁ ≤ k₂`,
`G_{k₂}(s) ≤ G_{k₁}(s)`; equivalently `k ↦ k log (1 + x / k)` is nondecreasing for `x ≥ 0`. -/
theorem nbPgf_antitone {R : ℝ} (hR : 0 ≤ R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {k₁ k₂ : ℝ}
    (hk₁ : 0 < k₁) (hk : k₁ ≤ k₂) : nbPgf R k₂ s ≤ nbPgf R k₁ s := by
  let x := R * (1 - s)
  have hx : 0 ≤ x := mul_nonneg hR (sub_nonneg.mpr hs.2)
  have hk₂ : 0 < k₂ := hk₁.trans_le hk
  have hmono := dispersion_log_monotone x hx
  have hle := hmono hk₁ hk₂ hk
  have hb₁ : 0 < 1 + x / k₁ := by positivity
  have hb₂ : 0 < 1 + x / k₂ := by positivity
  have he (k : ℝ) : R / k * (1 - s) = x / k := by dsimp [x]; ring
  simp only [nbPgf, he, Real.rpow_def_of_pos hb₁, Real.rpow_def_of_pos hb₂]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `k = 1` is the geometric offspring law: `G_1(s) = 1 / (1 + R (1 - s))`. -/
theorem nbPgf_one_dispersion (R s : ℝ) : nbPgf R 1 s = 1 / (1 + R * (1 - s)) := by
  simp [nbPgf, Real.rpow_neg_one]

/-- **Poisson limit**: as `k → ∞`, `G_k(s) → e^{-R (1 - s)}` (for all real `R`, `s`). -/
theorem tendsto_nbPgf_atTop (R s : ℝ) :
    Tendsto (fun k => nbPgf R k s) atTop (𝓝 (Real.exp (-(R * (1 - s))))) := by
  let x := R * (1 - s)
  have ht := (Real.tendsto_one_add_div_rpow_exp x).inv₀ (Real.exp_ne_zero x)
  have ht' : Tendsto (fun k : ℝ => ((1 + x / k) ^ k)⁻¹) atTop
      (𝓝 (Real.exp (-x))) := by simpa only [Real.exp_neg] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-x))] with k hk
  have hk0 : 0 < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hxk : 0 < k + x := by have := lt_of_le_of_lt (le_max_right _ _) hk; linarith
  have hb : 0 < 1 + x / k := by
    rw [show 1 + x / k = (k + x) / k by rw [add_div, div_self hk0.ne']]
    exact div_pos hxk hk0
  rw [nbPgf, show R / k * (1 - s) = x / k by dsimp [x]; ring,
    Real.rpow_neg hb.le]

/-- **Comparison principle for Galton–Watson extinction**: if the offspring generating
functions satisfy `f₂ ≤ f₁` on `[0, 1]`, then the extinction probabilities satisfy
`q₂ ≤ q₁`. -/
theorem extinctionProb_le_of_pgf_le (ν₁ ν₂ : Measure ℕ) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (h : ∀ s ∈ Icc (0 : ℝ) 1, pgf id ν₂ s ≤ pgf id ν₁ s) :
    extinctionProb ν₂ ≤ extinctionProb ν₁ := by
  obtain ⟨⟨hq₁, hfix⟩, -⟩ := isLeast_extinctionProb ν₁
  have hmono : MonotoneOn (pgf id ν₂) (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact integral_mono
      (integrable_pow_of_abs_le_one measurable_id (by simpa [abs_of_nonneg hs.1] using hs.2))
      (integrable_pow_of_abs_le_one measurable_id (by simpa [abs_of_nonneg ht.1] using ht.2))
      (fun k => pow_le_pow_left₀ hs.1 hst k)
  have hit : ∀ m, (pgf id ν₂)^[m] 0 ≤ extinctionProb ν₁ := by
    intro m
    induction m with
    | zero => exact hq₁.1
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      calc pgf id ν₂ ((pgf id ν₂)^[m] 0) ≤ pgf id ν₂ (extinctionProb ν₁) :=
            hmono (iterate_pgf_mem_Icc ν₂ m ⟨le_rfl, zero_le_one⟩) hq₁ ih
        _ ≤ pgf id ν₁ (extinctionProb ν₁) := h _ hq₁
        _ = extinctionProb ν₁ := hfix
  unfold extinctionProb
  exact ciSup_le fun m => by rw [law_real_zero]; exact hit m

/-- The extinction probability of the negative-binomial epidemic is the least fixed point of
`G_k` in `[0, 1]`. -/
theorem isLeast_extinctionProb_nbOffspring {R k : ℝ} (hk : 0 < k) (hR : 0 ≤ R) :
    have := isProbabilityMeasure_nbOffspring hk hR
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ nbPgf R k s = s} (extinctionProb (nbOffspring R k)) := by
  have := isProbabilityMeasure_nbOffspring hk hR
  have h := isLeast_extinctionProb (nbOffspring R k)
  have hset : {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id (nbOffspring R k) s = s} =
      {s | s ∈ Icc (0 : ℝ) 1 ∧ nbPgf R k s = s} := by
    ext s
    constructor
    · rintro ⟨hs, he⟩; exact ⟨hs, by rwa [← pgf_nbOffspring hk hR hs]⟩
    · rintro ⟨hs, he⟩; exact ⟨hs, by rwa [pgf_nbOffspring hk hR hs]⟩
  rwa [hset] at h

/-- **Superspreading raises the extinction probability** (Lloyd-Smith et al. 2005): at a
fixed mean `R ≥ 0`, the probability `q_k` that the outbreak started by one case goes extinct
is nonincreasing in the dispersion `k > 0`. -/
theorem extinctionProb_nbOffspring_antitone {R : ℝ} (hR : 0 ≤ R) {k₁ k₂ : ℝ} (hk₁ : 0 < k₁)
    (hk : k₁ ≤ k₂) :
    have := isProbabilityMeasure_nbOffspring hk₁ hR
    have := isProbabilityMeasure_nbOffspring (hk₁.trans_le hk) hR
    extinctionProb (nbOffspring R k₂) ≤ extinctionProb (nbOffspring R k₁) := by
  have := isProbabilityMeasure_nbOffspring hk₁ hR
  have := isProbabilityMeasure_nbOffspring (hk₁.trans_le hk) hR
  exact extinctionProb_le_of_pgf_le _ _ fun s hs => by
    rw [pgf_nbOffspring (hk₁.trans_le hk) hR hs, pgf_nbOffspring hk₁ hR hs]
    exact nbPgf_antitone hR hs hk₁ hk

end MathlibExt.Biology.Epidemiology.Superspreading
