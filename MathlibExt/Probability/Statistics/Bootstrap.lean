/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LindebergFeller
public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Bootstrap validity for smooth statistics of the sample mean

Efron's nonparametric bootstrap approximates the sampling law of a statistic by its law under
resampling from the empirical distribution. This file proves that the approximation is
asymptotically valid for smooth functions of the mean of iid finite-dimensional observations:
for almost every data sequence, the conditional law of `√n (g(x̄*ₙ) - g(x̄ₙ))` given the data
converges weakly to the delta-method limit of `√n (g(x̄ₙ) - g(E X))`.

## Model of the conditional law

For data `x : ℕ → α`, `empirical x n` puts mass `1 / n` on each of `x 0, …, x (n - 1)`, and
`world x` is the single probability space `ℕ → ℕ → α` (a product of `infinitePi`s) on which the
row `ω n` is an iid sequence from `empirical x n`. The bootstrap resample of size `n` is
`ω n 0, …, ω n (n - 1)`. Since `world x` depends only on the data, "the conditional law of a
bootstrap statistic given the sample" is formalized as its law under `world x`, and bootstrap
validity is a `TendstoInDistribution` statement under `world x`, holding for a fixed data
sequence (deterministic theorems) or for `P`-almost every realised data sequence (iid
theorems).

## The conditional triangular-array CLT

The resampled values form a triangular array whose row-`n` law changes with `n`, so the iid
CLT does not apply to them, and neither does an iid delta method for the data. The proof
applies the triangular-array Lindeberg–Feller theorem `lindeberg_feller_clt_triangular` to the
centred bootstrap array `(ω n k - x̄ₙ) / √n`. Its Lindeberg condition is a condition on the data,

  `(1 / n) ∑_{i<n} (x i - x̄ₙ)² 𝟙{|x i - x̄ₙ| > ε √n} → 0` for every `ε > 0`,

which, with `empiricalVar x n → σ² > 0`, gives the conditional CLT
`tendstoInDistribution_bootMean`. For iid square-integrable data both conditions hold almost
surely: the strong law for `X` and `X²` gives the variance limit and `max_{i<n} |X i| = o(√n)`
(`lindeberg_of_tendsto_sampleMean`), so the truncated sums are eventually `0`.

Smooth statistics need a delta method with a *moving* centre, since both `x̄*ₙ` and `x̄ₙ`
move: `TendstoInDistribution.delta_method_of_hasStrictFDerivAt` assumes `g` strictly
differentiable at the limit. For `E`-valued data, every projection `⟪·, t⟫` maps the bootstrap
world of `x` to the bootstrap world of `⟪x ·, t⟫` (`map_world`), and the Cramér–Wold device
assembles the directions. Almost surely, the plug-in variances converge in every direction at
once: finitely many strong laws, one for each coordinate product in an orthonormal basis.

## Main results

* `tendstoInDistribution_bootMean`: conditional Lindeberg CLT for the bootstrap mean.
* `TendstoInDistribution.delta_method_of_hasStrictFDerivAt`: delta method with a moving centre.
* `tendstoInDistribution_bootstrap_of_hasStrictDerivAt`: bootstrap of `g(x̄)`, fixed data.
* `ae_tendstoInDistribution_bootMean`,
  `ae_tendstoInDistribution_bootstrap_of_hasStrictDerivAt`: almost-sure bootstrap validity for
  iid real data with positive variance.
* `tendstoInDistribution_bootMeanVec`,
  `tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt`: the same for `E`-valued data in a
  finite-dimensional inner product space, fixed data.
* `ae_tendstoInDistribution_bootMeanVec`,
  `ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt`: almost-sure bootstrap validity
  for iid `E`-valued data with nonsingular covariance and smooth `g : E → F`.

## Scope

* Only iid observations and statistics `g(x̄)` with `g` strictly differentiable at the mean.
  Nothing here concerns dependent data, high-dimensional (`dim → ∞`) settings, the
  `m`-out-of-`n` bootstrap, or coverage of bootstrap confidence intervals.
* The variance must be positive (scalar case) and the covariance nonsingular (vector case);
  degenerate directions are excluded by hypothesis, not handled.
* The conclusion is first order: when `g' = 0` (or `L = 0`) the limit is the point mass at
  `0`, and no second-order bootstrap limit is claimed.

## References

* P. J. Bickel and D. A. Freedman, *Some asymptotic theory for the bootstrap*, Ann. Statist. 9
  (1981), 1196–1217.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Chapter 23 (consistency of the
  bootstrap for the sample mean and the bootstrap delta method).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped Topology ENNReal NNReal RealInnerProductSpace
open MathlibExt.Probability.Causality (sampleMean)

namespace ProbabilityTheory.Bootstrap

section Generic

variable {α : Type*} [MeasurableSpace α] [Zero α]

/-- The **empirical distribution** of the first `n` observations `x 0, …, x (n - 1)`:
mass `1 / n` at each `x i`, `i < n`. For `n = 0` (no data) it is the point mass at `0`;
this convention only keeps the bootstrap law a probability measure at every index and plays
no role in any limit statement. -/
noncomputable def empirical (x : ℕ → α) (n : ℕ) : Measure α :=
  if n = 0 then Measure.dirac 0 else (n : ℝ≥0∞)⁻¹ • ∑ i ∈ range n, Measure.dirac (x i)

/-- For `n ≠ 0` the empirical distribution is the average of the point masses. -/
theorem empirical_of_ne_zero {x : ℕ → α} {n : ℕ} (hn : n ≠ 0) :
    empirical x n = (n : ℝ≥0∞)⁻¹ • ∑ i ∈ range n, Measure.dirac (x i) := by
  simp [empirical, hn]

/-- The empirical distribution is a probability measure. -/
instance isProbabilityMeasure_empirical (x : ℕ → α) (n : ℕ) :
    IsProbabilityMeasure (empirical x n) := by
  by_cases hn : n = 0
  · simp only [empirical, hn, ite_true]; infer_instance
  · constructor
    rw [empirical_of_ne_zero hn, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply]
    simp only [measure_univ, Finset.sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)

/-- Every function is integrable for the empirical distribution (finitely many atoms). -/
theorem integrable_empirical [MeasurableSingletonClass α] (x : ℕ → α) (n : ℕ) (f : α → ℝ) :
    Integrable f (empirical x n) := by
  by_cases hn : n = 0
  · simp only [empirical, hn, ite_true]
    exact integrable_dirac enorm_lt_top
  · rw [empirical_of_ne_zero hn]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by exact_mod_cast hn))
    exact integrable_finsetSum_measure.2 fun i _ => integrable_dirac enorm_lt_top

/-- Integrals against the empirical distribution are sample averages. -/
theorem integral_empirical [MeasurableSingletonClass α] {x : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (f : α → ℝ) :
    ∫ y, f y ∂empirical x n = (n : ℝ)⁻¹ * ∑ i ∈ range n, f (x i) := by
  rw [empirical_of_ne_zero hn, integral_smul_measure,
    integral_finsetSum_measure fun i _ => integrable_dirac enorm_lt_top]
  simp [integral_dirac, ENNReal.toReal_inv]

/-- The **bootstrap world** built on the data `x`: a single probability space
`ℕ → ℕ → α` on which, for every sample size `n`, the row `ω n` is an iid sequence drawn from
the empirical distribution `empirical x n`, and different rows are independent. The bootstrap
resample at sample size `n` is `(ω n 0, …, ω n (n - 1))`. The measure depends only on the
data, so laws under `world x` are the *conditional* laws of bootstrap statistics given the
sample. -/
noncomputable def world (x : ℕ → α) : Measure (ℕ → ℕ → α) :=
  Measure.infinitePi fun n => Measure.infinitePi fun _ : ℕ => empirical x n

/-- The bootstrap world is a probability measure. -/
instance isProbabilityMeasure_world (x : ℕ → α) : IsProbabilityMeasure (world x) := by
  unfold world; infer_instance

/-- Each bootstrap draw `ω n k` has law `empirical x n` under `world x`. -/
theorem measurePreserving_world_eval (x : ℕ → α) (n k : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℕ → α => ω n k) (world x) (empirical x n) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => empirical x n) k).comp
    (measurePreserving_eval_infinitePi
      (fun n => Measure.infinitePi fun _ : ℕ => empirical x n) n)

/-- Expectations of a single bootstrap draw are sample averages of the data. -/
theorem integral_world [MeasurableSingletonClass α] {x : ℕ → α} {n : ℕ} (hn : n ≠ 0) (k : ℕ)
    {f : α → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω n k) ∂world x = (n : ℝ)⁻¹ * ∑ i ∈ range n, f (x i) := by
  have h := measurePreserving_world_eval x n k
  rw [← integral_empirical hn f, ← h.map_eq,
    integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]

/-- Every measurable function of a single bootstrap draw is integrable. -/
theorem integrable_world [MeasurableSingletonClass α] (x : ℕ → α) (n k : ℕ) {f : α → ℝ}
    (hf : Measurable f) :
    Integrable (fun ω : ℕ → ℕ → α => f (ω n k)) (world x) :=
  ((measurePreserving_world_eval x n k).integrable_comp hf.aestronglyMeasurable).2
    (integrable_empirical x n f)

/-- Pushing the empirical distribution forward along a map fixing `0` gives the empirical
distribution of the transformed data. -/
theorem map_empirical [MeasurableSingletonClass α] {β : Type*} [MeasurableSpace β] [Zero β]
    [MeasurableSingletonClass β]
    (x : ℕ → α) (n : ℕ) {f : α → β} (hf : Measurable f) (hf0 : f 0 = 0) :
    (empirical x n).map f = empirical (fun i => f (x i)) n := by
  by_cases hn : n = 0
  · simp [empirical, hn, Measure.map_dirac, hf0]
  · rw [empirical_of_ne_zero hn, empirical_of_ne_zero hn, Measure.map_smul _ hf.aemeasurable,
      Measure.map_finset_sum hf.aemeasurable]
    simp [Measure.map_dirac]

/-- Transforming every bootstrap draw by a map fixing `0` turns the bootstrap world of `x` into
the bootstrap world of the transformed data. -/
theorem map_world [MeasurableSingletonClass α] {β : Type*} [MeasurableSpace β] [Zero β]
    [MeasurableSingletonClass β]
    (x : ℕ → α) {f : α → β} (hf : Measurable f) (hf0 : f 0 = 0) :
    (world x).map (fun ω n k => f (ω n k)) = world (fun i => f (x i)) := by
  unfold world
  refine (Measure.infinitePi_map_pi
    (μ := fun n => Measure.infinitePi fun _ : ℕ => empirical x n)
    (f := fun _ (row : ℕ → α) k => f (row k)) (fun _ => by fun_prop)).trans ?_
  congr 1; funext n
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => empirical x n) (f := fun _ => f) (fun _ => hf)]
  simp_rw [map_empirical x n hf hf0]

end Generic

/-! Throughout, `x̄ₙ` is `sampleMean x (range n)`, reusing
`MathlibExt.Probability.Causality.sampleMean`. -/

/-- The sample mean `x̄ₙ = sampleMean x (range n)` of the first `n` observations as a scaled
sum. -/
theorem sampleMean_range (x : ℕ → ℝ) (n : ℕ) :
    sampleMean x (range n) = (n : ℝ)⁻¹ * ∑ i ∈ range n, x i := by
  simp [sampleMean, div_eq_inv_mul]

/-- The **plug-in sample variance** `(1 / n) ∑_{i < n} (x i - x̄ₙ)²`, i.e. the variance of
the empirical distribution `empirical x n`. Its divisor is `n`, unlike the unbiased
`MathlibExt.Probability.Causality.sampleVar` (divisor `n - 1`); the bootstrap resamples from
the empirical distribution, so the plug-in variance is the one that appears. -/
noncomputable def empiricalVar (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, (x i - sampleMean x (range n)) ^ 2

/-- The **bootstrap sample mean** at sample size `n`: the average of the resample
`ω n 0, …, ω n (n - 1)`. -/
noncomputable def bootMean (n : ℕ) (ω : ℕ → ℕ → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ k ∈ range n, ω n k

/-- The bootstrap mean is measurable. -/
theorem measurable_bootMean (n : ℕ) : Measurable (bootMean n) := by
  unfold bootMean; fun_prop

/-- `n * x̄ₙ = ∑_{i<n} x i` for `n ≠ 0`. -/
private theorem natCast_mul_sampleMean {x : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * sampleMean x (range n) = ∑ i ∈ range n, x i := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [sampleMean_range, ← mul_assoc, mul_inv_cancel₀ this]

/-- The centred, `√n`-scaled bootstrap mean is the row sum of the triangular array
`(ω n k - x̄ₙ) / √n`. -/
theorem sqrt_mul_bootMean_sub (x : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ → ℝ) :
    √n * (bootMean n ω - sampleMean x (range n)) =
      ∑ k ∈ range n, (ω n k - sampleMean x (range n)) / √n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hs : √(n : ℝ) ≠ 0 := by positivity
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by positivity)
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    bootMean, eq_div_iff hs]
  calc √(n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ range n, ω n k - sampleMean x (range n)) * √(n : ℝ)
      = (√(n : ℝ) * √(n : ℝ)) *
          ((n : ℝ)⁻¹ * ∑ k ∈ range n, ω n k - sampleMean x (range n)) := by ring
    _ = _ := by rw [hsq]; field_simp


/-- The rows of the centred, scaled bootstrap array are independent under `world x`. -/
private theorem iIndepFun_row (x : ℕ → ℝ) (n : ℕ) :
    iIndepFun (m := fun _ => inferInstance)
      ((range n).restrict (fun k (ω : ℕ → ℕ → ℝ) => (ω n k - sampleMean x (range n)) / √n))
      (world x) := by
  have h := iIndepFun_uncurry_infinitePi' (fun n (_ : ℕ) => empirical x n)
    (X := fun n (_ : ℕ) (y : ℝ) => (y - sampleMean x (range n)) / √n) (fun _ _ => by fun_prop)
  exact h.precomp (g := fun k : range n => (n, k.1)) fun a b hab =>
    Subtype.ext (congrArg Prod.snd hab)

/-- **Conditional Lindeberg CLT for the bootstrap mean (Bickel–Freedman).**

Fix a data sequence `x`. Suppose the plug-in sample variances `empiricalVar x n` converge to
`σ² > 0`, and the centred data satisfy the Lindeberg condition
`(1 / n) ∑_{i<n} (x i - x̄ₙ)² 𝟙{|x i - x̄ₙ| > ε √n} → 0` for every `ε > 0`. Then, under the
bootstrap world (i.e. conditionally on the data), `√n (x̄*ₙ - x̄ₙ)` converges in distribution to
`N(0, σ²)`.

The proof applies the triangular-array Lindeberg–Feller theorem
`lindeberg_feller_clt_triangular` to the bootstrap array `(ω n k - x̄ₙ) / √n`, `k < n`, whose
rows are iid from the centred empirical distribution. The data Lindeberg hypothesis is exactly
the Lindeberg condition of that array; it does not follow from the variance condition alone,
which is why an iid central limit theorem for the data cannot replace it. -/
theorem tendstoInDistribution_bootMean (x : ℕ → ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : Tendsto (empiricalVar x) atTop (𝓝 v))
    (hLind : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |x i - sampleMean x (range n)| then (x i - sampleMean x (range n)) ^ 2 else 0)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (bootMean n ω - sampleMean x (range n))) atTop
      (id : ℝ → ℝ)
      (fun _ => world x) (gaussianReal 0 v) := by
  set σ : ℝ := √(v : ℝ) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσv : σ ^ 2 = v := Real.sq_sqrt v.2
  have hgauss : gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ = gaussianReal 0 v := by
    congr 1; exact NNReal.eq hσv
  set X : ℕ → ℕ → (ℕ → ℕ → ℝ) → ℝ := fun n k ω => (ω n k - sampleMean x (range n)) / √n with hX
  have hXmeas : ∀ n k, Measurable (X n k) := fun n k => by simp only [hX]; fun_prop
  have hmean : ∀ n, ∀ k ∈ range n, ∫ ω, X n k ω ∂world x = 0 := by
    intro n k hk
    have hn : n ≠ 0 := by rintro rfl; simp at hk
    rw [integral_world hn k (f := fun y => (y - sampleMean x (range n)) / √n) (by fun_prop),
      ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
      natCast_mul_sampleMean hn]
    simp
  have hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => (X n k ω) ^ 2) (world x) :=
    fun n k _ => integrable_world x n k
      (f := fun y => ((y - sampleMean x (range n)) / √n) ^ 2) (by fun_prop)
  -- the row variance is the plug-in sample variance
  have hvar' : Tendsto (fun n => ∑ k ∈ range n, ∫ ω, (X n k ω) ^ 2 ∂world x) atTop
      (𝓝 (σ ^ 2)) := by
    rw [hσv]
    refine hvar.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    simp_rw [hX, integral_world hn _
      (f := fun y => ((y - sampleMean x (range n)) / √n) ^ 2) (by fun_prop)]
    rw [Finset.sum_const, card_range, nsmul_eq_mul, empiricalVar]
    simp_rw [div_pow, hsq, ← Finset.sum_div]
    field_simp
  -- the Lindeberg condition of the bootstrap array is the data Lindeberg condition
  have hL : LindebergConditionTriangular X (world x) := by
    intro ε hε
    refine (hLind ε hε).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : 0 < √(n : ℝ) := by positivity
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hfun : ∀ k, (fun ω : ℕ → ℕ → ℝ => (X n k ω) ^ 2 *
        Set.indicator {ω' | ε < |X n k ω'|} 1 ω) = fun ω =>
        (fun y : ℝ => if ε * √n < |y - sampleMean x (range n)|
          then ((y - sampleMean x (range n)) / √n) ^ 2 else 0) (ω n k) := by
      intro k; funext ω
      simp only [hX, Set.indicator_apply, Set.mem_ofPred_eq, abs_div, abs_of_pos hs,
        lt_div_iff₀ hs, Pi.one_apply]
      split_ifs <;> simp
    have hmeasf : Measurable fun y : ℝ =>
        if ε * √n < |y - sampleMean x (range n)|
        then ((y - sampleMean x (range n)) / √n) ^ 2 else 0 :=
      Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
        measurable_const
    simp_rw [hfun, integral_world hn _ hmeasf, Finset.sum_const, card_range, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [div_pow, hsq]; field_simp
    · simp
  have hclt := lindeberg_feller_clt_triangular X (iIndepFun_row x) (fun n k _ => hXmeas n k)
    hmean hint2 σ hσ hvar' hL
  have hS : ∀ n : ℕ, Measurable fun ω : ℕ → ℕ → ℝ =>
      √(n : ℝ) * (bootMean n ω - sampleMean x (range n)) :=
    fun n =>
    measurable_const.mul ((measurable_bootMean n).sub measurable_const)
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ (fun n => (hS n).aemeasurable)
    measurable_id.aemeasurable]
  intro f
  have h := hclt f
  rw [hgauss] at h
  simp only [id]
  refine h.congr fun n => ?_
  rw [integral_map (Finset.measurable_sum _ fun k _ => hXmeas n k).aemeasurable
    f.continuous.aestronglyMeasurable]
  simp_rw [hX, sqrt_mul_bootMean_sub]


end ProbabilityTheory.Bootstrap

namespace MeasureTheory

variable {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {l : Filter ι}

/-- If `U n → u₀` in probability and the deterministic `c n → θ`, then `f (U n, c n)` tends to
`f (u₀, θ)` in probability for `f` continuous at `(u₀, θ)`. -/
private theorem tendstoInMeasure_comp_prodMk_seq {E G F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace G] [PseudoMetricSpace F] {U : ι → Ω → E} {c : ι → G} {u₀ : E} {θ : G}
    {f : E × G → F} (hf : ContinuousAt f (u₀, θ)) (hU : TendstoInMeasure μ U l (fun _ ↦ u₀))
    (hc : Tendsto c l (𝓝 θ)) :
    TendstoInMeasure μ (fun n ω ↦ f (U n ω, c n)) l (fun _ ↦ f (u₀, θ)) := by
  rw [tendstoInMeasure_iff_dist] at hU ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hU δ hδ)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hc (Metric.ball_mem_nhds θ hδ)] with n hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra h
  refine (hδε ?_).not_ge hω
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨not_le.1 h, hn⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [l.IsCountablyGenerated]

/-- **Delta method with a moving centre.** Let `r n → ∞`, let the deterministic centres
`c n → θ`, and suppose `r n • (X n - c n)` converges in distribution to `Z`. If `g` is
*strictly* differentiable at `θ` with derivative `L`, then `r n • (g (X n) - g (c n))`
converges in distribution to `L Z`.

Strict differentiability (`HasStrictFDerivAt`) is the right hypothesis here: the increment
`g (X n) - g (c n)` is taken between two points that both move towards `θ`, and plain
differentiability at `θ` only controls increments based at `θ` itself. This is the form used
for the bootstrap, where `X n` is the bootstrap statistic and `c n` the observed one. -/
theorem TendstoInDistribution.delta_method_of_hasStrictFDerivAt {X : ι → Ω → E} {c : ι → E}
    {Z : Ω' → E} {θ : E} {r : ι → ℝ} {g : E → F} {L : E →L[ℝ] F}
    (hXZ : TendstoInDistribution (fun n ω ↦ r n • (X n ω - c n)) l Z (fun _ ↦ μ) μ')
    (hr : Tendsto r l atTop) (hc : Tendsto c l (𝓝 θ)) (hg : HasStrictFDerivAt g L θ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hgX : ∀ n, AEMeasurable (fun ω ↦ g (X n ω)) μ) :
    TendstoInDistribution (fun n ω ↦ r n • (g (X n ω) - g (c n))) l (fun ω ↦ L (Z ω))
      (fun _ ↦ μ) μ' := by
  have hr_pos : ∀ᶠ n in l, 0 < r n := hr.eventually_gt_atTop 0
  -- Step 1: `X n - c n → 0` in probability.
  have h1 : TendstoInDistribution (fun n ω ↦ (r n)⁻¹ • (r n • (X n ω - c n))) l
      (fun _ ↦ (0 : E)) (fun _ ↦ μ) μ' := by
    refine (hXZ.smul_of_tendstoInMeasure_const (Y := fun n _ ↦ (r n)⁻¹) (c := 0) ?_
      (fun _ ↦ aemeasurable_const)).congr (fun _ ↦ ae_of_all _ fun _ ↦ rfl)
      (ae_of_all _ fun ω ↦ zero_smul ℝ (Z ω))
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1
      (tendsto_inv_atTop_zero.comp hr)).eventually (gt_mem_nhds hε)] with n hn
    simp only [Function.comp_apply, sub_zero, norm_inv, Real.norm_eq_abs] at hn
    simp [hn.not_ge]
  have hU : TendstoInMeasure μ (fun n ω ↦ X n ω - c n) l (fun _ ↦ 0) := by
    refine (tendstoInMeasure_of_tendstoInDistribution_const h1).congr' ?_ EventuallyEq.rfl
    filter_upwards [hr_pos] with n hn
    exact ae_of_all _ fun ω ↦ by simp [smul_smul, inv_mul_cancel₀ hn.ne']
  -- Step 2: the normalised remainder tends to `0` in probability.
  set ψ : E × E → F := fun q ↦ ‖q.1‖⁻¹ • (g (q.2 + q.1) - g q.2 - L q.1) with hψ_def
  have hψ0 : ψ (0, θ) = 0 := by simp [ψ]
  have hψ : ContinuousAt ψ (0, θ) := by
    have hφ : Tendsto (fun q : E × E ↦ (q.2 + q.1, q.2)) (𝓝 (0, θ)) (𝓝 (θ, θ)) := by
      have : Continuous fun q : E × E ↦ (q.2 + q.1, q.2) := by fun_prop
      simpa using this.tendsto (0, θ)
    have ho := (hasStrictFDerivAt_iff_isLittleO.1 hg).comp_tendsto hφ
    rw [ContinuousAt, hψ0, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Asymptotics.isLittleO_iff.1 ho (half_pos hε)] with q hq
    simp only [Function.comp_apply, add_sub_cancel_left] at hq
    rw [dist_zero_right, hψ_def, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖q.1‖ 0 with h0 | h0
    · simp [h0, hε]
    · calc ‖q.1‖⁻¹ * ‖g (q.2 + q.1) - g q.2 - L q.1‖ ≤ ‖q.1‖⁻¹ * (ε / 2 * ‖q.1‖) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
  set η : ι → Ω → F := fun n ω ↦
    ‖X n ω - c n‖⁻¹ • (g (X n ω) - g (c n) - L (X n ω - c n)) with hη_def
  have hηψ : ∀ n ω, η n ω = ψ (X n ω - c n, c n) := fun n ω ↦ by
    simp [η, ψ, add_sub_cancel]
  have hη : TendstoInMeasure μ η l (fun _ ↦ 0) := by
    have h := tendstoInMeasure_comp_prodMk_seq hψ hU hc
    rw [hψ0] at h
    exact h.congr (fun n ↦ ae_of_all _ fun ω ↦ (hηψ n ω).symm) EventuallyEq.rfl
  have hη_meas : ∀ n, AEMeasurable (η n) μ := fun n ↦
    ((hX n).sub_const _).norm.inv.smul (((hgX n).sub_const _).sub
      (L.continuous.measurable.comp_aemeasurable ((hX n).sub_const _)))
  have hnorm : TendstoInDistribution (fun n ω ↦ ‖r n • (X n ω - c n)‖) l (fun ω ↦ ‖Z ω‖)
      (fun _ ↦ μ) μ' := hXZ.continuous_comp continuous_norm
  have hprod : TendstoInDistribution (fun n ω ↦ ‖r n • (X n ω - c n)‖ • η n ω) l
      (fun _ ↦ (0 : F)) (fun _ ↦ μ) μ' :=
    (hnorm.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × F ↦ p.1 • p.2) (by fun_prop) hη hη_meas).congr
      (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ smul_zero _)
  have hrem : TendstoInMeasure μ (fun n ω ↦ r n • (g (X n ω) - g (c n) - L (X n ω - c n))) l
      (fun _ ↦ 0) := by
    refine (tendstoInMeasure_of_tendstoInDistribution_const hprod).congr' ?_ EventuallyEq.rfl
    filter_upwards [hr_pos] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    by_cases hv : X n ω - c n = 0
    · have hXn : X n ω = c n := sub_eq_zero.1 hv
      simp [η, hXn]
    · simp only [η, norm_smul, Real.norm_of_nonneg hn.le, smul_smul, mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), mul_one]
  -- Step 3: assemble.
  have hlin : TendstoInDistribution (fun n ω ↦ L (r n • (X n ω - c n))) l (fun ω ↦ L (Z ω))
      (fun _ ↦ μ) μ' := hXZ.continuous_comp L.continuous
  refine (hlin.add_of_tendstoInMeasure_const hrem fun n ↦ ?_).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ add_zero _)
  · exact (((hgX n).sub_const _).sub
      (L.continuous.measurable.comp_aemeasurable ((hX n).sub_const _))).const_smul _
  · simp only [Pi.add_apply, map_smul, ← smul_add]
    congr 1
    abel

end MeasureTheory

namespace ProbabilityTheory.Bootstrap

/-- **Bootstrap validity for a smooth function of the mean (deterministic data).**

Under the hypotheses of `tendstoInDistribution_bootMean`, if moreover the sample means converge
to `θ` and `g` is strictly differentiable at `θ` with derivative `g'`, then, conditionally on
the data, the bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` converges in distribution to
`N(0, g'² v)`, the same limit as the sampling distribution of `√n (g(x̄ₙ) - g(θ))`. -/
theorem tendstoInDistribution_bootstrap_of_hasStrictDerivAt (x : ℕ → ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : Tendsto (empiricalVar x) atTop (𝓝 v))
    (hLind : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |x i - sampleMean x (range n)| then (x i - sampleMean x (range n)) ^ 2 else 0)
      atTop (𝓝 0))
    {θ : ℝ} (hθ : Tendsto (fun n : ℕ => sampleMean x (range n)) atTop (𝓝 θ)) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasStrictDerivAt g g' θ) (hgm : Measurable g) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (g (bootMean n ω) - g (sampleMean x (range n)))) atTop
      (id : ℝ → ℝ) (fun _ => world x) (gaussianReal 0 (‖g'‖₊ ^ 2 * v)) := by
  have h := tendstoInDistribution_bootMean x hv hvar hLind
  have hr : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hd := TendstoInDistribution.delta_method_of_hasStrictFDerivAt (X := bootMean)
    (c := fun n : ℕ => sampleMean x (range n)) (r := fun n : ℕ => √(n : ℝ)) h hr hθ
    hg.hasStrictFDerivAt
    (fun n => (measurable_bootMean n).aemeasurable)
    (fun n => (hgm.comp (measurable_bootMean n)).aemeasurable)
  have hlaw : (gaussianReal 0 v).map
      (fun ω => ContinuousLinearMap.toSpanSingleton ℝ g' (id ω)) =
      (gaussianReal 0 (‖g'‖₊ ^ 2 * v)).map id := by
    have hfun : (fun ω => ContinuousLinearMap.toSpanSingleton ℝ g' (id ω)) =
        fun ω => g' * ω := by
      funext ω; simp [mul_comm]
    rw [hfun, gaussianReal_map_const_mul, Measure.map_id, mul_zero]
    congr 2
    exact NNReal.eq (by simp)
  refine ⟨hd.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hlim : (⟨(gaussianReal 0 (‖g'‖₊ ^ 2 * v)).map id, inferInstance⟩ :
      ProbabilityMeasure ℝ) = ⟨(gaussianReal 0 v).map
        (fun ω => ContinuousLinearMap.toSpanSingleton ℝ g' (id ω)), inferInstance⟩ :=
    Subtype.ext hlaw.symm
  rw [hlim]
  exact hd.tendsto

/-- The plug-in sample variance is the mean of squares minus the squared mean. -/
theorem empiricalVar_eq {x : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    empiricalVar x n = (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ^ 2 - sampleMean x (range n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsum := natCast_mul_sampleMean (x := x) hn
  have : ∑ i ∈ range n, (x i - sampleMean x (range n)) ^ 2 =
      ∑ i ∈ range n, x i ^ 2 - 2 * sampleMean x (range n) * ∑ i ∈ range n, x i +
        n * sampleMean x (range n) ^ 2 := by
    calc ∑ i ∈ range n, (x i - sampleMean x (range n)) ^ 2
        = ∑ i ∈ range n,
            (x i ^ 2 + (-(2 * sampleMean x (range n))) * x i + sampleMean x (range n) ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, card_range, nsmul_eq_mul]
          ring
  rw [empiricalVar, this, ← hsum]
  field_simp
  ring

/-- Sample variances converge once the sample means and the running means of squares do. -/
theorem tendsto_empiricalVar {x : ℕ → ℝ} {a b : ℝ}
    (hm : Tendsto (fun n : ℕ => sampleMean x (range n)) atTop (𝓝 a))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ^ 2) atTop (𝓝 b)) :
    Tendsto (empiricalVar x) atTop (𝓝 (b - a ^ 2)) := by
  refine (hsq.sub (hm.pow 2)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [empiricalVar_eq hn]

/-- If the running means of squares converge, then `x n ² / (n + 1) → 0`. -/
private theorem tendsto_sq_div_succ {x : ℕ → ℝ} {a : ℝ}
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ^ 2) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => x n ^ 2 / (n + 1)) atTop (𝓝 0) := by
  set B : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ^ 2
  have hB1 : Tendsto (fun n : ℕ => B (n + 1)) atTop (𝓝 a) := hsq.comp (tendsto_add_atTop_nat 1)
  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hlim := hB1.sub (hfrac.mul hsq)
  rw [one_mul, sub_self] at hlim
  refine hlim.congr' (Eventually.of_forall fun n => ?_)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [B, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- If `x n ² / (n + 1) → 0` then, for every `δ > 0`, eventually all of `x 0, …, x (n - 1)`
satisfy `x i ² ≤ δ n`. -/
private theorem eventually_forall_sq_le {x : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => x n ^ 2 / (n + 1)) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ i < n, x i ^ 2 ≤ δ * n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (ge_mem_nhds (half_pos hδ)))
  set C := ∑ j ∈ range N, x j ^ 2
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (C / δ)]
    with n hn i hi
  by_cases hiN : N ≤ i
  · have h1 := hN i hiN
    have hi1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  · have h1 : x i ^ 2 ≤ C :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _)
        (mem_range.2 (not_le.1 hiN))
    rw [div_le_iff₀ hδ] at hn
    linarith

/-- **The data Lindeberg condition from convergent first and second running means.** If the
sample means converge and the running means of squares converge, then the centred data
satisfy the Lindeberg condition of `tendstoInDistribution_bootMean`; in fact the truncated sums
are eventually `0`, because `max_{i<n} |x i - x̄ₙ| = o(√n)`. -/
theorem lindeberg_of_tendsto_sampleMean {x : ℕ → ℝ} {θ a : ℝ}
    (hθ : Tendsto (fun n : ℕ => sampleMean x (range n)) atTop (𝓝 θ))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ^ 2) atTop (𝓝 a))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |x i - sampleMean x (range n)| then (x i - sampleMean x (range n)) ^ 2 else 0)
      atTop (𝓝 0) := by
  have hε2 : 0 < (ε / 2) ^ 2 := by positivity
  have hsqrt : Tendsto (fun n : ℕ => ε / 2 * √(n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (half_pos hε)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_forall_sq_le (tendsto_sq_div_succ hsq) hε2,
    hθ.abs.eventually (ge_mem_nhds (lt_add_one |θ|)),
    hsqrt.eventually_ge_atTop (|θ| + 1)] with n hx hm hs
  symm
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i hi => ?_)
  have hxi : |x i| ≤ ε / 2 * √(n : ℝ) := by
    have := Real.abs_le_sqrt (hx i (mem_range.1 hi))
    rwa [Real.sqrt_mul (le_of_lt hε2), Real.sqrt_sq (by positivity)] at this
  have hle : |x i - sampleMean x (range n)| ≤ ε * √(n : ℝ) :=
    calc |x i - sampleMean x (range n)| ≤ |x i| + |sampleMean x (range n)| := abs_sub _ _
      _ ≤ ε / 2 * √(n : ℝ) + ε / 2 * √(n : ℝ) := add_le_add hxi (hm.trans hs)
      _ = ε * √(n : ℝ) := by ring
  simp [not_lt.2 hle]

section IID

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For iid square-integrable data, almost every sample path has convergent sample means,
convergent running means of squares, and plug-in variances converging to the variance. -/
private theorem ae_data_limits (X : ℕ → Ω → ℝ) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => sampleMean (fun i => X i ω) (range n)) atTop (𝓝 P[X 0]) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω ^ 2) atTop
        (𝓝 P[fun ω => X 0 ω ^ 2]) ∧
      Tendsto (empiricalVar (fun i => X i ω)) atTop (𝓝 (variance (X 0) P)) := by
  have hmean := strong_law_ae_real X (hint.integrable one_le_two) hindep hident
  have hsq := strong_law_ae_real (fun i ω => X i ω ^ 2) hint.integrable_sq
    (fun i j hij => (hindep hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
    (fun i => (hident i).comp (measurable_id.pow_const 2))
  filter_upwards [hmean, hsq] with ω h1 h2
  have h1' : Tendsto (fun n : ℕ => sampleMean (fun i => X i ω) (range n)) atTop (𝓝 P[X 0]) :=
    h1.congr fun n => by simp [sampleMean_range, div_eq_inv_mul]
  have h2' : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω ^ 2) atTop
      (𝓝 P[fun ω => X 0 ω ^ 2]) :=
    h2.congr fun n => by simp [div_eq_inv_mul]
  refine ⟨h1', h2', ?_⟩
  rw [variance_eq_sub hint]
  exact tendsto_empiricalVar h1' h2'

/-- **Almost-sure bootstrap validity for the mean (Bickel–Freedman 1981).** Let `X 0, X 1, …`
be iid (pairwise independence suffices) square-integrable real observations with positive
variance `σ²`. Then for `P`-almost every realised data sequence `x = (X i ω)ᵢ`, the
conditional law of the bootstrap statistic `√n (x̄*ₙ - x̄ₙ)` given the data converges weakly to
`N(0, σ²)`, the limit law of `√n (x̄ₙ - E X)`. -/
theorem ae_tendstoInDistribution_bootMean (X : ℕ → Ω → ℝ) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hvar : variance (X 0) P ≠ 0) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) * (bootMean n ω' - sampleMean (fun i => X i ω) (range n))) atTop
      (id : ℝ → ℝ) (fun _ => world (fun i => X i ω))
      (gaussianReal 0 (variance (X 0) P).toNNReal) := by
  have hv : (variance (X 0) P).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)
  filter_upwards [ae_data_limits X hint hindep hident] with ω ⟨h1, h2, h3⟩
  refine tendstoInDistribution_bootMean _ hv ?_ (lindeberg_of_tendsto_sampleMean h1 h2)
  rwa [Real.coe_toNNReal _ (variance_nonneg _ _)]

/-- **Almost-sure bootstrap validity for a smooth function of the mean.** Let `X 0, X 1, …`
be iid (pairwise independence suffices) square-integrable real observations with mean `μ₀`
and positive variance `σ²`, and let `g` be measurable and strictly differentiable at `μ₀` with
derivative `g'`. Then for `P`-almost every realised data sequence, the conditional law of the
bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` converges weakly to `N(0, g'² σ²)`, the limit law of
`√n (g(x̄ₙ) - g(μ₀))` given by the delta method. -/
theorem ae_tendstoInDistribution_bootstrap_of_hasStrictDerivAt (X : ℕ → Ω → ℝ)
    (hint : MemLp (X 0) 2 P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hvar : variance (X 0) P ≠ 0)
    {g : ℝ → ℝ} {g' : ℝ} (hg : HasStrictDerivAt g g' P[X 0]) (hgm : Measurable g) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) *
        (g (bootMean n ω') - g (sampleMean (fun i => X i ω) (range n)))) atTop
      (id : ℝ → ℝ) (fun _ => world (fun i => X i ω))
      (gaussianReal 0 (‖g'‖₊ ^ 2 * (variance (X 0) P).toNNReal)) := by
  have hv : (variance (X 0) P).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)
  filter_upwards [ae_data_limits X hint hindep hident] with ω ⟨h1, h2, h3⟩
  refine tendstoInDistribution_bootstrap_of_hasStrictDerivAt _ hv ?_
    (lindeberg_of_tendsto_sampleMean h1 h2) h1 hg hgm
  rwa [Real.coe_toNNReal _ (variance_nonneg _ _)]

end IID

/-! ### Finite-dimensional observations -/

section Vector

/-- Transfer convergence in distribution along a measure-preserving map. -/
private theorem tendstoInDistribution_comp_of_map_eq {Ω₁ Ω₂ Ω' : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω'] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {μ' : Measure Ω'} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ'] {Φ : Ω₁ → Ω₂} (hΦ : Measurable Φ) (hmap : μ₁.map Φ = μ₂)
    {Y : ℕ → Ω₂ → ℝ} (hY : ∀ n, Measurable (Y n)) {Z : Ω' → ℝ}
    (h : TendstoInDistribution Y atTop Z (fun _ => μ₂) μ') :
    TendstoInDistribution (fun n ω => Y n (Φ ω)) atTop Z (fun _ => μ₁) μ' := by
  refine ⟨fun n => ((hY n).comp hΦ).aemeasurable, h.aemeasurable_limit, ?_⟩
  refine h.tendsto.congr fun n => Subtype.ext ?_
  change μ₂.map (Y n) = μ₁.map (Y n ∘ Φ)
  rw [← hmap, Measure.map_map (hY n) hΦ]

/-- Replace the limit variable of a convergence in distribution by one with the same law. -/
private theorem tendstoInDistribution_of_map_limit_eq {Ω₁ Ω₁' Ω₂' : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₁'] [MeasurableSpace Ω₂'] {μ₁ : Measure Ω₁} {ν₁ : Measure Ω₁'}
    {ν₂ : Measure Ω₂'} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] {Y : ℕ → Ω₁ → ℝ} {Z₁ : Ω₁' → ℝ} {Z₂ : Ω₂' → ℝ}
    (h : TendstoInDistribution Y atTop Z₁ (fun _ => μ₁) ν₁) (hZ₂ : AEMeasurable Z₂ ν₂)
    (heq : ν₁.map Z₁ = ν₂.map Z₂) :
    TendstoInDistribution Y atTop Z₂ (fun _ => μ₁) ν₂ := by
  refine ⟨h.forall_aemeasurable, hZ₂, ?_⟩
  have hlim : (⟨ν₂.map Z₂, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨ν₁.map Z₁, inferInstance⟩ := Subtype.ext heq.symm
  rw [hlim]
  exact h.tendsto

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The **sample mean** `(1 / n) ∑_{i < n} x i` of `E`-valued observations. -/
noncomputable def sampleMeanVec (x : ℕ → E) (n : ℕ) : E := (n : ℝ)⁻¹ • ∑ i ∈ range n, x i

/-- The **bootstrap sample mean** of `E`-valued observations at sample size `n`. -/
noncomputable def bootMeanVec (n : ℕ) (ω : ℕ → ℕ → E) : E := (n : ℝ)⁻¹ • ∑ k ∈ range n, ω n k

/-- The vector bootstrap mean is measurable. -/
theorem measurable_bootMeanVec (n : ℕ) : Measurable (bootMeanVec (E := E) n) := by
  unfold bootMeanVec; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Projections of the vector sample mean are sample means of the projected data. -/
theorem inner_sampleMeanVec (x : ℕ → E) (n : ℕ) (t : E) :
    ⟪sampleMeanVec x n, t⟫ = sampleMean (fun i => ⟪x i, t⟫) (range n) := by
  simp [sampleMeanVec, sampleMean_range, real_inner_smul_left, sum_inner]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Projections of the vector bootstrap mean are bootstrap means of the projected draws. -/
theorem inner_bootMeanVec (n : ℕ) (ω : ℕ → ℕ → E) (t : E) :
    ⟪bootMeanVec n ω, t⟫ = bootMean n (fun n k => ⟪ω n k, t⟫) := by
  simp [bootMeanVec, bootMean, real_inner_smul_left, sum_inner]

/-- **Conditional multivariate CLT for the bootstrap mean.**

Fix `E`-valued data `x` (finite-dimensional real inner product space). Let `Z` be a random
vector whose projections `⟪Z, t⟫` are `N(0, v t)`, and assume the covariance is nonsingular
(`v t ≠ 0` for `t ≠ 0`). If, for every direction `t`, the plug-in variances of the projected
data `⟪x i, t⟫` converge to `v t` and the projected data satisfy the Lindeberg condition, then,
conditionally on the data, `√n (x̄*ₙ - x̄ₙ)` converges in distribution to `Z`.

Each projection is the scalar bootstrap of the projected data (`map_world`), so the scalar
conditional Lindeberg CLT `tendstoInDistribution_bootMean` applies; the Cramér–Wold device
(`TendstoInDistribution.of_inner`) assembles the directions. -/
theorem tendstoInDistribution_bootMeanVec (x : ℕ → E) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (v : E → ℝ≥0) (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫) (gaussianReal 0 (v t)) μ')
    (hv : ∀ t, t ≠ 0 → v t ≠ 0)
    (hvar : ∀ t, Tendsto (empiricalVar (fun i => ⟪x i, t⟫)) atTop (𝓝 (v t)))
    (hLind : ∀ t, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |⟪x i, t⟫ - sampleMean (fun i => ⟪x i, t⟫) (range n)|
        then (⟪x i, t⟫ - sampleMean (fun i => ⟪x i, t⟫) (range n)) ^ 2 else 0) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (bootMeanVec n ω - sampleMeanVec x n)) atTop Z
      (fun _ => world x) μ' := by
  refine TendstoInDistribution.of_inner hZ (fun n => ((measurable_const.smul
    ((measurable_bootMeanVec n).sub measurable_const))).aemeasurable) fun t => ?_
  have hinner : Measurable fun y : E => ⟪y, t⟫ := (continuous_id.inner continuous_const).measurable
  by_cases ht : t = 0
  · subst ht
    have hZmeas : AEMeasurable (fun ω => ⟪Z ω, (0 : E)⟫) μ' := by simp
    refine ⟨fun n => by simp, hZmeas, tendsto_const_nhds.congr fun n => Subtype.ext ?_⟩
    simp [Measure.map_const]
  -- the scalar bootstrap of the projected data
  have hs := tendstoInDistribution_bootMean (fun i => ⟪x i, t⟫) (hv t ht) (hvar t) (hLind t)
  have hΦ : Measurable fun (ω : ℕ → ℕ → E) (n k : ℕ) => ⟪ω n k, t⟫ := by fun_prop
  have hY : ∀ n : ℕ, Measurable fun ω : ℕ → ℕ → ℝ =>
      √(n : ℝ) * (bootMean n ω - sampleMean (fun i => ⟪x i, t⟫) (range n)) := fun n =>
    measurable_const.mul ((measurable_bootMean n).sub measurable_const)
  have h1 := tendstoInDistribution_comp_of_map_eq hΦ (map_world x hinner (inner_zero_left _))
    hY hs
  have h2 := tendstoInDistribution_of_map_limit_eq (ν₂ := μ') (Z₂ := fun ω => ⟪Z ω, t⟫) h1
    (hinner.comp_aemeasurable hZ) (by rw [Measure.map_id, (hZlaw t).map_eq])
  refine h2.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
  simp [real_inner_smul_left, inner_sub_left, inner_bootMeanVec, inner_sampleMeanVec]

/-- **Bootstrap validity for smooth finite-dimensional statistics (deterministic data).**

Under the hypotheses of `tendstoInDistribution_bootMeanVec`, if the sample means converge to
`θ` and `g : E → F` is strictly differentiable at `θ` with derivative `L`, then, conditionally
on the data, `√n (g(x̄*ₙ) - g(x̄ₙ))` converges in distribution to `L Z`; this is the delta-method
limit of `√n (g(x̄ₙ) - g(θ))` when `√n (x̄ₙ - θ) →ᵈ Z`. -/
theorem tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F] [MeasurableSpace F]
    [BorelSpace F] (x : ℕ → E) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (v : E → ℝ≥0) (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫) (gaussianReal 0 (v t)) μ')
    (hv : ∀ t, t ≠ 0 → v t ≠ 0)
    (hvar : ∀ t, Tendsto (empiricalVar (fun i => ⟪x i, t⟫)) atTop (𝓝 (v t)))
    (hLind : ∀ t, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |⟪x i, t⟫ - sampleMean (fun i => ⟪x i, t⟫) (range n)|
        then (⟪x i, t⟫ - sampleMean (fun i => ⟪x i, t⟫) (range n)) ^ 2 else 0) atTop (𝓝 0))
    {θ : E} (hθ : Tendsto (sampleMeanVec x) atTop (𝓝 θ)) {g : E → F} {L : E →L[ℝ] F}
    (hg : HasStrictFDerivAt g L θ) (hgm : Measurable g) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (g (bootMeanVec n ω) - g (sampleMeanVec x n))) atTop
      (fun ω => L (Z ω)) (fun _ => world x) μ' :=
  TendstoInDistribution.delta_method_of_hasStrictFDerivAt
    (tendstoInDistribution_bootMeanVec x hZ v hZlaw hv hvar hLind)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hθ hg
    (fun n => (measurable_bootMeanVec n).aemeasurable)
    (fun n => (hgm.comp (measurable_bootMeanVec n)).aemeasurable)

/-- Running means of a finite linear combination of statistics converge to the same linear
combination of the limits. -/
private theorem tendsto_runningMean_of_eq_sum {β ι : Type*} {x : ℕ → β} {f : β → ℝ}
    (s : Finset ι) (a : ι → ℝ) (h : ι → β → ℝ) (hf : ∀ y, f y = ∑ p ∈ s, a p * h p y)
    (L : ι → ℝ)
    (hL : ∀ p ∈ s, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, h p (x i)) atTop (𝓝 (L p))) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, f (x i)) atTop
      (𝓝 (∑ p ∈ s, a p * L p)) := by
  refine (tendsto_finsetSum s fun p hp => (hL p hp).const_mul (a p)).congr fun n => ?_
  simp_rw [hf, Finset.sum_comm (s := range n), Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by ring

section IIDVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For iid square-integrable `E`-valued data, almost every sample path has convergent sample
means and, simultaneously in every direction `t`, convergent running means of `⟪x i, t⟫²`.
The simultaneity over the uncountably many directions comes from finitely many strong laws for
the coordinate products in an orthonormal basis. -/
private theorem ae_vec_data_limits (X : ℕ → Ω → E) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (sampleMeanVec (fun i => X i ω)) atTop (𝓝 P[X 0]) ∧
      ∀ t : E, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪X i ω, t⟫ ^ 2) atTop
        (𝓝 P[fun ω => ⟪X 0 ω, t⟫ ^ 2]) := by
  set b := stdOrthonormalBasis ℝ E
  set Q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → E → ℝ :=
    fun p y => ⟪y, b p.1⟫ * ⟪y, b p.2⟫ with hQ
  have hQm : ∀ p, Measurable (Q p) := fun p => by
    simp only [hQ]
    exact ((continuous_id.inner continuous_const).mul
      (continuous_id.inner continuous_const)).measurable
  have hQint : ∀ p, Integrable (fun ω => Q p (X 0 ω)) P := fun p =>
    (hint.inner_const (b p.1)).integrable_mul (hint.inner_const (b p.2))
  have hQlaw : ∀ p, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, Q p (X i ω))
      atTop (𝓝 P[fun ω => Q p (X 0 ω)]) := fun p =>
    (strong_law_ae_real (fun i ω => Q p (X i ω)) (hQint p)
      (fun i j hij => (hindep hij).comp (hQm p) (hQm p))
      (fun i => (hident i).comp (hQm p))).mono fun ω h =>
      h.congr fun n => by simp [div_eq_inv_mul]
  filter_upwards [strong_law_ae X (hint.integrable one_le_two) hindep hident,
    ae_all_iff.2 hQlaw] with ω hmean hQω
  refine ⟨hmean, fun t => ?_⟩
  set a : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
    fun p => ⟪b p.1, t⟫ * ⟪b p.2, t⟫
  have hexp : ∀ y : E, ⟪y, t⟫ ^ 2 = ∑ p ∈ Finset.univ, a p * Q p y := by
    intro y
    rw [← b.sum_inner_mul_inner y t, sq, Finset.sum_mul_sum, ← Finset.univ_product_univ,
      Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      simp only [a, hQ]; ring
  have hlim : P[fun ω => ⟪X 0 ω, t⟫ ^ 2] = ∑ p ∈ Finset.univ, a p * P[fun ω => Q p (X 0 ω)] := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun p _ => (hQint p).const_mul (a p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  rw [hlim]
  exact tendsto_runningMean_of_eq_sum (x := fun i => X i ω) Finset.univ a Q hexp _
    fun p _ => hQω p

/-- **Almost-sure bootstrap validity for the multivariate mean.** Let `X 0, X 1, …` be iid
(pairwise independence suffices) square-integrable random vectors in a finite-dimensional real
inner product space `E` with nonsingular covariance (`Var ⟪X 0, t⟫ ≠ 0` for `t ≠ 0`), and let
`Z` be a centred Gaussian vector with the same covariance (`⟪Z, t⟫ ~ N(0, Var ⟪X 0, t⟫)`). Then
for `P`-almost every realised data sequence, the conditional law of `√n (x̄*ₙ - x̄ₙ)` given the
data converges weakly to the law of `Z`, the multivariate CLT limit of `√n (x̄ₙ - E X)`. -/
theorem ae_tendstoInDistribution_bootMeanVec (X : ℕ → Ω → E) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (Var[fun ω => ⟪X 0 ω, t⟫; P]).toNNReal) μ')
    (hnondeg : ∀ t, t ≠ 0 → Var[fun ω => ⟪X 0 ω, t⟫; P] ≠ 0) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) • (bootMeanVec n ω' - sampleMeanVec (fun i => X i ω) n))
      atTop Z (fun _ => world (fun i => X i ω)) μ' := by
  filter_upwards [ae_vec_data_limits X hint hindep hident] with ω ⟨hmean, hsq⟩
  have hm : ∀ t : E, Tendsto (fun n : ℕ => sampleMean (fun i => ⟪X i ω, t⟫) (range n)) atTop
      (𝓝 P[fun ω => ⟪X 0 ω, t⟫]) := fun t => by
    have hc : Continuous fun y : E => ⟪y, t⟫ := continuous_id.inner continuous_const
    have h := (hc.tendsto _).comp hmean
    change Tendsto _ atTop (𝓝 (∫ x, ⟪X 0 x, t⟫ ∂P))
    have hint1 : ∫ ω, ⟪X 0 ω, t⟫ ∂P = ⟪P[X 0], t⟫ := by
      simp_rw [real_inner_comm t]
      exact integral_inner (hint.integrable one_le_two) t
    rw [hint1]
    exact h.congr fun n => by simp [inner_sampleMeanVec]
  refine tendstoInDistribution_bootMeanVec _ hZ _ hZlaw (fun t ht => ?_) (fun t => ?_)
    (fun t => lindeberg_of_tendsto_sampleMean (hm t) (hsq t))
  · rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm (hnondeg t ht))
  · rw [Real.coe_toNNReal _ (variance_nonneg _ _), variance_eq_sub (hint.inner_const t)]
    exact tendsto_empiricalVar (hm t) (hsq t)

/-- **Almost-sure bootstrap validity for smooth finite-dimensional statistics.** Under the
hypotheses of `ae_tendstoInDistribution_bootMeanVec`, let `g : E → F` be measurable and
strictly differentiable at the mean `E X` with derivative `L`. Then for `P`-almost every
realised data sequence, the conditional law of `√n (g(x̄*ₙ) - g(x̄ₙ))` given the data converges
weakly to the law of `L Z`, the delta-method limit of `√n (g(x̄ₙ) - g(E X))`. -/
theorem ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F] [MeasurableSpace F]
    [BorelSpace F] (X : ℕ → Ω → E) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (Var[fun ω => ⟪X 0 ω, t⟫; P]).toNNReal) μ')
    (hnondeg : ∀ t, t ≠ 0 → Var[fun ω => ⟪X 0 ω, t⟫; P] ≠ 0)
    {g : E → F} {L : E →L[ℝ] F} (hg : HasStrictFDerivAt g L P[X 0]) (hgm : Measurable g) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) •
        (g (bootMeanVec n ω') - g (sampleMeanVec (fun i => X i ω) n)))
      atTop (fun ω' => L (Z ω')) (fun _ => world (fun i => X i ω)) μ' := by
  filter_upwards [ae_tendstoInDistribution_bootMeanVec X hint hindep hident hZ hZlaw hnondeg,
    ae_vec_data_limits X hint hindep hident] with ω h ⟨hmean, _⟩
  exact TendstoInDistribution.delta_method_of_hasStrictFDerivAt h
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hmean hg
    (fun n => (measurable_bootMeanVec n).aemeasurable)
    (fun n => (hgm.comp (measurable_bootMeanVec n)).aemeasurable)

end IIDVector

end Vector

end ProbabilityTheory.Bootstrap
