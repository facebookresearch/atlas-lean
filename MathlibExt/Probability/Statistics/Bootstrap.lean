/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Resampling.BootstrapMeanCLT
public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Statistics.DeltaMethod
public import MathlibExt.Probability.Statistics.MultivariateCLT
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
theorems). The empirical laws reuse `ProbabilityTheory.empiricalLaw`, with the historical
point-mass-at-zero convention for the empty row. `map_world_bootstrapMeasure` bridges `world`
to the canonical resampling coupling by replacing only row zero. All scalar CLTs use
`ProbabilityTheory.tendstoInDistribution_sum_bootstrapRow`; the vector and almost-sure
results extend that canonical machinery.

## The conditional triangular-array CLT

The resampled values form a triangular array whose row-`n` law changes with `n`, so the iid
CLT does not apply to them, and neither does an iid delta method for the data. The proof
applies the triangular-array Lindeberg–Feller theorem `lindeberg_feller_clt_triangular` to the
centred bootstrap array `(ω n k - x̄ₙ) / √n`. Its Lindeberg condition is a condition on the data,

  `(1 / n) ∑_{i<n} (x i - x̄ₙ)² 𝟙{|x i - x̄ₙ| > ε √n} → 0` for every `ε > 0`,

which, with `empiricalVar x n → σ² > 0`, gives the conditional CLT `tendstoInDistribution_bootMean`.
When `σ² = 0`, Chebyshev's inequality under `world x` gives the point mass at `0`
(`gaussianReal 0 0`) instead, so no positivity hypothesis is needed and a singular covariance is
allowed in the vector case. For iid square-integrable data both conditions hold almost surely:
the strong law for `X` and `X²` gives the variance limit and `max_{i<n} |X i| = o(√n)`
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
  iid square-integrable real data.
* `tendstoInDistribution_bootMeanVec`,
  `tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt`: the same for `E`-valued data in a
  finite-dimensional inner product space, fixed data.
* `bootstrap_consistent_mean`: the sampling law and, almost surely, the bootstrap law of the
  scaled multivariate mean share the Gaussian limit.
* `ae_tendstoInDistribution_bootMeanVec`,
  `ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt`: almost-sure bootstrap validity
  for iid square-integrable `E`-valued data (singular covariance allowed) and smooth
  `g : E → F`.

## Scope

* Only iid observations and statistics `g(x̄)` with `g` strictly differentiable at the mean.
  Nothing here concerns dependent data, high-dimensional (`dim → ∞`) settings, the
  `m`-out-of-`n` bootstrap, or coverage of bootstrap confidence intervals.
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
  if n = 0 then Measure.dirac 0 else empiricalLaw x n

/-- The positive rows use the canonical empirical law; only row zero has a different convention. -/
theorem empirical_eq_empiricalLaw {x : ℕ → α} {n : ℕ} (hn : n ≠ 0) :
    empirical x n = empiricalLaw x n := by
  simp [empirical, hn]

/-- For `n ≠ 0` the empirical distribution is the average of the point masses. -/
theorem empirical_of_ne_zero {x : ℕ → α} {n : ℕ} (hn : n ≠ 0) :
    empirical x n = (n : ℝ≥0∞)⁻¹ • ∑ i ∈ range n, Measure.dirac (x i) := by
  rw [empirical_eq_empiricalLaw hn, empiricalLaw_eq]

/-- The empirical distribution is a probability measure. -/
instance isProbabilityMeasure_empirical (x : ℕ → α) (n : ℕ) :
    IsProbabilityMeasure (empirical x n) := by
  by_cases hn : n = 0
  · simp only [empirical, hn, ite_true]; infer_instance
  · rw [empirical_eq_empiricalLaw hn]
    exact isProbabilityMeasure_empiricalLaw x (Nat.pos_of_ne_zero hn)

/-- Every function is integrable for the empirical distribution (finitely many atoms). -/
theorem integrable_empirical [MeasurableSingletonClass α] (x : ℕ → α) (n : ℕ) (f : α → ℝ) :
    Integrable f (empirical x n) := by
  by_cases hn : n = 0
  · simp only [empirical, hn, ite_true]
    exact integrable_dirac enorm_lt_top
  · rw [empirical_eq_empiricalLaw hn]
    exact integrable_empiricalLaw x n f

/-- Integrals against the empirical distribution are sample averages. -/
theorem integral_empirical [MeasurableSingletonClass α] {x : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (f : α → ℝ) :
    ∫ y, f y ∂empirical x n = (n : ℝ)⁻¹ * ∑ i ∈ range n, f (x i) := by
  rw [empirical_eq_empiricalLaw hn, integral_empiricalLaw]

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

/-- Replacing the unused zero row by `x 0` gives the canonical bootstrap coupling.
Every positive row is unchanged, so statistics from those rows have exactly the same laws. -/
theorem map_world_bootstrapMeasure (x : ℕ → α) :
    (world x).map (fun ω n k => if n = 0 then x 0 else ω n k) = bootstrapMeasure x := by
  unfold world bootstrapMeasure
  rw [Measure.infinitePi_map_pi
    (μ := fun n => Measure.infinitePi fun _ : ℕ => empirical x n)
    (f := fun n (row : ℕ → α) k => if n = 0 then x 0 else row k) (fun _ => by fun_prop)]
  congr 1
  funext n
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => empirical x n)
    (f := fun _ y => if n = 0 then x 0 else y) (fun _ => by fun_prop)]
  congr 1
  funext k
  by_cases hn : n = 0
  · subst n
    simp [Measure.map_const, empiricalLaw_eq]
  · simp [hn, empirical_eq_empiricalLaw hn, max_eq_left (Nat.one_le_iff_ne_zero.2 hn)]

end Generic

/-! Throughout, `x̄ₙ` is `sampleMean x (range n)`, reusing
`MathlibExt.Probability.Causality.sampleMean`. -/

/-- The sample mean `x̄ₙ = sampleMean x (range n)` of the first `n` observations as a scaled
sum. -/
theorem sampleMean_range (x : ℕ → ℝ) (n : ℕ) :
    sampleMean x (range n) = (n : ℝ)⁻¹ * ∑ i ∈ range n, x i := by
  simp [sampleMean, div_eq_inv_mul]

/-- The existing finite-set mean agrees with the canonical resampling mean. -/
theorem sampleMean_eq_empiricalMean (x : ℕ → ℝ) (n : ℕ) :
    sampleMean x (range n) = empiricalMean x n := by
  rw [sampleMean_range, empiricalMean_eq]

/-- The **plug-in sample variance** `(1 / n) ∑_{i < n} (x i - x̄ₙ)²`, i.e. the variance of
the empirical distribution `empirical x n`. Its divisor is `n`, unlike the unbiased
`MathlibExt.Probability.Causality.sampleVar` (divisor `n - 1`); the bootstrap resamples from
the empirical distribution, so the plug-in variance is the one that appears. -/
noncomputable def empiricalVar (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, (x i - sampleMean x (range n)) ^ 2

/-- The **bootstrap sample mean** at sample size `n`: the average of the resample
`ω n 0, …, ω n (n - 1)`. -/
noncomputable def bootMean (n : ℕ) (ω : ℕ → ℕ → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ k ∈ range n, ω n k

/-- The bootstrap statistic is the canonical empirical mean of the resampled row. -/
theorem bootMean_eq_empiricalMean (n : ℕ) (ω : ℕ → ℕ → ℝ) :
    bootMean n ω = empiricalMean (ω n) n := by
  rw [bootMean, empiricalMean_eq]

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

/-- **Conditional Lindeberg CLT for the bootstrap mean (Bickel–Freedman).**

Fix a data sequence `x`. Suppose the plug-in sample variances `empiricalVar x n` converge to
`σ² ≥ 0`, and the centred data satisfy the Lindeberg condition
`(1 / n) ∑_{i<n} (x i - x̄ₙ)² 𝟙{|x i - x̄ₙ| > ε √n} → 0` for every `ε > 0`. Then, under the
bootstrap world (i.e. conditionally on the data), `√n (x̄*ₙ - x̄ₙ)` converges in distribution to
`N(0, σ²)`; for `σ² = 0` this is the point mass at `0`, obtained from Chebyshev's inequality
(the Lindeberg hypothesis is then not used).

For `σ² > 0` the proof applies the triangular-array Lindeberg–Feller theorem
`lindeberg_feller_clt_triangular` to the bootstrap array `(ω n k - x̄ₙ) / √n`, `k < n`, whose
rows are iid from the centred empirical distribution. The data Lindeberg hypothesis is exactly
the Lindeberg condition of that array; it does not follow from the variance condition alone,
which is why an iid central limit theorem for the data cannot replace it. -/
theorem tendstoInDistribution_bootMean (x : ℕ → ℝ) {v : ℝ≥0}
    (hvar : Tendsto (empiricalVar x) atTop (𝓝 v))
    (hLind : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |x i - sampleMean x (range n)| then (x i - sampleMean x (range n)) ^ 2
        else 0) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (bootMean n ω - sampleMean x (range n))) atTop
      (id : ℝ → ℝ) (fun _ => world x) (gaussianReal 0 v) := by
  have hvar' : Tendsto (fun n => ∑ k ∈ range n,
      ∫ ω, (bootstrapRow x n k ω) ^ 2 ∂bootstrapMeasure x) atTop (𝓝 (v : ℝ)) := by
    refine hvar.congr fun n => ?_
    rw [sum_integral_bootstrapRow_sq, ← sampleMean_eq_empiricalMean]
    rfl
  have hLind' := lindebergConditionTriangular_bootstrapRow_of_data x
    (by simpa only [← sampleMean_eq_empiricalMean] using hLind)
  have hc := tendstoInDistribution_sum_bootstrapRow x hvar' hLind'
  have h := tendstoInDistribution_comp_of_map_eq
    (Φ := fun (ω : ℕ → ℕ → ℝ) n k => if n = 0 then x 0 else ω n k) (by fun_prop)
    (map_world_bootstrapMeasure x)
    (fun n => Finset.measurable_sum _ fun k _ => measurable_bootstrapRow x n k) hc
  refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, bootstrapRow, ← sampleMean_eq_empiricalMean, sqrt_mul_bootMean_sub]

end ProbabilityTheory.Bootstrap


namespace ProbabilityTheory.Bootstrap

/-- **Bootstrap validity for a smooth function of the mean (deterministic data).**

Under the hypotheses of `tendstoInDistribution_bootMean`, if moreover the sample means converge
to `θ` and `g` is strictly differentiable at `θ` with derivative `g'`, then, conditionally on
the data, the bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` converges in distribution to
`N(0, g'² v)`, the same limit as the sampling distribution of `√n (g(x̄ₙ) - g(θ))`. -/
theorem tendstoInDistribution_bootstrap_of_hasStrictDerivAt (x : ℕ → ℝ) {v : ℝ≥0}
    (hvar : Tendsto (empiricalVar x) atTop (𝓝 v))
    (hLind : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |x i - sampleMean x (range n)| then (x i - sampleMean x (range n)) ^ 2 else 0)
      atTop (𝓝 0))
    {θ : ℝ} (hθ : Tendsto (fun n : ℕ => sampleMean x (range n)) atTop (𝓝 θ)) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasStrictDerivAt g g' θ) (hgm : Measurable g) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (g (bootMean n ω) - g (sampleMean x (range n)))) atTop
      (id : ℝ → ℝ) (fun _ => world x) (gaussianReal 0 (‖g'‖₊ ^ 2 * v)) := by
  have h := tendstoInDistribution_bootMean x hvar hLind
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
be iid (pairwise independence suffices) square-integrable real observations with variance
`σ²`. Then for `P`-almost every realised data sequence `x = (X i ω)ᵢ`, the
conditional law of the bootstrap statistic `√n (x̄*ₙ - x̄ₙ)` given the data converges weakly to
`N(0, σ²)`, the limit law of `√n (x̄ₙ - E X)`. -/
theorem ae_tendstoInDistribution_bootMean (X : ℕ → Ω → ℝ) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) * (bootMean n ω' - sampleMean (fun i => X i ω) (range n))) atTop
      (id : ℝ → ℝ) (fun _ => world (fun i => X i ω))
      (gaussianReal 0 (variance (X 0) P).toNNReal) := by
  filter_upwards [ae_data_limits X hint hindep hident] with ω ⟨h1, h2, h3⟩
  refine tendstoInDistribution_bootMean _ ?_ (lindeberg_of_tendsto_sampleMean h1 h2)
  rwa [Real.coe_toNNReal _ (variance_nonneg _ _)]

/-- **Almost-sure bootstrap validity for a smooth function of the mean.** Let `X 0, X 1, …`
be iid (pairwise independence suffices) square-integrable real observations with mean `μ₀`
and variance `σ²`, and let `g` be measurable and strictly differentiable at `μ₀` with
derivative `g'`. Then for `P`-almost every realised data sequence, the conditional law of the
bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` converges weakly to `N(0, g'² σ²)`, the limit law of
`√n (g(x̄ₙ) - g(μ₀))` given by the delta method. -/
theorem ae_tendstoInDistribution_bootstrap_of_hasStrictDerivAt (X : ℕ → Ω → ℝ)
    (hint : MemLp (X 0) 2 P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} {g' : ℝ} (hg : HasStrictDerivAt g g' P[X 0]) (hgm : Measurable g) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) *
        (g (bootMean n ω') - g (sampleMean (fun i => X i ω) (range n)))) atTop
      (id : ℝ → ℝ) (fun _ => world (fun i => X i ω))
      (gaussianReal 0 (‖g'‖₊ ^ 2 * (variance (X 0) P).toNNReal)) := by
  filter_upwards [ae_data_limits X hint hindep hident] with ω ⟨h1, h2, h3⟩
  refine tendstoInDistribution_bootstrap_of_hasStrictDerivAt _ ?_
    (lindeberg_of_tendsto_sampleMean h1 h2) h1 hg hgm
  rwa [Real.coe_toNNReal _ (variance_nonneg _ _)]

end IID

/-! ### Finite-dimensional observations -/

section Vector

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

Fix `E`-valued data `x` (finite-dimensional real inner product space). Let `Z` be a random vector
whose projections `⟪Z, t⟫` are `N(0, v t)`; the covariance may be singular (`v t = 0` gives the
point mass at `0`). If, for every direction `t`, the plug-in variances of the projected data
`⟪x i, t⟫` converge to `v t` and the projected data satisfy the Lindeberg condition, then,
conditionally on the data, `√n (x̄*ₙ - x̄ₙ)` converges in distribution to `Z`.

Each projection is the scalar bootstrap of the projected data (`map_world`), so the scalar
conditional Lindeberg CLT `tendstoInDistribution_bootMean` applies; the Cramér–Wold device
(`TendstoInDistribution.of_inner`) assembles the directions. -/
theorem tendstoInDistribution_bootMeanVec (x : ℕ → E) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (v : E → ℝ≥0) (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫) (gaussianReal 0 (v t)) μ')
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
  -- the scalar bootstrap of the projected data
  have hs := tendstoInDistribution_bootMean (fun i => ⟪x i, t⟫) (hvar t) (hLind t)
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
    (tendstoInDistribution_bootMeanVec x hZ v hZlaw hvar hLind)
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
inner product space `E` (the covariance may be singular), and let
`Z` be a centred Gaussian vector with the same covariance (`⟪Z, t⟫ ~ N(0, Var ⟪X 0, t⟫)`). Then
for `P`-almost every realised data sequence, the conditional law of `√n (x̄*ₙ - x̄ₙ)` given the
data converges weakly to the law of `Z`, the multivariate CLT limit of `√n (x̄ₙ - E X)`. -/
theorem ae_tendstoInDistribution_bootMeanVec (X : ℕ → Ω → E) (hint : MemLp (X 0) 2 P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (Var[fun ω => ⟪X 0 ω, t⟫; P]).toNNReal) μ') :
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
  refine tendstoInDistribution_bootMeanVec _ hZ _ hZlaw (fun t => ?_)
    (fun t => lindeberg_of_tendsto_sampleMean (hm t) (hsq t))
  rw [Real.coe_toNNReal _ (variance_nonneg _ _), variance_eq_sub (hint.inner_const t)]
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
    {g : E → F} {L : E →L[ℝ] F} (hg : HasStrictFDerivAt g L P[X 0]) (hgm : Measurable g) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) •
        (g (bootMeanVec n ω') - g (sampleMeanVec (fun i => X i ω) n)))
      atTop (fun ω' => L (Z ω')) (fun _ => world (fun i => X i ω)) μ' := by
  filter_upwards [ae_tendstoInDistribution_bootMeanVec X hint hindep hident hZ hZlaw,
    ae_vec_data_limits X hint hindep hident] with ω h ⟨hmean, _⟩
  exact TendstoInDistribution.delta_method_of_hasStrictFDerivAt h
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hmean hg
    (fun n => (measurable_bootMeanVec n).aemeasurable)
    (fun n => (hgm.comp (measurable_bootMeanVec n)).aemeasurable)

/-- **Bootstrap consistency for the multivariate mean.** For iid square-integrable random
vectors in a finite-dimensional real inner product space and a centred Gaussian `Z` with the
covariance of `X 0`, the sampling distribution of `(√n)⁻¹ • (∑_{k<n} X k - n • E X)`, which
equals `√n (x̄ₙ - E X)` (multivariate CLT, `tendstoInDistribution_inv_sqrt_smul_sum_sub`),
and, for almost every data sequence, the
conditional law of the bootstrap statistic `√n (x̄*ₙ - x̄ₙ)` have the same limit law, that of
`Z`. The covariance may be singular. -/
theorem bootstrap_consistent_mean (X : ℕ → Ω → E) (hint : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (Var[fun ω => ⟪X 0 ω, t⟫; P]).toNNReal) μ') :
    TendstoInDistribution
        (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P)) atTop Z
        (fun _ => P) μ' ∧
      ∀ᵐ ω ∂P, TendstoInDistribution
        (fun (n : ℕ) ω' => √(n : ℝ) • (bootMeanVec n ω' - sampleMeanVec (fun i => X i ω) n))
        atTop Z (fun _ => world (fun i => X i ω)) μ' :=
  ⟨tendstoInDistribution_inv_sqrt_smul_sum_sub hZ hZlaw hint hindep hident,
    ae_tendstoInDistribution_bootMeanVec X hint (fun _ _ hij => hindep.indepFun hij) hident hZ
      hZlaw⟩

end IIDVector

end Vector

end ProbabilityTheory.Bootstrap
