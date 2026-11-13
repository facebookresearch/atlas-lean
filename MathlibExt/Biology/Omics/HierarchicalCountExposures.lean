/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCount
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw

import MathlibExt.Probability.Distributions.GammaMoments
import MathlibExt.Probability.Distributions.PoissonKernel
import MathlibExt.Probability.NonnegSLLN

/-!
# Pooled Gamma–Poisson counts with different exposures: posterior consistency

One gene has rate `λ ~ Gamma(a, b)` shared by cells `i` with size factors (exposures) `sᵢ`, and
the cell counts are conditionally independent, `kᵢ ∣ λ ~ Po(sᵢ λ)`, the hierarchy of
`MathlibExt.Biology.Omics.HierarchicalCount`. The pooled posterior is `Gamma(a + K, b + S)` with
`K = ∑ᵢ kᵢ` and `S = ∑ᵢ sᵢ`. This file proves that the pooled posterior is consistent, almost
surely, when the exposures differ from cell to cell. The cell counts are then not identically
distributed, so the i.i.d. strong law does not give `K / S → r₀`; the strong law for
non-identically distributed nonnegative variables,
`ProbabilityTheory.ae_tendsto_sum_div_sum_integral` in `MathlibExt.Probability.NonnegSLLN`, is used
for that purpose.

## Source

* Pooled posterior with exposures: A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson,
  A. Vehtari, D. B. Rubin, *Bayesian Data Analysis*, 3rd ed., CRC Press (2013), §2.6, "Poisson
  model parameterized in terms of rate and exposure": for `yᵢ ∼ Po(xᵢ θ)` and
  `θ ∼ Gamma(α, β)`, the posterior is `θ ∣ y ∼ Gamma(α + ∑ᵢ yᵢ, β + ∑ᵢ xᵢ)`
  (`pooledPosterior_eq_gammaPDFReal`).
* Posterior consistency: the same book, Appendix B (large-sample theory): the posterior
  concentrates at the true parameter as data accumulate (`tendsto_pooledPosterior_of_tendsto`,
  `ae_tendsto_pooledPosterior_exposures`, `ae_tendsto_pooledPosterior_poisson`).

## Main results

* `prod_poissonExposureLik`: the joint likelihood factors as a rate-free constant times
  `r^K e^{-S r}`.
* `pooledPosterior_eq_gammaPDFReal`: **pooled conjugacy with exposures.** The posterior is
  `Gamma(a + ∑ᵢ kᵢ, b + ∑ᵢ sᵢ)`.
* `tendsto_pooledPosterior_of_tendsto`: **deterministic core.** If `S → ∞` and `K / S → r₀`, the
  posterior mean tends to `r₀`, the posterior variance to `0`, and the posterior mass outside
  every neighbourhood of `r₀` to `0`.
* `ae_tendsto_gammaSequence_of_moments`: **a.s. convergence of the Gamma sequence.** For
  pairwise independent counts with `E Xᵢ = sᵢ r₀`, `Var Xᵢ ≤ C sᵢ`, real `sᵢ ≤ B` and
  `∑ sᵢ = ∞`, the conclusions of the deterministic core hold almost surely for
  `Gamma(a + Kₙ, b + Sₙ)`; no sign condition on `sᵢ`, so these laws need not be posteriors.
* `ae_tendsto_pooledPosterior_exposures`: **a.s. posterior consistency with exposures.** The
  same for nonnegative exposures `sᵢ ∈ [0, B]`, where `Gamma(a + Kₙ, b + Sₙ)` is the pooled
  posterior.
* `ae_tendsto_pooledPosterior_poisson`: the same for `Xᵢ ∼ Po(sᵢ r₀)`.

## Implementation notes

The pooled posterior is restated without new definitions, as the product of the one-cell
likelihoods `HierarchicalCount.poissonExposureLik`; its mean and variance are
`HierarchicalCount.integral_id_posterior` and `HierarchicalCount.variance_posterior` at count
`K` and exposure `S`. `HierarchicalCountPooled` (PR #1608, open) is not imported, and two results
here overlap it: `pooledPosterior_eq_gammaPDFReal` duplicates
`HierarchicalCountPooled.pooledPosterior_eq_gammaPDFReal` (same name, sibling namespace), and
`tendsto_pooledPosterior_of_tendsto` is #1608's `tendsto_posteriorMean_of_tendsto` plus the
concentration conclusion. Follow-up: after #1608 merges, derive both from #1608's versions and
remove the duplicate names. The new content with exposures is the strong law and the two a.s.
theorems.

The strong law `ProbabilityTheory.ae_tendsto_sum_div_sum_integral` is a pure probability result
and lives in `MathlibExt.Probability.NonnegSLLN`, next to `PairwiseIndepSLLN`; the indicator law
`ProbabilityTheory.pairwise_indep_slln` is its special case with variance at most mean and means
at most `1`.

Reuse (search of Mathlib, `MathlibExt`, `CSLibExt` and `WantedExt` on 2026-11-12 for strong
laws, Kronecker/Kolmogorov criteria and Poisson moments): Mathlib's
`ProbabilityTheory.strong_law_ae` needs identically distributed variables, and
`ProbabilityTheory.pairwise_indep_slln` covers indicators only; no strong law for
non-identically distributed real variables existed. Reused: the strong law
`ProbabilityTheory.ae_tendsto_sum_div_sum_integral`, Mathlib's Chebyshev inequality
`ProbabilityTheory.meas_ge_le_variance_div_sq`, the Gamma moments
`ProbabilityTheory.memLp_id_gammaMeasure`, and the Poisson moments
`ProbabilityTheory.integral_natCast_poissonMeasure` and
`ProbabilityTheory.variance_natCast_poissonMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Function
open scoped Nat NNReal
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExt.Biology.Omics.HierarchicalCountExposures


variable {ι : Type*} [Fintype ι]

/-! ### The pooled posterior with per-cell exposures -/

/-- **Factorization of the joint likelihood.** For cells `i` with size factors `sᵢ` and counts
`kᵢ`, `∏ᵢ e^{-sᵢ r} (sᵢ r)^{kᵢ} / kᵢ! = (∏ᵢ sᵢ^{kᵢ} / kᵢ!) · r^K e^{-S r}` with `K = ∑ᵢ kᵢ`
and `S = ∑ᵢ sᵢ`: the dependence on the rate is through `(K, S)` only. -/
theorem prod_poissonExposureLik (s : ι → ℝ) (k : ι → ℕ) (r : ℝ) :
    ∏ i, poissonExposureLik (s i) (k i) r =
      (∏ i, s i ^ k i / (k i)!) * (r ^ (∑ i, k i) * exp (-((∑ i, s i) * r))) := by
  have h : ∀ i, poissonExposureLik (s i) (k i) r =
      s i ^ k i / (k i)! * (r ^ k i * exp (-(s i * r))) := fun i => by
    rw [poissonExposureLik, mul_pow]; ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Real.exp_sum,
    Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- **Pooled Gamma–Poisson conjugacy with different exposures.** With prior `λ ~ Gamma(a, b)`
(`a, b > 0`) and conditionally independent cell counts `kᵢ ~ Po(sᵢ λ)` with size factors
`sᵢ > 0`, the posterior density (joint likelihood times prior density over
the joint marginal likelihood) is the `Gamma(a + ∑ᵢ kᵢ, b + ∑ᵢ sᵢ)` density: the one-cell
posterior `HierarchicalCount.posterior_eq_gammaPDFReal` at count `K = ∑ᵢ kᵢ` and exposure
`S = ∑ᵢ sᵢ`. Its mean `(a + K) / (b + S)` and variance `(a + K) / (b + S)²` are then
`HierarchicalCount.integral_id_posterior` and `HierarchicalCount.variance_posterior`. -/
theorem pooledPosterior_eq_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) (k : ι → ℕ) (r : ℝ) :
    (∏ i, poissonExposureLik (s i) (k i) r) * gammaPDFReal a b r /
        (∫ x, ∏ i, poissonExposureLik (s i) (k i) x ∂gammaMeasure a b) =
      gammaPDFReal (a + (∑ i, k i : ℕ)) (b + ∑ i, s i) r := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := isProbabilityMeasure_gammaMeasure ha hb
    simp [Finset.univ_eq_empty]
  set K := ∑ i, k i
  set S := ∑ i, s i
  have hS : 0 < S := Finset.sum_pos (fun i _ => hs i) Finset.univ_nonempty
  have hc : (∏ i, s i ^ k i / (k i)!) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    div_ne_zero (pow_ne_zero _ (hs i).ne') (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hd : S ^ K / (K)! ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hS.ne') (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have h1 : ∀ x, poissonExposureLik S K x = S ^ K / (K)! * (x ^ K * exp (-(S * x))) :=
    fun x => by rw [poissonExposureLik, mul_pow]; ring
  have hone := posterior_eq_gammaPDFReal ha hb hS K r
  rw [marginalLik] at hone
  simp_rw [h1] at hone
  rw [integral_const_mul, mul_assoc, mul_div_mul_left _ _ hd] at hone
  simp_rw [prod_poissonExposureLik]
  rw [integral_const_mul, mul_assoc, mul_div_mul_left _ _ hc]
  exact hone

/-! ### Posterior consistency: deterministic core -/

/-- **Posterior consistency, deterministic core.** Along any filter, if the pooled exposure
`S → ∞` and the pooled rate `K / S → r₀`, then for a prior `Gamma(a, b)` with `a, b > 0` the
pooled posterior `Gamma(a + K, b + S)` has mean `(a + K) / (b + S) → r₀`, variance
`(a + K) / (b + S)² → 0`, and assigns vanishing mass to the complement of every neighbourhood
`(r₀ - ε, r₀ + ε)` of `r₀`: the posterior concentrates at `r₀`. -/
theorem tendsto_pooledPosterior_of_tendsto {α : Type*} {l : Filter α} {a b r₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) {S : α → ℝ} {K : α → ℕ} (hS : Tendsto S l atTop)
    (hK : Tendsto (fun i => (K i : ℝ) / S i) l (𝓝 r₀)) :
    Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) ∧
      Tendsto (fun i => (a + K i) / (b + S i) ^ 2) l (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => gammaMeasure (a + K i) (b + S i) {x | ε ≤ |x - r₀|}) l (𝓝 0) := by
  have h0 : ∀ c : ℝ, Tendsto (fun i => c / S i) l (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop hS
  have hmean : Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) := by
    have h := ((h0 a).add hK).div ((h0 b).add tendsto_const_nhds) (by norm_num : (0 : ℝ) + 1 ≠ 0)
    rw [zero_add, zero_add, div_one] at h
    refine h.congr' ?_
    filter_upwards [hS.eventually_gt_atTop 0] with i hi
    change (a / S i + K i / S i) / (b / S i + 1) = (a + K i) / (b + S i)
    rw [← add_div, div_add_one hi.ne', div_div_div_cancel_right₀ hi.ne']
  have hvar : Tendsto (fun i => (a + K i) / (b + S i) ^ 2) l (𝓝 0) := by
    have hinv : Tendsto (fun i => (b + S i)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left l b hS).inv_tendsto_atTop
    have h := hmean.mul hinv
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun i => ?_)
    change (a + K i) / (b + S i) * (b + S i)⁻¹ = (a + K i) / (b + S i) ^ 2
    rw [sq, ← div_div]
    exact (div_eq_mul_inv _ _).symm
  refine ⟨hmean, hvar, fun ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hup : Tendsto (fun i => ENNReal.ofReal ((a + K i) / (b + S i) ^ 2 / (ε / 2) ^ 2)) l
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hvar.div_const ((ε / 2) ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hS.eventually_ge_atTop 0, (Metric.tendsto_nhds.1 hmean) _ hε2] with i hSi hmi
  have haK : 0 < a + K i := by positivity
  have hbS : 0 < b + S i := by linarith
  have := isProbabilityMeasure_gammaMeasure haK hbS
  have hsub : {x : ℝ | ε ≤ |x - r₀|} ⊆
      {x | ε / 2 ≤ |id x - ∫ y, id y ∂gammaMeasure (a + K i) (b + S i)|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, id] at hx ⊢
    rw [integral_id_posterior ha hb hSi]
    rw [Real.dist_eq] at hmi
    have := abs_sub_abs_le_abs_sub (x - r₀) (x - posteriorMean a b (S i) (K i))
    have h2 : x - r₀ - (x - posteriorMean a b (S i) (K i)) =
        posteriorMean a b (S i) (K i) - r₀ := by ring
    rw [h2] at this
    linarith
  refine (measure_mono hsub).trans ?_
  have := meas_ge_le_variance_div_sq (μ := gammaMeasure (a + K i) (b + S i))
    (memLp_id_gammaMeasure haK hbS) hε2
  rwa [variance_posterior ha hb hSi] at this

/-! ### Almost-sure posterior consistency with different exposures -/

/-- **Almost-sure convergence of the Gamma sequence `Gamma(a + Kₙ, b + Sₙ)`.** A purely analytic
statement: let `s₀, s₁, …` be reals with `sᵢ ≤ B` and `Sₙ = ∑_{i<n} sᵢ → ∞`, and let the counts
`X₀, X₁, …` (natural numbers) be pairwise independent and square-integrable with mean
`E Xᵢ = sᵢ r₀` for some `r₀ ≥ 0` and variance `Var Xᵢ ≤ C sᵢ`. Then almost surely, for `a, b > 0`
and `Kₙ = ∑_{i<n} Xᵢ`, the ratio `(a + Kₙ) / (b + Sₙ)` (`posteriorMean`) tends to `r₀`,
`(a + Kₙ) / (b + Sₙ)²` tends to `0`, and the mass that `gammaMeasure (a + Kₙ) (b + Sₙ)` assigns
outside every neighbourhood `(r₀ - ε, r₀ + ε)` tends to `0`.

No sign condition on `sᵢ` is imposed (for `r₀ > 0`, `sᵢ ≥ 0` follows from `E Xᵢ = sᵢ r₀ ≥ 0`), so
`b + Sₙ` may be nonpositive for small `n` and these Gamma laws need not be posteriors. For
nonnegative exposures they are the pooled posteriors: see `ae_tendsto_pooledPosterior_exposures`.
The counts are not identically distributed, so Mathlib's `ProbabilityTheory.strong_law_ae` does
not apply; `Kₙ / Sₙ → r₀` comes from `ProbabilityTheory.ae_tendsto_sum_div_sum_integral`. -/
theorem ae_tendsto_gammaSequence_of_moments {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {s : ℕ → ℝ} {a b r₀ B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hsB : ∀ i, s i ≤ B)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, s i) atTop atTop)
    (hL2 : ∀ i, MemLp (fun ω => (X i ω : ℝ)) 2 μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hmean : ∀ i, μ[fun ω => (X i ω : ℝ)] = s i * r₀)
    (hvar : ∀ i, Var[fun ω => (X i ω : ℝ); μ] ≤ C * s i) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, s i)
          (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ i ∈ Finset.range n, X i ω : ℕ)) /
          (b + ∑ i ∈ Finset.range n, s i) ^ 2) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n => gammaMeasure (a + (∑ i ∈ Finset.range n, X i ω : ℕ))
          (b + ∑ i ∈ Finset.range n, s i) {x | ε ≤ |x - r₀|}) atTop (𝓝 0) := by
  have hnonneg : ∀ i, 0 ≤ᵐ[μ] fun ω => (X i ω : ℝ) := fun i =>
    Eventually.of_forall fun ω => Nat.cast_nonneg _
  suffices h : ∀ᵐ ω ∂μ, Tendsto (fun n => ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ) /
      ∑ i ∈ Finset.range n, s i) atTop (𝓝 r₀) by
    filter_upwards [h] with ω hω
    exact tendsto_pooledPosterior_of_tendsto ha hb hS hω
  rcases hr₀.eq_or_lt with h0 | hpos
  · -- `r₀ = 0`: every count vanishes almost surely.
    have hzero : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 := fun i => by
      have h := (integral_eq_zero_iff_of_nonneg_ae (hnonneg i)
        ((hL2 i).integrable one_le_two)).1 (by rw [hmean, ← h0, mul_zero])
      filter_upwards [h] with ω hω
      have h' : (X i ω : ℝ) = 0 := hω
      exact_mod_cast h'
    filter_upwards [ae_all_iff.2 hzero] with ω hω
    rw [← h0]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [hω]
  · have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
    have hlaw := ae_tendsto_sum_div_sum_integral (μ := μ) (Y := fun i ω => (X i ω : ℝ))
      (B := B * r₀) (C := C / r₀)
      hL2 hnonneg (fun i j hij => (hindep hij).comp hcast hcast)
      (fun i => by rw [hmean]; exact mul_le_mul_of_nonneg_right (hsB i) hr₀)
      (fun i => by rw [hmean, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hpos.ne'];
                   exact hvar i)
      (by simpa [hmean, ← Finset.sum_mul] using hS.atTop_mul_const hpos)
    filter_upwards [hlaw] with ω hω
    simp only [hmean, ← Finset.sum_mul] at hω
    have h := hω.const_mul r₀
    rw [mul_one] at h
    refine h.congr fun n => ?_
    rw [Nat.cast_sum, ← div_div, mul_div_cancel₀ _ hpos.ne']

/-- **Almost-sure posterior consistency of the pooled posterior with different exposures.**
Let cells `i = 0, 1, …` have nonnegative size factors (exposures) `sᵢ ∈ [0, B]` with divergent
total exposure `Sₙ = ∑_{i<n} sᵢ → ∞`, and let the cell counts `X₀, X₁, …` (natural numbers) be
pairwise independent and square-integrable with mean `E Xᵢ = sᵢ r₀` at a true rate `r₀ ≥ 0` and
variance `Var Xᵢ ≤ C sᵢ` (for `Xᵢ ~ Po(sᵢ r₀)`, `C = r₀`; see
`ae_tendsto_pooledPosterior_poisson`). Then almost surely, for the prior `Gamma(a, b)`
(`a, b > 0`), the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` over the first `n` cells
(`Kₙ = ∑_{i<n} Xᵢ`) has mean tending to `r₀`, variance tending to `0`, and mass outside every
neighbourhood `(r₀ - ε, r₀ + ε)` tending to `0`. This is `ae_tendsto_gammaSequence_of_moments`
for nonnegative exposures. -/
theorem ae_tendsto_pooledPosterior_exposures {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {s : ℕ → ℝ≥0} {a b r₀ B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hsB : ∀ i, (s i : ℝ) ≤ B)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, (s i : ℝ)) atTop atTop)
    (hL2 : ∀ i, MemLp (fun ω => (X i ω : ℝ)) 2 μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hmean : ∀ i, μ[fun ω => (X i ω : ℝ)] = s i * r₀)
    (hvar : ∀ i, Var[fun ω => (X i ω : ℝ); μ] ≤ C * s i) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (s i : ℝ))
          (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ i ∈ Finset.range n, X i ω : ℕ)) /
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) ^ 2) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n => gammaMeasure (a + (∑ i ∈ Finset.range n, X i ω : ℕ))
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) {x | ε ≤ |x - r₀|}) atTop (𝓝 0) :=
  ae_tendsto_gammaSequence_of_moments ha hb hr₀ hsB hS hL2 hindep hmean hvar

/-- **Poisson counts with different exposures.** If the cell counts are pairwise independent with
`Xᵢ ~ Po(sᵢ r₀)` for size factors `sᵢ ∈ [0, B]` with divergent total exposure, then almost surely
the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` has mean tending to the true rate `r₀`, variance
tending to `0`, and concentrates at `r₀`. -/
theorem ae_tendsto_pooledPosterior_poisson {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {s : ℕ → ℝ≥0} {r₀ : ℝ≥0}
    {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hsB : ∀ i, (s i : ℝ) ≤ B)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, (s i : ℝ)) atTop atTop)
    (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (s i * r₀)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (s i : ℝ))
          (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ i ∈ Finset.range n, X i ω : ℕ)) /
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) ^ 2) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n => gammaMeasure (a + (∑ i ∈ Finset.range n, X i ω : ℕ))
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) {x | ε ≤ |x - r₀|}) atTop (𝓝 0) := by
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  have hmem : ∀ r : ℝ≥0, MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := fun r =>
    (memLp_two_iff_integrable_sq hcast.aestronglyMeasurable).2
      (integrable_natCast_sq_poissonMeasure r)
  refine ae_tendsto_pooledPosterior_exposures (C := r₀) ha hb r₀.2 hsB hS
    (fun i => (hlaw i).memLp_comp (hmem _)) hindep (fun i => ?_) (fun i => ?_)
  · have h := (hlaw i).integral_comp (f := fun n : ℕ => (n : ℝ)) hcast.aestronglyMeasurable
    rw [integral_natCast_poissonMeasure, NNReal.coe_mul] at h
    exact h
  · have h := variance_map (μ := μ) (X := fun n : ℕ => (n : ℝ)) (Y := X i)
      ((hlaw i).map_eq ▸ hcast.aemeasurable) (hlaw i).aemeasurable
    rw [(hlaw i).map_eq, variance_natCast_poissonMeasure, NNReal.coe_mul] at h
    rw [← Function.comp_def, ← h, mul_comm]

end MathlibExt.Biology.Omics.HierarchicalCountExposures
