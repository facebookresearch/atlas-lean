/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCount
public import MathlibExt.Probability.Distributions.Multinomial

/-!
# Pooled Gamma–Poisson counts

Continue the hierarchy of `MathlibExt.Biology.Omics.HierarchicalCount` to several cells. One
gene has rate `λ ~ Gamma(a, b)`, shared by cells `j ∈ ι` with size factors `sⱼ > 0`, and the
cell counts are conditionally independent, `kⱼ ∣ λ ~ Po(sⱼ λ)`. Pooling replaces the cells by
the total count `K = ∑ⱼ kⱼ` and the total exposure `S = ∑ⱼ sⱼ`.

## Main definitions

* `pooledLik s k r = ∏ⱼ P(kⱼ ∣ r)`: the joint likelihood of the cell counts.
* `pooledMarginalLik a b s k`: the joint marginal likelihood `∫ ∏ⱼ P(kⱼ ∣ r) dGamma(a, b)`.

## Main results

* `pooledLik_eq_multinomialReal_mul`: **factorization.** The joint likelihood is the
  multinomial mass of the split `k ∣ K` with cell probabilities `sⱼ / S` (free of `r`) times the
  `Po(S r)` mass of `K`; so `(K, S)` is sufficient for `λ`.
* `pooledMarginalLik_eq_multinomialReal_mul`, `pooledMarginalLik_eq_negBinomialReal`: the joint
  marginal is the multinomial split times `NB(a, S a / b)` at `K`.
* `pooledPosterior_eq_gammaPDFReal`: **pooled conjugacy.** The posterior is
  `Gamma(a + ∑ⱼ kⱼ, b + ∑ⱼ sⱼ)`, the one-cell posterior at count `K` and exposure `S`.
* `integral_id_pooledPosterior`, `variance_pooledPosterior`, `pooledPosteriorMean_eq_shrinkage`:
  posterior mean `(a + K) / (b + S)`, variance `(a + K) / (b + S)²`, and the shrinkage form with
  weight `S / (b + S)` on the pooled rate `K / S`; `shrinkageWeight_mono` (more exposure, less
  shrinkage).
* `sum_pooledMarginalLik`: the pooled count `K` has law `NB(a, S a / b)`.
* `tendsto_posteriorMean_of_tendsto`, `ae_tendsto_pooledPosterior`: **posterior consistency.**
  As the pooled exposure grows and `K / S → r₀`, the posterior mean tends to `r₀` and the
  posterior variance to `0`; a.s. for i.i.d. cell counts with mean `s r₀`.
* `ae_tendsto_pooledEB`: **empirical Bayes with pooled counts.** For i.i.d. units whose pooled
  count has the pooled law above, the moment estimates from the pooled counts converge a.s. to
  `(a, b)` and the empirical-Bayes posterior mean to the oracle pooled posterior mean.

## Implementation notes

The cell split reuses `ProbabilityTheory.multinomialReal`; the pooled posterior and its moments
are the one-cell results `HierarchicalCount.posterior_eq_gammaPDFReal`,
`HierarchicalCount.integral_id_posterior` and `HierarchicalCount.variance_posterior` at exposure
`S` and count `K`, and empirical-Bayes consistency is `HierarchicalCount.ae_tendsto_mom` at
exposure `S`, whose moment hypotheses are derived here from the law of the pooled count.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley (1968), §VI.9 (sums and splits of Poisson counts).
* C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer.
  Statist. Assoc. 78 (1983), 47–55.
* A. Sarkar and M. Stephens, *Separating measurement and expression models clarifies confusion
  in single-cell RNA sequencing analysis*, Nat. Genet. 53 (2021), 770–777.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
open scoped Nat
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExt.Biology.Omics.HierarchicalCountPooled

variable {ι : Type*} [Fintype ι]

/-- The joint likelihood `∏ⱼ e^{-sⱼ r} (sⱼ r)^{kⱼ} / kⱼ!` of conditionally independent cell
counts `kⱼ ∣ λ = r ~ Po(sⱼ r)` with size factors `sⱼ`. -/
noncomputable def pooledLik (s : ι → ℝ) (k : ι → ℕ) (r : ℝ) : ℝ :=
  ∏ j, poissonExposureLik (s j) (k j) r

/-- The joint marginal likelihood of the cell counts under the shared prior `λ ~ Gamma(a, b)`:
`∫ ∏ⱼ P(kⱼ ∣ r) dGamma(a, b)(r)`. -/
noncomputable def pooledMarginalLik (a b : ℝ) (s : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∫ r, pooledLik s k r ∂gammaMeasure a b

/-- **Factorization of the pooled likelihood.** For size factors `sⱼ > 0`, the joint likelihood
of the cell counts is the multinomial mass of the split `k` of `K = ∑ⱼ kⱼ` with cell
probabilities `sⱼ / S`, `S = ∑ⱼ sⱼ`, which does not depend on the rate, times the `Po(S r)` mass
of `K`. -/
theorem pooledLik_eq_multinomialReal_mul {s : ι → ℝ} (hs : ∀ j, 0 < s j) (k : ι → ℕ) (r : ℝ) :
    pooledLik s k r = multinomialReal (∑ j, k j) (fun j => s j / ∑ i, s i) k *
      poissonExposureLik (∑ j, s j) (∑ j, k j) r := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [pooledLik, multinomialReal, poissonExposureLik]
  have hS : 0 < ∑ j, s j := sum_pos (fun j _ => hs j) univ_nonempty
  rw [multinomialReal_eq_factorial_div rfl, pooledLik]
  simp only [poissonExposureLik, div_pow, mul_pow]
  rw [prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_div_distrib, ← Real.exp_sum,
    prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, sum_neg_distrib, ← sum_mul]
  have hK : ((∑ j, k j)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hP : (∏ j, ((k j)! : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hSK : (∑ j, s j) ^ (∑ j, k j) ≠ 0 := pow_ne_zero _ hS.ne'
  field_simp

/-- The pooled marginal likelihood is the multinomial split mass times the one-cell marginal
likelihood of the total count `K` at the total exposure `S`. -/
theorem pooledMarginalLik_eq_multinomialReal_mul (a b : ℝ) {s : ι → ℝ} (hs : ∀ j, 0 < s j)
    (k : ι → ℕ) :
    pooledMarginalLik a b s k = multinomialReal (∑ j, k j) (fun j => s j / ∑ i, s i) k *
      marginalLik a b (∑ j, s j) (∑ j, k j) := by
  rw [pooledMarginalLik, funext (pooledLik_eq_multinomialReal_mul hs k), integral_const_mul,
    marginalLik]

/-- The pooled marginal likelihood is the multinomial split mass times the negative binomial
mass `NB(a, S a / b)` of the total count. -/
theorem pooledMarginalLik_eq_negBinomialReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ j, 0 < s j) (k : ι → ℕ) :
    pooledMarginalLik a b s k = multinomialReal (∑ j, k j) (fun j => s j / ∑ i, s i) k *
      negBinomialReal a ((∑ j, s j) * a / b) (∑ j, k j) := by
  rw [pooledMarginalLik_eq_multinomialReal_mul a b hs,
    marginalLik_eq_negBinomialReal ha hb (sum_nonneg fun j _ => (hs j).le)]

/-- The multinomial split mass is positive at every count vector when all cell probabilities
are positive. -/
private lemma multinomialReal_sum_pos {p : ι → ℝ} (hp : ∀ j, 0 < p j) (k : ι → ℕ) :
    0 < multinomialReal (∑ j, k j) p k := by
  rw [multinomialReal, ite_eq_left rfl]
  exact mul_pos (Nat.cast_pos.2 (Nat.multinomial_pos _ _)) (prod_pos fun j _ => pow_pos (hp j) _)

/-- **Pooled Gamma–Poisson conjugacy.** With prior `λ ~ Gamma(a, b)` (`a, b > 0`) and
conditionally independent cell counts `kⱼ ~ Po(sⱼ λ)` (`sⱼ > 0`), the posterior density (joint
likelihood times prior density over the joint marginal likelihood) is the
`Gamma(a + ∑ⱼ kⱼ, b + ∑ⱼ sⱼ)` density. With no cells it is the prior. -/
theorem pooledPosterior_eq_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ j, 0 < s j) (k : ι → ℕ) (r : ℝ) :
    pooledLik s k r * gammaPDFReal a b r / pooledMarginalLik a b s k =
      gammaPDFReal (a + (∑ j, k j : ℕ)) (b + ∑ j, s j) r := by
  rw [pooledLik_eq_multinomialReal_mul hs, pooledMarginalLik_eq_multinomialReal_mul a b hs,
    mul_assoc, mul_div_mul_left _ _ (multinomialReal_sum_pos (fun j => ?_) k).ne']
  · rcases isEmpty_or_nonempty ι with hι | hι
    · have := isProbabilityMeasure_gammaMeasure ha hb
      simp [marginalLik, poissonExposureLik]
    exact posterior_eq_gammaPDFReal ha hb (sum_pos (fun j _ => hs j) univ_nonempty) _ r
  · exact div_pos (hs j) (sum_pos (fun i _ => hs i) ⟨j, mem_univ j⟩)


/-- The pooled posterior `Gamma(a + K, b + S)` has mean
`posteriorMean a b S K = (a + K) / (b + S)`, the one-cell posterior mean at the pooled count and
exposure. -/
theorem integral_id_pooledPosterior {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ j, 0 ≤ s j) (k : ι → ℕ) :
    ∫ x, x ∂gammaMeasure (a + (∑ j, k j : ℕ)) (b + ∑ j, s j) =
      posteriorMean a b (∑ j, s j) (∑ j, k j) :=
  integral_id_posterior ha hb (sum_nonneg fun j _ => hs j) _

/-- The pooled posterior `Gamma(a + K, b + S)` has variance `(a + K) / (b + S) ^ 2`. -/
theorem variance_pooledPosterior {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ j, 0 ≤ s j) (k : ι → ℕ) :
    variance id (gammaMeasure (a + (∑ j, k j : ℕ)) (b + ∑ j, s j)) =
      (a + (∑ j, k j : ℕ)) / (b + ∑ j, s j) ^ 2 :=
  variance_posterior ha hb (sum_nonneg fun j _ => hs j) _

/-- **Pooled shrinkage.** With at least one cell, the pooled posterior mean is
`w · (K / S) + (1 - w) · (a / b)` with `w = S / (b + S)`: the pooled rate estimate `K / S`
shrunk toward the prior mean. -/
theorem pooledPosteriorMean_eq_shrinkage [Nonempty ι] {a b : ℝ} (hb : 0 < b) {s : ι → ℝ}
    (hs : ∀ j, 0 < s j) (k : ι → ℕ) :
    posteriorMean a b (∑ j, s j) (∑ j, k j) =
      shrinkageWeight b (∑ j, s j) * ((∑ j, k j : ℕ) / ∑ j, s j) +
        (1 - shrinkageWeight b (∑ j, s j)) * (a / b) :=
  posteriorMean_eq_shrinkage hb (sum_pos (fun j _ => hs j) univ_nonempty) _

/-- **More exposure, less shrinkage.** For a prior rate `b > 0` the shrinkage weight
`S / (b + S)` is strictly increasing in the pooled exposure `S ≥ 0`, so pooling an extra cell
moves the posterior mean toward the pooled data. -/
theorem shrinkageWeight_strictMonoOn {b : ℝ} (hb : 0 < b) :
    StrictMonoOn (shrinkageWeight b) (Set.Ici 0) := by
  intro S (hS : 0 ≤ S) S' (hS' : 0 ≤ S') hlt
  rw [shrinkageWeight, shrinkageWeight, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Law of the pooled count.** With at least one cell, summing the joint marginal
likelihood over the cell splits `k` with `∑ⱼ kⱼ = K` gives `NB(a, S a / b)` at `K`: the pooled
count follows the one-cell marginal law at the total exposure `S`. -/
theorem sum_pooledMarginalLik [Nonempty ι] [DecidableEq ι] {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ j, 0 < s j) (K : ℕ) :
    ∑ k ∈ piAntidiag univ K, pooledMarginalLik a b s k =
      negBinomialReal a ((∑ j, s j) * a / b) K := by
  have hS : 0 < ∑ j, s j := sum_pos (fun j _ => hs j) univ_nonempty
  rw [sum_congr rfl fun k hk => by
    rw [pooledMarginalLik_eq_negBinomialReal ha hb hs, (mem_piAntidiag.1 hk).1], ← sum_mul,
    sum_multinomialReal (by rw [← sum_div, div_self hS.ne']), one_mul]

/-! ### Posterior consistency -/

/-- **Posterior consistency, deterministic core.** If the pooled exposure `S → ∞` and the
pooled rate `K / S → r₀`, the pooled posterior mean `(a + K) / (b + S)` tends to `r₀` and the
posterior variance `(a + K) / (b + S) ^ 2` tends to `0`: the prior washes out. -/
theorem tendsto_posteriorMean_of_tendsto {α : Type*} {l : Filter α} {a b r₀ : ℝ} {S : α → ℝ}
    {K : α → ℕ} (hS : Tendsto S l atTop) (hK : Tendsto (fun i => (K i : ℝ) / S i) l (𝓝 r₀)) :
    Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) ∧
      Tendsto (fun i => (a + K i) / (b + S i) ^ 2) l (𝓝 0) := by
  have h0 : ∀ c : ℝ, Tendsto (fun i => c / S i) l (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop hS
  have hmean : Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) := by
    have h := ((h0 a).add hK).div ((h0 b).add tendsto_const_nhds) (by norm_num : (0 : ℝ) + 1 ≠ 0)
    rw [zero_add, zero_add, div_one] at h
    refine h.congr' ?_
    filter_upwards [hS.eventually_gt_atTop 0] with i hi
    change (a / S i + K i / S i) / (b / S i + 1) = (a + K i) / (b + S i)
    rw [← add_div, div_add_one hi.ne', div_div_div_cancel_right₀ hi.ne']
  refine ⟨hmean, ?_⟩
  have hinv : Tendsto (fun i => (b + S i)⁻¹) l (𝓝 0) :=
    (tendsto_atTop_add_const_left l b hS).inv_tendsto_atTop
  have h := hmean.mul hinv
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun i => ?_)
  change (a + K i) / (b + S i) * (b + S i)⁻¹ = (a + K i) / (b + S i) ^ 2
  rw [sq, ← div_div]
  exact (div_eq_mul_inv _ _).symm

/-- **Almost-sure posterior consistency of the pooled posterior.** Let the cell counts
`X₀, X₁, …` (natural numbers) be pairwise independent and identically distributed, with
integrable mean `E X₀ = s r₀` for a common size factor `s > 0` (e.g. `Xⱼ ~ Po(s r₀)` at a true
rate `r₀`). Then almost surely the posterior mean of the pooled posterior over the first `n`
cells tends to `r₀` and its variance tends to `0`. -/
theorem ae_tendsto_pooledPosterior {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {a b s r₀ : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω => (X 0 ω : ℝ)) μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ) (hmean : μ[fun ω => (X 0 ω : ℝ)] = s * r₀) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ _j : Fin n, s) (∑ j : Fin n, X j ω)) atTop
          (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ j : Fin n, X j ω : ℕ)) / (b + ∑ _j : Fin n, s) ^ 2) atTop
          (𝓝 0) := by
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  have hlaw := strong_law_ae (fun j ω => (X j ω : ℝ)) hint
    (fun i j hij => (hindep hij).comp hcast hcast) (fun j => (hident j).comp hcast)
  filter_upwards [hlaw] with ω hω
  simp only [smul_eq_mul, hmean] at hω
  have hS : Tendsto (fun n : ℕ => ∑ _j : Fin n, s) atTop atTop := by
    simpa [Finset.sum_const, nsmul_eq_mul] using tendsto_natCast_atTop_atTop.atTop_mul_const hs
  refine tendsto_posteriorMean_of_tendsto hS ?_
  have h := hω.div_const s
  rw [mul_div_cancel_left₀ _ hs.ne'] at h
  refine h.congr fun n => ?_
  simp only [Nat.cast_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fin.sum_univ_eq_sum_range (fun j => (X j ω : ℝ))]
  ring

/-! ### Empirical Bayes with pooled counts -/

/-- For a natural-number random variable `N` on a finite measure space and a nonnegative `g`,
if `∑ₖ g(K) P(N = K)` converges to `c` then `g ∘ N` is integrable with integral `c`. -/
private lemma integrable_integral_comp_of_hasSum {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : Ω → ℕ} (hN : Measurable N) {g : ℕ → ℝ}
    (hg : ∀ K, 0 ≤ g K) {c : ℝ} (hc : HasSum (fun K => g K * μ.real (N ⁻¹' {K})) c) :
    Integrable (fun ω => g (N ω)) μ ∧ ∫ ω, g (N ω) ∂μ = c := by
  have hlin : ∫⁻ ω, ENNReal.ofReal (g (N ω)) ∂μ = ENNReal.ofReal c := by
    rw [← lintegral_map (f := fun K => ENNReal.ofReal (g K)) Measurable.of_discrete hN,
      lintegral_countable', ← hc.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun K => mul_nonneg (hg K) measureReal_nonneg) hc.summable]
    refine tsum_congr fun K => ?_
    rw [Measure.map_apply hN (measurableSet_singleton K), ENNReal.ofReal_mul (hg K),
      ofReal_measureReal]
  have hc0 : 0 ≤ c := hc.nonneg fun K => mul_nonneg (hg K) measureReal_nonneg
  have hm : AEStronglyMeasurable (fun ω => g (N ω)) μ :=
    ((Measurable.of_discrete (f := g)).comp hN).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hg _), hlin]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hg _) hm, hlin,
      ENNReal.toReal_ofReal hc0]

/-- **Strong consistency of empirical Bayes with pooled counts.** Units `i = 0, 1, …` (e.g.
genes or donors) each carry a rate drawn from `Gamma(a, b)` and are observed on the same cells
`ι` with size factors `sⱼ > 0`; `Nᵢ` is unit `i`'s pooled count. Suppose the `Nᵢ` are pairwise
independent and identically distributed, and `N₀` has the law of the pooled count:
`P(N₀ = K) = ∑_{∑ⱼ kⱼ = K} pooledMarginalLik a b s k`. Then almost surely the moment estimates
computed from the pooled counts of the first `n` units at the total exposure `S = ∑ⱼ sⱼ`
converge to `(a, b)`, and for every pooled count `K` the empirical-Bayes posterior mean
converges to the oracle pooled posterior mean `(a + K) / (b + S)`. The moment hypotheses of
`HierarchicalCount.ae_tendsto_mom` are derived from the law via `sum_pooledMarginalLik`. -/
theorem ae_tendsto_pooledEB [Nonempty ι] [DecidableEq ι] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ → Ω → ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ j, 0 < s j) (hmeas : Measurable (N 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on N)) (hident : ∀ i, IdentDistrib (N i) (N 0) μ μ)
    (hlaw : ∀ K, μ.real (N 0 ⁻¹' {K}) = ∑ k ∈ piAntidiag univ K, pooledMarginalLik a b s k) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => momShape (sampleMean (fun i ω => (N i ω : ℝ)) n ω)
          (sampleVar (fun i ω => (N i ω : ℝ)) n ω)) atTop (𝓝 a) ∧
        Tendsto (fun n => momRate (∑ j, s j) (sampleMean (fun i ω => (N i ω : ℝ)) n ω)
          (sampleVar (fun i ω => (N i ω : ℝ)) n ω)) atTop (𝓝 b) ∧
        ∀ K : ℕ, Tendsto (fun n => ebPosteriorMean (∑ j, s j)
          (sampleMean (fun i ω => (N i ω : ℝ)) n ω) (sampleVar (fun i ω => (N i ω : ℝ)) n ω) K)
          atTop (𝓝 (posteriorMean a b (∑ j, s j) K)) := by
  have hS : 0 < ∑ j, s j := sum_pos (fun j _ => hs j) univ_nonempty
  have hm : 0 ≤ (∑ j, s j) * a / b := by positivity
  have hp : ∀ K, μ.real (N 0 ⁻¹' {K}) = negBinomialReal a ((∑ j, s j) * a / b) K := fun K => by
    rw [hlaw, sum_pooledMarginalLik ha hb hs]
  have h1 : HasSum (fun K : ℕ => (K : ℝ) * μ.real (N 0 ⁻¹' {K})) ((∑ j, s j) * a / b) := by
    simp only [hp]
    exact hasSum_mul_negBinomialReal ha hm
  have h2 : HasSum (fun K : ℕ => (K : ℝ) ^ 2 * μ.real (N 0 ⁻¹' {K}))
      ((∑ j, s j) * a / b + ((∑ j, s j) * a / b) ^ 2 / a + ((∑ j, s j) * a / b) ^ 2) := by
    simp only [hp]
    exact hasSum_sq_negBinomialReal ha hm
  obtain ⟨hint1, hmean⟩ := integrable_integral_comp_of_hasSum hmeas (g := fun K => (K : ℝ))
    (fun K => Nat.cast_nonneg K) h1
  obtain ⟨hint2, hsq⟩ := integrable_integral_comp_of_hasSum hmeas (g := fun K => (K : ℝ) ^ 2)
    (fun K => sq_nonneg _) h2
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  exact ae_tendsto_mom (X := fun i ω => (N i ω : ℝ)) ha hb hS hint1.aestronglyMeasurable hint2
    (fun i j hij => (hindep hij).comp hcast hcast) (fun i => (hident i).comp hcast) hmean hsq

end MathlibExt.Biology.Omics.HierarchicalCountPooled
