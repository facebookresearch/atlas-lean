/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomial
public import MathlibExt.Probability.Distributions.PoissonMixtureSum

import MathlibExt.Probability.Distributions.Gamma
import MathlibExt.Probability.Distributions.GammaMoments

/-!
# The gamma-Poisson model of mutation counts in a region

Dig (Sherman et al. 2022) tests a set of candidate somatic mutations for an excess over the
neutral mutations expected at their positions. A genomic region `R` has an uncertain neutral
mutation rate `λ`, with predicted mean `μ > 0` and variance `σ² > 0`, modelled as gamma
distributed with that mean and variance: shape `α = μ² / σ²` and scale `θ = σ² / μ`. Each possible
mutation `i` of `R`, a position and a change of its base `X` in context `a X b` into `Y`, has a
probability `p i`, normalized so that the probabilities of all possible mutations of `R` sum to
`1`, and `C > 0` scales the rates from the training cohort to the cohort under study (`C_SNV`).
Given `λ`, the number of observed mutations in a set `I` of candidate mutations of `R` is Poisson
with mean `C (∑_{i ∈ I} p i) λ`: the regional rate thinned by the context probabilities of `I`.
Its marginal law is negative binomial,

`∑_I M_i ~ NegativeBinomial(α, 1 / (1 + C θ ∑_{i ∈ I} p i))`.

The `p`-value of an observed count is the upper tail of this law, and for a union of regions
with independent rates the law of the total count is the convolution of the regions' negative
binomial laws.

## Main definitions

* `rateLaw μ σsq`: the gamma law with shape `μ² / σsq` and scale `σsq / μ` of the regional rate.
* `countPMF μ σsq C p I`: the mass function of the number of mutations in `I`.
* `unionCountPMF μ σsq C p I`: the same for the union of the sets `I r` of regions `r` whose
  rates are independent.

## Main results

* `integral_id_rateLaw`, `variance_id_rateLaw`: the rate law has mean `μ` and variance `σsq`.
* `countPMF_eq_negBinomialPMF`: the count is `NB(μ² / σsq, 1 / (1 + C (σsq / μ) ∑_{i ∈ I} p i))`.
* `countPMF_nonneg`, `hasSum_countPMF`: it is a probability mass function.
* `tsum_countPMF_add`: the `p`-value `P(N ≥ m)` of a count `m` is `1 - ∑_{k < m} NB(k)`.
* `unionCountPMF_eq_sum_prod_negBinomialPMF`: over a union of regions the mass function is the
  convolution of the regions' negative binomial mass functions.
* `unionCountPMF_nonneg`, `hasSum_unionCountPMF`, `tsum_unionCountPMF_add`: it is a probability
  mass function, with upper-tail `p`-values.

## Implementation notes

Laws on `ℕ` are given by their mass functions, as `ProbabilityTheory.poissonMixtureReal` gives
those of mixed Poisson laws. The theorems hold for any cohort scaling `C ≥ 0` and any
probabilities `p ≥ 0` on the candidate set, normalized or not; with `C ∑_{i ∈ I} p i = 0` the
count is `0` almost surely, the negative binomial law with success probability `1`. The
gamma-Poisson hierarchy with an exposure `s`,
`Domains.Biology.Omics.HierarchicalCount.marginalLik`, is the same mixture for `s = C ∑_{i ∈ I} p i`
and the gamma law of rate `μ / σsq`. Here the model is a Poisson mixture over the image of the rate
law under scaling (`ProbabilityTheory.gammaMeasure_map_const_mul`), which Greenwood–Yule
(`ProbabilityTheory.poissonMixtureReal_gammaMeasure`) and the change to the success probability
(`ProbabilityTheory.negBinomialReal_eq_negBinomialPMF`) evaluate.

## References

* M. A. Sherman, A. U. Yaari, O. Priebe, F. Dietlein, P.-R. Loh and B. Berger, *Genome-wide
  mapping of somatic mutation rates uncovers drivers of cancer*, Nat. Biotechnol. 40 (2022),
  1634–1643, Methods, "Modeling mutation counts over an arbitrary set of positions", and
  Supplementary Methods, "Passenger model for SNVs" and "Extension to mutations spanning multiple
  kilobase-scale regions".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped Nat

namespace Domains.Biology.CancerGenomics.RegionalMutationBurden

variable {ι ρ : Type*}

/-- The law of the neutral mutation rate of a region with predicted mean `μ` and variance `σsq`:
the gamma law with shape `α = μ² / σsq` and scale `θ = σsq / μ`, that is, rate `θ⁻¹`. For
`μ, σsq > 0` it is the gamma law with mean `μ` and variance `σsq` (`integral_id_rateLaw`,
`variance_id_rateLaw`). -/
noncomputable def rateLaw (μ σsq : ℝ) : Measure ℝ :=
  gammaMeasure (μ ^ 2 / σsq) (σsq / μ)⁻¹

/-- For `μ, σsq > 0` the rate law is a probability measure. -/
theorem isProbabilityMeasure_rateLaw {μ σsq : ℝ} (hμ : 0 < μ) (hσ : 0 < σsq) :
    IsProbabilityMeasure (rateLaw μ σsq) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)

/-- The rate law has mean `μ`. -/
theorem integral_id_rateLaw {μ σsq : ℝ} (hμ : 0 < μ) (hσ : 0 < σsq) :
    ∫ x, x ∂rateLaw μ σsq = μ := by
  rw [rateLaw, integral_id_gammaMeasure (by positivity) (by positivity)]
  field_simp

/-- The rate law has variance `σsq`. -/
theorem variance_id_rateLaw {μ σsq : ℝ} (hμ : 0 < μ) (hσ : 0 < σsq) :
    variance id (rateLaw μ σsq) = σsq := by
  rw [rateLaw, variance_id_gammaMeasure (by positivity) (by positivity)]
  field_simp

/-- **Gamma-Poisson model of mutation counts in a region** (Dig). A region has a neutral
mutation rate `λ ~ rateLaw μ σsq`, gamma with mean `μ` and variance `σsq`. Each possible mutation
`i : ι` of the region, a position and a change of its base in context, has probability `p i`
(normalized over the possible mutations of the region, which no result here needs), and `C`
scales the rates to the cohort under study. Given `λ`, the number of observed mutations in a
set `I` of candidate mutations is Poisson with mean `C (∑_{i ∈ I} p i) λ`, the regional rate
thinned by the context probabilities of `I`. `countPMF μ σsq C p I k` is the marginal probability
that this count is `k`: the Poisson mixture over the law of `C (∑_{i ∈ I} p i) λ`. For
`μ, σsq > 0`, `C ≥ 0` and `p ≥ 0` on `I` it is a probability mass function (`hasSum_countPMF`),
negative binomial with shape `μ² / σsq` and success probability
`1 / (1 + C (σsq / μ) ∑_{i ∈ I} p i)` (`countPMF_eq_negBinomialPMF`). -/
noncomputable def countPMF (μ σsq C : ℝ) (p : ι → ℝ) (I : Finset ι) (k : ℕ) : ℝ :=
  poissonMixtureReal ((rateLaw μ σsq).map fun x => C * (∑ i ∈ I, p i) * x) k

/-- The law of the Poisson rate of the set `I` is a probability measure. -/
private lemma isProbabilityMeasure_map_rate {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι}
    (hμ : 0 < μ) (hσ : 0 < σsq) :
    IsProbabilityMeasure ((rateLaw μ σsq).map fun x => C * (∑ i ∈ I, p i) * x) :=
  have := isProbabilityMeasure_rateLaw hμ hσ
  inferInstance

/-- The law of the Poisson rate of the set `I` is concentrated on `[0, ∞)`. -/
private lemma ae_nonneg_map_rate {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι} (hC : 0 ≤ C)
    (hp : ∀ i ∈ I, 0 ≤ p i) :
    ∀ᵐ y ∂(rateLaw μ σsq).map (fun x => C * (∑ i ∈ I, p i) * x), 0 ≤ y :=
  (ae_map_iff (by fun_prop) measurableSet_Ici).2 <|
    (ae_nonneg_gammaMeasure _ _).mono fun _ hx => mul_nonneg (mul_nonneg hC (sum_nonneg hp)) hx

/-- **The marginal law of the count is negative binomial.** For `μ, σsq > 0`, `C ≥ 0` and `p ≥ 0`
on `I`, the number of mutations in `I` has law
`NB(α, 1 / (1 + C θ ∑_{i ∈ I} p i))`, with shape `α = μ² / σsq` and scale `θ = σsq / μ`:
`P(N = k) = α⁽ᵏ⁾ / k! · q ^ α (1 - q) ^ k` at `q = 1 / (1 + C θ ∑_{i ∈ I} p i)`. -/
theorem countPMF_eq_negBinomialPMF {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι} (hμ : 0 < μ)
    (hσ : 0 < σsq) (hC : 0 ≤ C) (hp : ∀ i ∈ I, 0 ≤ p i) (k : ℕ) :
    countPMF μ σsq C p I k =
      negBinomialPMF (μ ^ 2 / σsq) (1 / (1 + C * (σsq / μ) * ∑ i ∈ I, p i)) k := by
  have hα : 0 < μ ^ 2 / σsq := by positivity
  have hθ : 0 < σsq / μ := by positivity
  have hc : 0 ≤ C * ∑ i ∈ I, p i := mul_nonneg hC (sum_nonneg hp)
  have := isProbabilityMeasure_rateLaw hμ hσ
  rw [countPMF]
  rcases hc.eq_or_lt with hc0 | hc0
  · simp_rw [← hc0, zero_mul]
    rw [Measure.map_const, measure_univ, one_smul, poissonMixtureReal_dirac,
      show C * (σsq / μ) * ∑ i ∈ I, p i = 0 by rw [mul_right_comm, ← hc0, zero_mul]]
    rcases k with _ | k <;> simp [negBinomialPMF]
  · rw [rateLaw, gammaMeasure_map_const_mul hα (inv_pos.2 hθ) hc0,
      poissonMixtureReal_gammaMeasure hα (div_pos (inv_pos.2 hθ) hc0),
      negBinomialReal_eq_negBinomialPMF hα (div_nonneg hα.le (div_pos (inv_pos.2 hθ) hc0).le)]
    congr 1
    field_simp

/-- The mass function of the count is nonnegative. -/
theorem countPMF_nonneg {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι} (hC : 0 ≤ C)
    (hp : ∀ i ∈ I, 0 ≤ p i) (k : ℕ) : 0 ≤ countPMF μ σsq C p I k :=
  poissonMixtureReal_nonneg (ae_nonneg_map_rate hC hp) k

/-- **Normalization.** For `μ, σsq > 0`, `C ≥ 0` and `p ≥ 0` on `I`, the masses of the count sum
to one. -/
theorem hasSum_countPMF {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι} (hμ : 0 < μ) (hσ : 0 < σsq)
    (hC : 0 ≤ C) (hp : ∀ i ∈ I, 0 ≤ p i) : HasSum (countPMF μ σsq C p I) 1 :=
  have := isProbabilityMeasure_map_rate (C := C) (p := p) (I := I) hμ hσ
  hasSum_poissonMixtureReal (ae_nonneg_map_rate hC hp)

/-- **Upper-tail `p`-value.** For `μ, σsq > 0`, `C ≥ 0` and `p ≥ 0` on `I`, the `p`-value of an
observed count `m`, the upper tail `P(N ≥ m) = ∑_{k ≥ 0} P(N = k + m)` of the count's law, is
`1 - ∑_{k < m} NB(k)` with `NB` the negative binomial mass function of
`countPMF_eq_negBinomialPMF`. -/
theorem tsum_countPMF_add {μ σsq C : ℝ} {p : ι → ℝ} {I : Finset ι} (hμ : 0 < μ) (hσ : 0 < σsq)
    (hC : 0 ≤ C) (hp : ∀ i ∈ I, 0 ≤ p i) (m : ℕ) :
    ∑' k, countPMF μ σsq C p I (k + m) =
      1 - ∑ k ∈ range m,
        negBinomialPMF (μ ^ 2 / σsq) (1 / (1 + C * (σsq / μ) * ∑ i ∈ I, p i)) k := by
  rw [((hasSum_nat_add_iff' m).2 (hasSum_countPMF hμ hσ hC hp)).tsum_eq]
  simp_rw [countPMF_eq_negBinomialPMF hμ hσ hC hp]

/-- **Mutation counts over a union of regions.** Finitely many regions `r : ρ` have predicted
means `μ r` and variances `σsq r` of their neutral mutation rates, mutation probabilities `p r`
and sets `I r` of candidate mutations, in a cohort with scaling `C`. Their rates are independent,
`λ_r ~ rateLaw (μ r) (σsq r)`, and given the rates the counts of the regions are independent and
Poisson with means `C (∑_{i ∈ I r} p r i) λ_r`, so that the total count is Poisson with mean
`∑_r C (∑_{i ∈ I r} p r i) λ_r`. `unionCountPMF μ σsq C p I k` is the marginal probability that the
total count is `k`: the Poisson mixture over the law of that sum under the product of the rate
laws. It is the convolution of the regions' negative binomial mass functions
(`unionCountPMF_eq_sum_prod_negBinomialPMF`). -/
noncomputable def unionCountPMF [Fintype ρ] (μ σsq : ρ → ℝ) (C : ℝ) (p : ρ → ι → ℝ)
    (I : ρ → Finset ι) (k : ℕ) : ℝ :=
  poissonMixtureReal ((Measure.pi fun r => rateLaw (μ r) (σsq r)).map
    fun x => ∑ r, C * (∑ i ∈ I r, p r i) * x r) k

variable [Fintype ρ]

/-- The law of the Poisson rate of the union is the law of the sum of independent rates, one of
each region's law. -/
private lemma pi_map_sum_rate {μ σsq : ρ → ℝ} {C : ℝ} {p : ρ → ι → ℝ} {I : ρ → Finset ι}
    (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) :
    (Measure.pi fun r => rateLaw (μ r) (σsq r)).map
        (fun x => ∑ r, C * (∑ i ∈ I r, p r i) * x r) =
      (Measure.pi fun r => (rateLaw (μ r) (σsq r)).map
        fun x => C * (∑ i ∈ I r, p r i) * x).map fun y => ∑ r, y r := by
  have : ∀ r, IsProbabilityMeasure (rateLaw (μ r) (σsq r)) := fun r =>
    isProbabilityMeasure_rateLaw (hμ r) (hσ r)
  have : ∀ r, IsProbabilityMeasure ((rateLaw (μ r) (σsq r)).map
      fun x => C * (∑ i ∈ I r, p r i) * x) := fun r => isProbabilityMeasure_map_rate (hμ r) (hσ r)
  rw [← Measure.pi_map_pi (fun r => by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The `p`-value of a union of regions comes from convolving their negative binomial laws.**
For `μ r, σsq r > 0`, `C ≥ 0` and `p r ≥ 0` on `I r`, the total count over the union of the
`I r` has mass `∑_{j} ∏_r NB_r(j r)` at `k`, over the `j : ρ → ℕ` with `∑_r j r = k`, where `NB_r`
is the negative binomial mass function of region `r`: the convolution of the regions' laws. -/
theorem unionCountPMF_eq_sum_prod_negBinomialPMF [DecidableEq ρ] {μ σsq : ρ → ℝ} {C : ℝ}
    {p : ρ → ι → ℝ} {I : ρ → Finset ι} (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C)
    (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i) (k : ℕ) :
    unionCountPMF μ σsq C p I k =
      ∑ j ∈ univ.piAntidiag k, ∏ r, negBinomialPMF (μ r ^ 2 / σsq r)
        (1 / (1 + C * (σsq r / μ r) * ∑ i ∈ I r, p r i)) (j r) := by
  have : ∀ r, IsProbabilityMeasure ((rateLaw (μ r) (σsq r)).map
      fun x => C * (∑ i ∈ I r, p r i) * x) := fun r => isProbabilityMeasure_map_rate (hμ r) (hσ r)
  rw [unionCountPMF, pi_map_sum_rate hμ hσ,
    poissonMixtureReal_pi_map_sum (fun r => ae_nonneg_map_rate hC (hp r))]
  refine sum_congr rfl fun j _ => prod_congr rfl fun r _ => ?_
  exact countPMF_eq_negBinomialPMF (hμ r) (hσ r) hC (hp r) (j r)

/-- The law of the Poisson rate of the union is concentrated on `[0, ∞)`. -/
private lemma ae_nonneg_pi_map_sum_rate {μ σsq : ρ → ℝ} {C : ℝ} {p : ρ → ι → ℝ}
    {I : ρ → Finset ι} (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C)
    (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i) :
    ∀ᵐ y ∂(Measure.pi fun r => rateLaw (μ r) (σsq r)).map
      (fun x => ∑ r, C * (∑ i ∈ I r, p r i) * x r), 0 ≤ y := by
  have : ∀ r, IsProbabilityMeasure (rateLaw (μ r) (σsq r)) := fun r =>
    isProbabilityMeasure_rateLaw (hμ r) (hσ r)
  have hmeas : Measurable fun x : ρ → ℝ => ∑ r, C * (∑ i ∈ I r, p r i) * x r := by fun_prop
  have h0 : ∀ᵐ x ∂Measure.pi fun r => rateLaw (μ r) (σsq r), ∀ r, 0 ≤ x r :=
    Measure.ae_pi_le_pi (Filter.eventually_pi fun r => ae_nonneg_gammaMeasure _ _)
  exact (ae_map_iff hmeas.aemeasurable measurableSet_Ici).2 <| h0.mono
    fun x hx => sum_nonneg fun r _ => mul_nonneg (mul_nonneg hC (sum_nonneg (hp r))) (hx r)

/-- The mass function of the total count over a union of regions is nonnegative. -/
theorem unionCountPMF_nonneg {μ σsq : ρ → ℝ} {C : ℝ} {p : ρ → ι → ℝ} {I : ρ → Finset ι}
    (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C) (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i)
    (k : ℕ) : 0 ≤ unionCountPMF μ σsq C p I k :=
  poissonMixtureReal_nonneg (ae_nonneg_pi_map_sum_rate hμ hσ hC hp) k

/-- **Normalization over a union of regions.** For `μ r, σsq r > 0`, `C ≥ 0` and `p r ≥ 0` on
`I r`, the masses of the total count sum to one. -/
theorem hasSum_unionCountPMF {μ σsq : ρ → ℝ} {C : ℝ} {p : ρ → ι → ℝ} {I : ρ → Finset ι}
    (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C) (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i) :
    HasSum (unionCountPMF μ σsq C p I) 1 := by
  have : ∀ r, IsProbabilityMeasure (rateLaw (μ r) (σsq r)) := fun r =>
    isProbabilityMeasure_rateLaw (hμ r) (hσ r)
  exact hasSum_poissonMixtureReal (ae_nonneg_pi_map_sum_rate hμ hσ hC hp)

/-- **Upper-tail `p`-value over a union of regions.** For `μ r, σsq r > 0`, `C ≥ 0` and `p r ≥ 0`
on `I r`, the `p`-value of an observed total count `m`, `P(N ≥ m) = ∑_{k ≥ 0} P(N = k + m)`, is
`1 - ∑_{k < m} ∑_{j} ∏_r NB_r(j r)`, one minus the masses below `m` of the convolution of the
regions' negative binomial laws (`unionCountPMF_eq_sum_prod_negBinomialPMF`). -/
theorem tsum_unionCountPMF_add [DecidableEq ρ] {μ σsq : ρ → ℝ} {C : ℝ} {p : ρ → ι → ℝ}
    {I : ρ → Finset ι} (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C)
    (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i) (m : ℕ) :
    ∑' k, unionCountPMF μ σsq C p I (k + m) =
      1 - ∑ k ∈ range m, ∑ j ∈ univ.piAntidiag k, ∏ r, negBinomialPMF (μ r ^ 2 / σsq r)
        (1 / (1 + C * (σsq r / μ r) * ∑ i ∈ I r, p r i)) (j r) := by
  rw [((hasSum_nat_add_iff' m).2 (hasSum_unionCountPMF hμ hσ hC hp)).tsum_eq]
  simp_rw [unionCountPMF_eq_sum_prod_negBinomialPMF hμ hσ hC hp]

end Domains.Biology.CancerGenomics.RegionalMutationBurden
