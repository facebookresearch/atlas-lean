/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MonotoneLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The posterior of a heterozygous selection coefficient is monotone in the PTV count

In the mutation–selection balance model of Cassa et al. (2017), the number `k` of
protein-truncating variant (PTV) alleles observed in a gene across `n` sampled chromosomes is
Poisson with mean `n U / s_het`, where `U` is the gene's PTV mutation rate and `s_het` the
selection coefficient against heterozygous carriers; a prior on `s_het` (an inverse Gaussian in
Cassa et al.) gives the posterior by Bayes' formula (Weghorn et al. 2019, eq. 1). Because the
mean decreases in `s_het`, the Poisson family has an antitone likelihood ratio, so for **every**
prior the posterior of `s_het` is stochastically nonincreasing in `k`: observing more PTVs never
raises the posterior probability of strong selection.

The general statement holds for any Poisson mean that is nonnegative and antitone in `s_het`
(for example one computed under a demographic model, as in Weghorn et al. 2019); the
deterministic balance mean `n U / s` is the special case `posteriorTail_balance_antitone`, where
integrability and positivity of the marginal likelihoods are proved for any probability prior
on `(0, ∞)`.

## Main results

* `MathlibExt.Biology.StatisticalGenetics.ShetPosterior.balanceMean`: `n U / s`.
* `posteriorTail_antitone_of_antitoneOn`: any antitone Poisson mean, any prior.
* `posteriorTail_balance_antitone`: the balance mean `n U / s`, any probability prior on
  `(0, ∞)`.

## References

* C. A. Cassa et al., *Estimating the selective effects of heterozygous protein-truncating
  variants from human exome data*, Nat. Genet. 49 (2017) 806–810.
* D. Weghorn et al., *Applicability of the mutation–selection balance model to population
  genetics of heterozygous protein-truncating variants in humans*, Mol. Biol. Evol. 36 (2019)
  1701–1710.
* P. R. Milgrom, *Good news and bad news: representation theorems and applications*,
  Bell J. Econ. 12 (1981) 380–391.
-/

@[expose] public section

open MeasureTheory Real Set ProbabilityTheory

namespace MathlibExt.Biology.StatisticalGenetics.ShetPosterior

/-- Mean PTV allele count `n U / s` at deterministic mutation–selection balance, for `n`
sampled chromosomes, PTV mutation rate `U` and heterozygous selection coefficient `s > 0`. -/
noncomputable def balanceMean (n U s : ℝ) : ℝ := n * U / s

/-- The balance mean is antitone in `s > 0` for `n U ≥ 0`. -/
theorem balanceMean_antitoneOn {n U : ℝ} (hnU : 0 ≤ n * U) :
    AntitoneOn (balanceMean n U) (Ioi 0) := by
  intro s hs s' _ hss'
  exact div_le_div_of_nonneg_left hnU hs hss'

/-- **Posterior of `s_het` is stochastically nonincreasing in the PTV count, any antitone
mean**: for a prior `μ` on `s_het` concentrated on `(0, ∞)`, a Poisson count with mean `λ`
nonnegative and antitone on `(0, ∞)`, integrable likelihoods and positive marginal likelihoods,
`P(s_het > t ∣ k') ≤ P(s_het > t ∣ k)` whenever `k ≤ k'`. -/
theorem posteriorTail_antitone_of_antitoneOn {μ : Measure ℝ}
    (hμ : μ (Ioi 0)ᶜ = 0) {lam : ℝ → ℝ} (hanti : AntitoneOn lam (Ioi 0))
    (hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lam s) (hint : ∀ k, Integrable (poissonLik lam k) μ)
    {k k' : ℕ} (hkk' : k ≤ k') (hk : 0 < ∫ s, poissonLik lam k s ∂μ)
    (hk' : 0 < ∫ s, poissonLik lam k' s ∂μ) (t : ℝ) :
    posteriorTail μ (poissonLik lam) k' t ≤ posteriorTail μ (poissonLik lam) k t :=
  posteriorTail_anti_of_hasAntitoneLR hμ (poissonLik_hasAntitoneLR hanti hnn) hint hkk' hk hk'
    t

/-- **Cassa et al. (2017) model**: with the balance mean `n U / s_het` (`n, U > 0`) and any
probability prior on `s_het ∈ (0, ∞)`, the posterior probability `P(s_het > t ∣ k)` is
nonincreasing in the observed PTV count `k`. -/
theorem posteriorTail_balance_antitone {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Ioi 0)ᶜ = 0) {n U : ℝ} (hn : 0 < n) (hU : 0 < U) {k k' : ℕ} (hkk' : k ≤ k')
    (t : ℝ) :
    posteriorTail μ (poissonLik (balanceMean n U)) k' t ≤
      posteriorTail μ (poissonLik (balanceMean n U)) k t := by
  have hnU : 0 < n * U := mul_pos hn hU
  have hae : ∀ᵐ s ∂μ, s ∈ Ioi (0 : ℝ) := mem_ae_iff.mpr hμ
  have hlam : ∀ s ∈ Ioi (0 : ℝ), 0 < balanceMean n U s := fun s hs => div_pos hnU hs
  have hLpos : ∀ j, ∀ s ∈ Ioi (0 : ℝ), 0 < poissonLik (balanceMean n U) j s := by
    intro j s hs
    unfold poissonLik
    have := hlam s hs
    positivity
  have hLle : ∀ j, ∀ s ∈ Ioi (0 : ℝ), poissonLik (balanceMean n U) j s ≤ 1 := by
    intro j s hs
    unfold poissonLik
    have h := pow_div_factorial_le_exp _ (hlam s hs).le j
    rw [mul_div_assoc]
    calc exp (-balanceMean n U s) * (balanceMean n U s ^ j / j.factorial)
        ≤ exp (-balanceMean n U s) * exp (balanceMean n U s) := by gcongr
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hmeas : ∀ j, Measurable (poissonLik (balanceMean n U) j) := by
    intro j
    unfold poissonLik balanceMean
    fun_prop
  have hint : ∀ j, Integrable (poissonLik (balanceMean n U) j) μ := by
    intro j
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hmeas j).aestronglyMeasurable ?_
    filter_upwards [hae] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (hLpos j s hs)]
    exact hLle j s hs
  have hμpos : 0 < μ (Ioi 0) := by
    rw [pos_iff_ne_zero]
    intro h0
    obtain ⟨s, hs1, hs2⟩ := (hae.and (measure_eq_zero_iff_ae_notMem.mp h0)).exists
    exact hs2 hs1
  have hmarg : ∀ j, 0 < ∫ s, poissonLik (balanceMean n U) j s ∂μ := by
    intro j
    have hnonneg : 0 ≤ᵐ[μ] poissonLik (balanceMean n U) j := by
      filter_upwards [hae] with s hs
      exact (hLpos j s hs).le
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg (hint j)]
    exact hμpos.trans_le (measure_mono fun s hs => (hLpos j s hs).ne')
  exact posteriorTail_antitone_of_antitoneOn hμ (balanceMean_antitoneOn hnU.le)
    (fun s hs => (hlam s hs).le) hint hkk' (hmarg k) (hmarg k') t

end MathlibExt.Biology.StatisticalGenetics.ShetPosterior
