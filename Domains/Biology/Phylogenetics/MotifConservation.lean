/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DeMoivreLaplace
public import MathlibExt.Probability.Distributions.BinomialTail

/-!
# The motif conservation score: binomial tails and their normal limit

Xie et al. (2005) measure the excess conservation of a motif with `N` occurrences, `k` of them
conserved across the aligned genomes, against the conservation probability `p` of comparable
random motifs. Under the null model the number of conserved occurrences is `Bin(N, p)`; the
evidence is the binomial upper tail `P(Bin(N, p) ≥ k)`, and the **motif conservation score**
(MCS) is described as essentially the number of standard deviations by which the observed
conservation exceeds the expected one. We formalize the binomial tail and the binomial
z-score `(k - N p) / √(N p (1 - p))` (`mcsApprox`): this is a binomial z-score
approximation to the MCS, not Xie et al.'s exact score, which may differ in detail
(see their Methods).

## Main results

* `binomTail` and its API (`binomTail_succ_le`, `hasDerivAt_binomTail`,
  `monotoneOn_binomTail`, `strictMonoOn_binomTail`, ...) are defined in
  `MathlibExt.Probability.Distributions.BinomialTail` and re-exported here under their original
  names. `strictMonoOn_binomTail` says a higher background conservation rate makes the same
  count less surprising.
* `mcsApprox_strictMono`: the MCS approximation is strictly increasing in the conserved count.
* `tendsto_prob_le_mcsApprox`: **de Moivre–Laplace for the MCS approximation**: for i.i.d.
  Bernoulli(`p`) conservation indicators, `P(z ≤ MCS approximation)` tends to the standard
  normal mass of `[z, ∞)`.

## References

* X. Xie, J. Lu, E. J. Kulbokas, T. R. Golub, V. Mootha, K. Lindblad-Toh, E. S. Lander,
  M. Kellis, *Systematic discovery of regulatory motifs in human promoters and 3′ UTRs by
  comparison of several mammals*, Nature 434 (2005), 338–345.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  Wiley, 1968 (binomial tails and the normal approximation).
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace MathlibExt.Biology.Phylogenetics.MotifConservation

-- The binomial tail API lives in `MathlibExt.Probability.Distributions.BinomialTail`;
-- these aliases keep the original names available in this namespace.
export ProbabilityTheory (binomTail binomTail_zero binomTail_of_lt binomTail_succ_le
  hasDerivAt_binomTail monotoneOn_binomTail strictMonoOn_binomTail)

/-- **Binomial z-score approximation to the motif conservation score**: the conserved count
`k` of a motif with `N` occurrences, standardized under `Bin(N, p)`:
`(k - N p) / √(N p (1 - p))`. This is an approximation to Xie et al.'s MCS, not their
exact score. -/
noncomputable def mcsApprox (N : ℕ) (k p : ℝ) : ℝ := (k - N * p) / Real.sqrt (N * p * (1 - p))

/-- The MCS approximation is strictly increasing in the conserved count, for `N ≥ 1` and `p ∈ (0, 1)`. -/
theorem mcsApprox_strictMono {N : ℕ} (hN : 0 < N) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMono fun k => mcsApprox N k p := by
  intro a b hab
  have hs : 0 < Real.sqrt (N * p * (1 - p)) :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (Nat.cast_pos.2 hN) hp0) (sub_pos.2 hp1))
  exact div_lt_div_of_pos_right (by linarith) hs

/-- The MCS approximation of the number of conserved occurrences among the first `n` is the
de Moivre–Laplace standardized sum. -/
theorem mcsApprox_sum_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (ω : Ω) :
    mcsApprox n (∑ i ∈ range n, X i ω) p = deMoivreLaplaceStandardized X p n ω := rfl

/-- **De Moivre–Laplace for the MCS approximation**: if the conservation indicators of
the occurrences are i.i.d. Bernoulli(`p`) with `0 < p < 1`, then for every `z`,
`P(z ≤ MCS approximation of the first n occurrences)` tends to the standard normal mass of
`[z, ∞)`. -/
theorem tendsto_prob_le_mcsApprox {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hmean : ∀ i, ∫ ω, X i ω ∂P = p)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (z : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | z ≤ mcsApprox n (∑ i ∈ range n, X i ω) p}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Ici z))) := by
  have hdist := deMoivreLaplace_tendstoInDistribution X hp0 hp1 h01 hmean hindep hident
  have hlim := by simpa [Measure.map_id] using hdist.tendsto
  have hnull : ((⟨gaussianReal 0 (1 : ℝ≥0), inferInstance⟩ : ProbabilityMeasure ℝ)
      : Measure ℝ) (frontier (Set.Ici z)) = 0 := by
    have hns : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    change (gaussianReal 0 (1 : ℝ≥0)) (frontier (Set.Ici z)) = 0
    rw [frontier_Ici]
    exact measure_singleton z
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hnull
  have hport' : Tendsto
      (fun n => (P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Ici z))
      atTop (𝓝 ((gaussianReal 0 1) (Set.Ici z))) :=
    hport
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport'
  have hterm : ∀ n : ℕ, P.real {ω | z ≤ mcsApprox n (∑ i ∈ range n, X i ω) p}
      = ((P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Ici z)).toReal := by
    intro n
    have hmeas : AEMeasurable (fun ω => deMoivreLaplaceStandardized X p n ω) P :=
      hdist.forall_aemeasurable n
    rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ici]
    rfl
  simp_rw [hterm]
  exact hreal

end MathlibExt.Biology.Phylogenetics.MotifConservation
