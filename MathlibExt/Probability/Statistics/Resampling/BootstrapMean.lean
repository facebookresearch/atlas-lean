/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Resampling.BootstrapMeanCLT

/-!
# The bootstrap mean's conditional expectation

For a fixed original sample `x : ℕ → ℝ` and `n > 0`, let the resample
`Y : Fin n → ℝ` be drawn i.i.d. from the empirical law `empiricalLaw x n`
(the resampling law, conditional on `x`). The expectation of the resample mean
`(1/n) ∑ k, Y k` over the resampling law is the sample mean `empiricalMean x n`
(`integral_bootstrapMean`). This is the conditional expectation given `x`;
no bootstrap validity or consistency is claimed. The proof is linearity of the
integral plus the landed `integral_empiricalLaw`.

## Main results

* `ProbabilityTheory.integral_bootstrapMean`.

Provenance: the proof body was drafted by Muse Code from a pinned statement
and was independently checked with Codex before integration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

theorem integral_bootstrapMean {x : ℕ → ℝ} {n : ℕ} (hn : 0 < n) :
    ∫ y, (n : ℝ)⁻¹ * ∑ k : Fin n, y k ∂(Measure.pi fun _ : Fin n => empiricalLaw x n) =
      empiricalMean x n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hprob : ∀ _ : Fin n, IsProbabilityMeasure (empiricalLaw x n) :=
    fun _ => isProbabilityMeasure_empiricalLaw x hn
  have hmp : ∀ k : Fin n, MeasurePreserving (Function.eval k)
      (Measure.pi fun _ : Fin n => empiricalLaw x n) (empiricalLaw x n) :=
    fun k => @measurePreserving_eval _ _ _ _ _ hprob k
  have hInt : ∀ k : Fin n, Integrable (fun y : Fin n → ℝ => y k)
      (Measure.pi fun _ : Fin n => empiricalLaw x n) := by
    intro k
    exact (hmp k).integrable_comp_of_integrable (integrable_empiricalLaw x n id)
  have hCoord : ∀ k : Fin n, (∫ y, y k ∂(Measure.pi fun _ : Fin n => empiricalLaw x n)) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i := by
    intro k
    have hmap : Measure.map (Function.eval k) (Measure.pi fun _ : Fin n => empiricalLaw x n) =
        empiricalLaw x n := (hmp k).map_eq
    have h1 : (∫ z, id z ∂(empiricalLaw x n)) =
        ∫ y, y k ∂(Measure.pi fun _ : Fin n => empiricalLaw x n) := by
      conv_lhs => rw [← hmap]
      exact integral_map (hmp k).measurable.aemeasurable aestronglyMeasurable_id
    rw [← h1]
    exact integral_empiricalLaw x n id
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hInt k)]
  simp only [hCoord]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, empiricalMean_eq]
  field_simp

end ProbabilityTheory
