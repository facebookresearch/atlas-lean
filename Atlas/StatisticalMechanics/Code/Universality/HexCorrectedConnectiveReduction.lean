/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexCorrectedTopWitness
import Code.Universality.HexStandardCount

namespace StatMech.Universality

open Filter Topology

noncomputable section



theorem hexStandard_connective_constant_of_corrected_data
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT)
    (hconv : ∀ x, 0 < x → x < hexChiE →
      Summable (fun n : ℕ =>
        hlc_sawCountR hexAWStart 1 n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (nhds kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  have hdivFixed := hexCS_critical_divergence_of_highestCuts
    hlocal hwindow HC
  have hdiv : ¬ Summable
      (fun n => hexLiteralSAWCount n * hexChiE ^ n) := by
    simpa only [hexLiteralSAWCount_eq hexAWStart 1] using hdivFixed
  have hconv' : ∀ x, 0 ≤ x → x < hexChiE →
      Summable (fun n => hexLiteralSAWCount n * x ^ n) := by
    intro x hx hlt
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · apply summable_of_hasFiniteSupport
      apply Set.Finite.subset (Set.finite_singleton 0)
      intro n hn
      simp only [Function.mem_support, ne_eq, Set.mem_singleton_iff] at hn ⊢
      by_contra hne
      exact hn (by rw [zero_pow hne, mul_zero])
    · simpa only [hexLiteralSAWCount_eq hexAWStart 1] using
        hconv x hxpos hlt
  exact hexStandard_connective_constant_of_series hdiv hconv'

end

end StatMech.Universality
