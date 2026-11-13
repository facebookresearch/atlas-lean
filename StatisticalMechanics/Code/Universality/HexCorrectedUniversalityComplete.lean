/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexCorrectedCompletedHighestCut
import Code.Universality.HexCorrectedStripLocal
import Code.Universality.HexLiteralHWDepthSubcritical
import Code.Universality.HexStandardCount

namespace StatMech.Universality

open Filter Topology

noncomputable section



theorem hexStandard_connective_constant_of_local
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (nhds kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  have hdivFixed :=
    hexCS_critical_divergence_of_completedHighestCut hlocal
  have hdiv : ¬ Summable
      (fun n => hexLiteralSAWCount n * hexChiE ^ n) := by
    simpa only [hexLiteralSAWCount_eq hexAWStart 1] using hdivFixed
  have hconvPos := hlhds_summable_of_local hlocal
  have hconv : ∀ x, 0 ≤ x → x < hexChiE →
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
        hconvPos x hxpos hlt
  exact hexStandard_connective_constant_of_series hdiv hconv



theorem hexStandard_connective_constant :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (nhds kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  apply hexStandard_connective_constant_of_local
  exact hexCS_localRelation



theorem hexStandard_connective_constant_tendsto :
    Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop
      (nhds (Real.sqrt (2 + Real.sqrt 2))) := by
  obtain ⟨kappa, _, hlim, hkappa⟩ := hexStandard_connective_constant
  simpa only [hkappa] using hlim

end

end StatMech.Universality
