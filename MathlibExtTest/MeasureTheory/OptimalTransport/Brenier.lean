/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Brenier

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.BrenierWanted (brenier)
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExtTest.MeasureTheory.OptimalTransport.Brenier

private abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A point mass is an admissible target. The potential has the prescribed constant gradient
almost everywhere, even though the target may be singular. -/
example {n : ℕ} (μ : ProbabilityMeasure (Space n)) (a : Space n)
    (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure (Space n)) < ⊤)
    (hac : (μ : Measure (Space n)) ≪ volume) :
    ∃ (U : Set (Space n)) (ψ : Space n → ℝ), IsOpen U ∧ (μ : Measure (Space n)) Uᶜ = 0 ∧
      ConvexOn ℝ U ψ ∧ ∀ᵐ x ∂(μ : Measure (Space n)), HasGradientAt ψ a x := by
  let ν : ProbabilityMeasure (Space n) := ⟨Measure.dirac a, inferInstance⟩
  have hm : ∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂(ν : Measure (Space n)) < ⊤ := by
    change (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂Measure.dirac a) < ⊤
    simp [eNorm_eq_nnNorm]
  obtain ⟨T, hT, π, hgraph, hπ, _, _, U, ψ, hU, _, hfull, hψ, hgrad⟩ :=
    brenier μ ν hμ hm hac
  have hmap : (μ : Measure (Space n)).map T = Measure.dirac a := by
    have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
    have h := hπ.2
    rw [hgraph, Measure.map_map measurable_snd hg] at h
    exact h.symm
  have hconst : ∀ᵐ x ∂(μ : Measure (Space n)), T x = a := by
    apply ae_of_ae_map (p := fun y => y = a) hT.aemeasurable
    rw [hmap, ae_dirac_eq]
    rfl
  refine ⟨U, ψ, hU, hfull, hψ, ?_⟩
  filter_upwards [hgrad, hconst] with x hx ha using ha ▸ hx

/-- For equal marginals the diagonal coupling is the unique optimizer. -/
example {n : ℕ} (μ : ProbabilityMeasure (Space n))
    (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure (Space n)) < ⊤)
    (hac : (μ : Measure (Space n)) ≪ volume)
    (π : ProbabilityMeasure (Space n × Space n)) (hπ : IsCoupling μ μ π)
    (hzero : (∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π : Measure (Space n × Space n))) = 0) :
    π = μ.map (fun x => (x, x)) := by
  obtain ⟨_, _, ρ, _, _, _, huniq, _⟩ := brenier μ μ hμ hμ hac
  have hcost : transportCost 2 μ μ = 0 :=
    le_antisymm ((transportCost_le_of_isCoupling hπ).trans_eq hzero) bot_le
  apply (huniq π hπ (hzero.trans hcost.symm)).trans
  symm
  apply huniq _ (isCoupling_diag μ)
  have hg : Measurable (fun x : Space n => (x, x)) := measurable_id.prodMk measurable_id
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map (measurable_edist.pow_const _) hg, hcost]
  simp

end MathlibExtTest.MeasureTheory.OptimalTransport.Brenier
