/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction

/-!
# Tests for the wired density as a right derivative

The loop at zero and the edge from zero to one in the one-dimensional box `Λ₁` cannot share
one wired density at `p = 1/4`. Restricting to genuine edges permits the centered free-energy
limit to supply a common right derivative.
-/

open StatMech.FK StatMech.Lattice

/-- **All-pairs obstruction.** At `t = log(1/3)`, the loop at zero and the edge from zero to one
cannot both have wired density equal to the right derivative of the same function. -/
example (g : ℝ → ℝ) :
    ¬ ∀ e : Sym2 (boxVerts 1 1),
      wiredEdgeDensity 1 2 (edgeIncl 1 1 e) (fsc_logistic (Real.log (1 / 3))) =
        pressureRightDeriv g (Real.log (1 / 3)) := by
  intro h
  have hp : (0 : ℝ) < 1 / 4 := by norm_num
  have hp1 : (1 / 4 : ℝ) < 1 := by norm_num
  have hlogistic : fsc_logistic (Real.log (1 / 3)) = 1 / 4 := by
    rw [fsc_logistic, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
    norm_num
  rw [hlogistic] at h
  let z : boxVerts 1 1 := ⟨0, ocs_zero_mem_box 1 1⟩
  have hloop := fpe2_wired_density_nonEdge 1 s(z, z) (by simp [SimpleGraph.mem_edgeFinset]) hp hp1
  let e := ocs_unitEdge 1 1 le_rfl (0, true)
  have he : e ∈ (boxGraph 1 1).edgeFinset := ocs_unitEdge1_mem_edgeFinset 1 (0, true)
  have hfinite := dfi_wired_per_edge_ge 1 1 le_rfl e hp hp1
  rw [← ocs_unitEdge_eq_innerEdgeLE 1 1 le_rfl (0, true)] at hfinite
  have hbound : wiredEdgeDensity 1 2 (edgeIncl 1 1 e) (1 / 4) ≤ 1 / 4 := by
    refine hfinite.trans ?_
    rw [fuc_edgeMargProb_eq_eventMassProb]
    refine (wiredFkProb_le_fkProbOne_increasing (boxGraph 1 1) (boxBoundary 1 1)
      hp hp1 (by norm_num : (1 : ℝ) ≤ 2) (boxEdgeOpenEvent_isIncreasing 1 1 e)).trans_eq ?_
    simp only [dfi_indicator_boxEdgeOpenEvent]
    simpa using fkProbOne_cylinder (boxGraph 1 1) hp hp1 {e} (Finset.singleton_subset_iff.mpr he)
  rw [h e, ← h s(z, z), hloop] at hbound
  norm_num at hbound

/-- **Genuine-edge non-vacuity.** The one-dimensional box `Λ₁` has an edge, and the centered
free-energy limit satisfies the wired right-derivative condition on its edges. -/
example : (boxGraph 1 1).edgeFinset.Nonempty ∧ ∃ g, fpe2_GenuineWiredIsRightDeriv 1 1 g := by
  have hbox (n : ℕ) (hn : 1 ≤ n) : 0 < (boxGraph 1 n).edgeFinset.card :=
    ecz_box_edge_pos 1 le_rfl hn
  obtain ⟨g, hlim, hg, _⟩ := ecz_centeredConvergence le_rfl hbox fun t =>
    ecz_blockOscillation_of_perEdgeDensity t (ecz_perEdgeDensityConverges le_rfl t hbox)
  exact ⟨Finset.card_pos.mp (hbox 1 le_rfl), g,
    ecz_genuineWiredIsRightDeriv_n1 le_rfl 1 hbox hg hlim
      (ecz_genuineFreeCollapse_n1 le_rfl 1 hbox) (ecz_genuineWiredCollapse_n1 le_rfl 1 hbox)⟩
