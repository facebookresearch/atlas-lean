/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Walls.bc98mcoroute
import Code.Walls.bc56menger
import Code.Walls.bc60upperlines
import Code.Walls.bc61coarsebox

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc99_texBoxAttach_of_bmm {n : ℕ}
    (h : bmm_BoxMengerAttachment d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23





theorem bc99_texBoxAttach_of_reachesNbr {n : ℕ}
    (h : bc56_BoxClusterReachesNbr d n) : tex_BoxAttachData d n :=
  bc99_texBoxAttach_of_bmm (bc56_boxMengerAttachment_of_reachesNbr h)









theorem bc99_hroute_of_reachesNbr
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d,
        0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) :=
  bc98_hroute_of_boxAttach μ hfe (fun n => bc99_texBoxAttach_of_reachesNbr (h n))


theorem bc99_close_a_of_reachesNbr
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
    bc95_SingleSiteRewiring μ :=
  bc98_close_a_of_boxAttach μ hfe (fun n => bc99_texBoxAttach_of_reachesNbr (h n))









theorem bc99_bk_from_reachesNbr
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc98_bk_from_boxAttach μ hfe hprob0 (fun n => bc99_texBoxAttach_of_reachesNbr (h n))














theorem bc99_upperLines_cluster_height {h : ℤ} {a : Site 2}
    (ha : a ∈ cluster 2 bc60_upperLines (bc57_pt 0 h)) : a 1 = h := by
  rw [mem_cluster] at ha
  exact bc60_height_invariant (by rw [bc57_pt_snd]) ha










theorem bc99_reachesNbr_fails_upperLines :
    ¬ bc56_ClusterReachesNbr bc60_upperLines (bc57_pt 0 3) := by
  rintro ⟨a, hadj, hmem, _hreach, _hinf⟩
  have hheight3 : a 1 = 3 := bc99_upperLines_cluster_height hmem
  have hle1 : a 1 ≤ 1 := bc60_nbr_height_le hadj
  omega










theorem bc99_boxReachesNbr_fails : ¬ bc56_BoxClusterReachesNbr 2 3 := by
  intro h
  
  have hb1 : bc57_pt 0 1 ∈ box 2 3 := bc60_pt_zero_mem_box (by decide)
  have hb2 : bc57_pt 0 2 ∈ box 2 3 := bc60_pt_zero_mem_box (by decide)
  have hb3 : bc57_pt 0 3 ∈ box 2 3 := bc60_pt_zero_mem_box (by decide)
  have hi1 : (cluster 2 bc60_upperLines (bc57_pt 0 1)).Infinite := bc60_cluster_infinite (by decide)
  have hi2 : (cluster 2 bc60_upperLines (bc57_pt 0 2)).Infinite := bc60_cluster_infinite (by decide)
  have hi3 : (cluster 2 bc60_upperLines (bc57_pt 0 3)).Infinite := bc60_cluster_infinite (by decide)
  have hcd12 : cluster 2 bc60_upperLines (bc57_pt 0 1) ≠ cluster 2 bc60_upperLines (bc57_pt 0 2) :=
    bc60_cluster_ne (by decide)
  have hcd13 : cluster 2 bc60_upperLines (bc57_pt 0 1) ≠ cluster 2 bc60_upperLines (bc57_pt 0 3) :=
    bc60_cluster_ne (by decide)
  have hcd23 : cluster 2 bc60_upperLines (bc57_pt 0 2) ≠ cluster 2 bc60_upperLines (bc57_pt 0 3) :=
    bc60_cluster_ne (by decide)
  obtain ⟨_, _, h3⟩ := h bc60_upperLines bc60_mem_threeMeetBox
    (bc57_pt 0 1) (bc57_pt 0 2) (bc57_pt 0 3) hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact bc99_reachesNbr_fails_upperLines h3














theorem bc99_notFree_of_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      ¬ bc56_BoxClusterReachesNbr 2 3 :=
  ⟨bc61_wholeBox_severs_upperLines hL, bc99_boxReachesNbr_fails⟩












theorem bc99_reachesNbr_nonvacuous :
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) :=
  bc56_threeRayConfig_reachesNbr_witness.1




























theorem bc99_status :
    
    (∀ (n : ℕ), bc56_BoxClusterReachesNbr 2 n → tex_BoxAttachData 2 n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 →
      (∀ n : ℕ, bc56_BoxClusterReachesNbr 2 n) →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ (L : ℕ), 3 ≤ L →
      bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
        ¬ bc56_BoxClusterReachesNbr 2 3) ∧
    
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n h; exact bc99_texBoxAttach_of_reachesNbr h
  · intro μ _ hfe hprob0 h; exact bc99_bk_from_reachesNbr μ hfe hprob0 h
  · intro L hL; exact bc99_notFree_of_coarseTrif hL
  · exact bc99_reachesNbr_nonvacuous

end StatMech.Walls
