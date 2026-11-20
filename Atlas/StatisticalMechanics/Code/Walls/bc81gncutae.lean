/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Walls.bc80gntrifcount
import Code.Walls.bc79finiteN
import Code.Walls.bc67supervertex
import Code.Walls.bc76buffer

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

















theorem bc81_singleBox_no_gap (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :=
  bc67_Gn_singleVertex_trifurcation_degree ω L y
    ((bc67_coarseTrif_is_G_n_trifurcation ω L y).mp h)











theorem bc81_omega_cluster_infinite_of_cut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d)
    (h : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    (cluster d ω a).Infinite := by
  apply h.mono
  intro z hz
  rw [mem_cluster] at hz ⊢
  exact bc61_connected_of_cut hz




theorem bc81_cut_cluster_infinite_of_coarse (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite ∧
      
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hinf₁, hinf₂, hinf₃⟩, hcut⟩ := h
  exact ⟨a₁, a₂, a₃,
    bc81_omega_cluster_infinite_of_cut ω L y a₁ hinf₁,
    bc81_omega_cluster_infinite_of_cut ω L y a₂ hinf₂,
    bc81_omega_cluster_infinite_of_cut ω L y a₃ hinf₃, hcut⟩





theorem bc81_infinite_clusters_coincide_of_le_one (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d}
    (hN : numInfiniteClusters d ω ≤ 1)
    (ha : (cluster d ω a).Infinite) (hb : (cluster d ω b).Infinite) :
    Connected d ω a b := by
  have hmemA : cluster d ω a ∈ infiniteClusters d ω := ⟨ha, a, rfl⟩
  have hmemB : cluster d ω b ∈ infiniteClusters d ω := ⟨hb, b, rfl⟩
  have hss : (infiniteClusters d ω).encard ≤ 1 := hN
  rw [Set.encard_le_one_iff] at hss
  have heq : cluster d ω a = cluster d ω b := hss _ _ hmemA hmemB
  have : b ∈ cluster d ω a := by rw [heq]; exact self_mem_cluster ω b
  exact this








theorem bc81_coarseTrif_arms_connected_of_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hN : numInfiniteClusters d ω ≤ 1) (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃ ∧
      
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hinf₁, hinf₂, hinf₃, hcut⟩ := bc81_cut_cluster_infinite_of_coarse ω L h
  exact ⟨a₁, a₂, a₃,
    bc81_infinite_clusters_coincide_of_le_one ω hN hinf₁ hinf₂,
    bc81_infinite_clusters_coincide_of_le_one ω hN hinf₁ hinf₃,
    bc81_infinite_clusters_coincide_of_le_one ω hN hinf₂ hinf₃, hcut⟩














theorem bc81_route2_circular (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] :
    μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc79_finite_N_iff_top_null μ







theorem bc81_coarseTrif_consistent_with_le_one (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hN : numInfiniteClusters d ω ≤ 1) (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) ∧
      
      (Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, hcut⟩ :=
    bc81_coarseTrif_arms_connected_of_le_one ω L hN h
  exact ⟨a₁, a₂, a₃, hcut, hc₁₂, hc₁₃, hc₂₃⟩



















theorem bc81_route1_fails {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc76_buffer_insufficient hL












theorem bc81_leaf_noncircular (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R :=
  bc79_residue_noncircular μ L hinv h0




theorem bc81_bk_from_leaf (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc78_bk_closed μ hd L hinv h0 hexist



















theorem bc81_cardinal_verdict (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), numInfiniteClusters d ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d, Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) ∧
    
    (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, bc81_route2_circular μ, ?_⟩
  · intro ω y h
    obtain ⟨a₁, a₂, a₃, _, hcut⟩ := bc81_singleBox_no_gap ω L y h
    exact ⟨a₁, a₂, a₃, hcut⟩
  · intro ω y hN h
    obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, _⟩ := bc81_coarseTrif_arms_connected_of_le_one ω L hN h
    exact ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃⟩
  · intro h0 hexist; exact bc81_bk_from_leaf μ hd L hinv h0 hexist



























theorem bc81_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site 2,
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), numInfiniteClusters 2 ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L y h
    obtain ⟨a₁, a₂, a₃, _, hcut⟩ := bc81_singleBox_no_gap ω L y h
    exact ⟨a₁, a₂, a₃, hcut⟩
  · intro ω L y hN h
    obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, _⟩ := bc81_coarseTrif_arms_connected_of_le_one ω L hN h
    exact ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃⟩
  · intro μ _; exact bc81_route2_circular μ
  · intro L hL; exact (bc81_route1_fails hL).2.2
  · intro μ _ L hinv h0 hexist; exact bc81_bk_from_leaf μ (by norm_num) L hinv h0 hexist

end StatMech.Walls
