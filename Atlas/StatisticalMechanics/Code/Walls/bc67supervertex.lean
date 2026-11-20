/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































































import Mathlib
import Code.Walls.bc66assembly
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}






















def bc67_GnIncident (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d) : Prop :=
  ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a








noncomputable def bc67_contractedLattice (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    SimpleGraph (Site d) :=
  openSubgraph d (removeSites (bc61_boxAround d L y) ω)


theorem bc67_contractedLattice_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Adj a b ↔
      (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b :=
  Iff.rfl






theorem bc67_Gn_deletion_eq_removeSites (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Reachable a b ↔
      Connected d (removeSites (bc61_boxAround d L y) ω) a b :=
  Iff.rfl



theorem bc67_contractedLattice_le (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc67_contractedLattice ω L y ≤ openSubgraph d ω :=
  openSubgraph_mono (bc61_removeBox_le d L y ω)



theorem bc67_connected_of_Gn {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a b : Site d}
    (h : (bc67_contractedLattice ω L y).Reachable a b) : Connected d ω a b :=
  bc61_connected_of_cut ((bc67_Gn_deletion_eq_removeSites ω L y a b).mp h)
















def bc67_IsGnTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    
    (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
    
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    
    (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)

















theorem bc67_gnTrif_of_coarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) : bc67_IsGnTrifurcation ω L y := by
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃,
    ⟨⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩,
    ⟨hcut₁₂, hcut₁₃, hcut₂₃⟩⟩






theorem bc67_coarseTrif_of_gnTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc67_IsGnTrifurcation ω L y) : bc61_IsCoarseTrifurcation ω L y := by
  obtain ⟨a₁, a₂, a₃, ⟨hin₁, hin₂, hin₃⟩, ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hin₁, hin₂, hin₃, ⟨hinf₁, hinf₂, hinf₃⟩, ⟨hcut₁₂, hcut₁₃, hcut₂₃⟩⟩






theorem bc67_coarseTrif_is_G_n_trifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y :=
  ⟨bc67_gnTrif_of_coarseTrif ω L y, bc67_coarseTrif_of_gnTrif ω L y⟩














theorem bc67_upperLines_is_G_n_trifurcation {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc67_gnTrif_of_coarseTrif bc60_upperLines L 0 (bc61_wholeBox_severs_upperLines hL)






theorem bc67_upperLines_Gn_severs {L : ℕ} (_hL : 3 ≤ L) :
    ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) := by
  rw [bc67_Gn_deletion_eq_removeSites]
  exact bc61_upperLines_arm_disconnected (by norm_num)
















theorem bc67_Gn_arm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z := by
  obtain ⟨z, hz, hconn⟩ := bc66_coarse_armReaching_unconditional ω L R hR y a habox hinf
  exact ⟨z, hz, (bc67_Gn_deletion_eq_removeSites ω L y a z).mpr hconn⟩







theorem bc67_Gn_singleVertex_trifurcation_degree (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (y : Site d) (h : bc67_IsGnTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, _, hcuts⟩ := h
  exact ⟨a₁, a₂, a₃, hincs, hcuts⟩

















theorem bc67_Gn_armForest_of_forestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιU : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R := by
  refine bc66_connectedForest_of_forestData ω L R W G ιU lamL hacyc hmin ?_ ?_ hlammap hlaminj
  · 
    intro y hybox htri
    exact hdeg3 y hybox ((bc67_coarseTrif_is_G_n_trifurcation ω L y).mp htri)
  · 
    intro y hybox htri z hzbox htriz hyz
    exact hιinj y hybox ((bc67_coarseTrif_is_G_n_trifurcation ω L y).mp htri)
      z hzbox ((bc67_coarseTrif_is_G_n_trifurcation ω L z).mp htriz) hyz





theorem bc67_Gn_armForest_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιU : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc65_coarseTcount_le_boundary_of_connectedForest ω L R
    (bc67_Gn_armForest_of_forestData ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj)














theorem bc67_infiniteClusters_top_null_of_GnForest_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGnforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc66_infiniteClusters_top_null_of_connectedForest μ hd hinv hfe L hGnforest hcoarseRoute

































theorem bc67_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d),
      (bc67_contractedLattice ω L y).Reachable a b ↔
        Connected d (removeSites (bc61_boxAround d L y) ω) a b) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    
    (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L y a b; exact bc67_Gn_deletion_eq_removeSites ω L y a b
  · intro ω L y; exact bc67_coarseTrif_is_G_n_trifurcation ω L y
  · intro ω L R hR y a habox hinf; exact bc67_Gn_arm_reaches_boundary ω L R hR y a habox hinf
  · intro L hL; exact bc67_upperLines_is_G_n_trifurcation hL

end StatMech.Walls
