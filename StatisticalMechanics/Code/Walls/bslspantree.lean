/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.bc121trifcount
import Code.Walls.bgfglobalforest
import Code.Walls.bc118pathmember
import Code.Walls.bc110globalforest

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














theorem bsl_count_via_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R h





theorem bsl_unconditional_leaf_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc118_count_unconditional_leaf_bound G hacyc hmin










open Classical in






theorem bsl_globalForest_of_connected_carrier
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R :=
  bc121_globalForest_of_peel2 ω L R G hGac ιU harm hinj hFmin

open Classical in






theorem bsl_spanForest_is_valid_carrier
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G₀ : SimpleGraph (↑S : Type)) [DecidableRel (osf_spanForest G₀).Adj]
    (ιU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        (osf_spanForest G₀).Reachable (ιU y) t₁ ∧ (osf_spanForest G₀).Reachable (ιU y) t₂ ∧
        (osf_spanForest G₀).Reachable (ιU y) t₃ ∧
        ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ ((osf_spanForest G₀).deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ osf_spanForest G₀ →
      F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        (osf_spanForest G₀).Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R :=
  bsl_globalForest_of_connected_carrier ω L R (osf_spanForest G₀) (osf_spanForest_acyclic G₀)
    ιU harm hinj hFmin

















theorem bsl_connected_needs_no_injection
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    
    bc69_Gn_globalForest ω L R ∧ bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
  have h69 := bsl_globalForest_of_connected_carrier ω L R G hGac ιU harm hinj hFmin
  exact ⟨h69, bsl_count_via_connectedForest ω L R h69⟩















theorem bsl_withinHub_targets_free (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a₁ a₂ a₃ : Site d)
    (hb₁ : a₁ ∈ box d R) (hb₂ : a₂ ∈ box d R) (hb₃ : a₃ ∈ box d R)
    (hi₁ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite)
    (hi₂ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite)
    (hi₃ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite)
    (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, z₂, z₃, hzb, _hr, hsep, hdist⟩ :=
    bgf_gnTrif_three_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, hzb, hsep, hdist⟩

















theorem bsl_perNode_cut_still_cross_hub :
    
    ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4 :=
  bgf_perNode_cut_needs_common_carrier





theorem bsl_obstruction_carrier_is_connected :
    (SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).Reachable 1 4 := by
  classical
  set G : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet
    {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)} with hG
  have h10 : G.Adj 1 0 := by rw [hG, SimpleGraph.fromEdgeSet_adj]; exact ⟨by left; rfl, by decide⟩
  have h02 : G.Adj 0 2 := by rw [hG, SimpleGraph.fromEdgeSet_adj]; exact ⟨by right; left; rfl, by decide⟩
  have h23 : G.Adj 2 3 := by rw [hG, SimpleGraph.fromEdgeSet_adj]; exact ⟨by right; right; left; rfl, by decide⟩
  have h34 : G.Adj 3 4 := by rw [hG, SimpleGraph.fromEdgeSet_adj]; exact ⟨by right; right; right; rfl, by decide⟩
  exact ((h10.reachable.trans h02.reachable).trans h23.reachable).trans h34.reachable








theorem bsl_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bsl_count_via_connectedForest ω L R (bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)









































theorem bsl_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bsl_count_via_connectedForest ω L R h
  · intro V _ G; exact osf_spanForest_acyclic G
  · intro V _ _ G _ hac hmin; exact bsl_unconditional_leaf_bound G hac hmin
  · exact bsl_perNode_cut_still_cross_hub

end StatMech.Walls
