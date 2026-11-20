/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Walls.bc121trifcount
import Code.Walls.bc112sepcontract

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}













theorem bc123_cut_forces_distinct {V : Type*} (G : SimpleGraph V) {u t₁ t₂ : V}
    (hcut : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂) : t₁ ≠ t₂ := by
  intro h; exact hcut (h ▸ SimpleGraph.Reachable.refl t₁)




theorem bc123_within_hub_distinct {V : Type*} (G : SimpleGraph V) {u t₁ t₂ t₃ : V}
    (hc₁₂ : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂)
    (hc₁₃ : ¬ (G.deleteIncidenceSet u).Reachable t₁ t₃)
    (hc₂₃ : ¬ (G.deleteIncidenceSet u).Reachable t₂ t₃) :
    t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ :=
  ⟨bc123_cut_forces_distinct G hc₁₂, bc123_cut_forces_distinct G hc₁₃,
   bc123_cut_forces_distinct G hc₂₃⟩




















theorem bc123_count_tolerates_shared_leaves {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc118_count_unconditional_leaf_bound G hacyc hmin









theorem bc123_shared_tip_breaks_cut :
    ((SimpleGraph.fromEdgeSet {s((0 : Fin 3), 2), s((1 : Fin 3), 2)}).deleteIncidenceSet
        (0 : Fin 3)).Reachable 2 1 := by
  classical
  
  have hadj : ((SimpleGraph.fromEdgeSet {s((0 : Fin 3), 2), s((1 : Fin 3), 2)}).deleteIncidenceSet
      (0 : Fin 3)).Adj 2 1 := by
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨?_, by decide, by decide⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, by decide⟩
    right
    rw [Sym2.eq_swap]; rfl
  exact hadj.reachable
















theorem bc123_gap1_finiteCarrier (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hL : 3 ≤ L) : bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_holds hd ω L R hL















theorem bc123_count_from_boundaryLeafResidue (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc112_BoundaryLeafResidue ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc106_separatedCount_of_contractedGraph ω L R
    ((bc112_boundaryLeafResidue_iff_full ω L R).mp h)








theorem bc123_separatedCount_closes_of_residue (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc112_BoundaryLeafResidue ω L R →
      (bc106_SeparatedContractedTrifGraph ω L R ∧
       bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
  intro h
  exact ⟨(bc112_boundaryLeafResidue_iff_full ω L R).mp h,
    bc123_count_from_boundaryLeafResidue ω L R h⟩











open Classical in






theorem bc123_globalForest_via_peel2_finiteCarrier
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    
    (harmAdj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        G.Adj (ιU y) t₁ ∧ G.Adj (ιU y) t₂ ∧ G.Adj (ιU y) t₃ ∧
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
    bc69_Gn_globalForest ω L R := by
  classical
  refine bc121_globalForest_of_peel2 ω L R G hGac ιU ?_ hinj hFmin
  intro y hybox htri
  obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, ha₁, ha₂, ha₃, hc₁₂, hc₁₃, hc₂₃⟩ := harmAdj y hybox htri
  
  
  exact ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, ha₁.ne, ha₂.ne, ha₃.ne,
    ha₁.reachable, ha₂.reachable, ha₃.reachable, hc₁₂, hc₁₃, hc₂₃⟩








theorem bc123_count_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
  have hfull : bc106_SeparatedContractedTrifGraph ω L R :=
    bc106_separatedContractedTrifGraph_of_noTrif ω L R hz₀ hz₁ hzne hno
  exact bc123_count_from_boundaryLeafResidue ω L R
    ((bc112_boundaryLeafResidue_iff_full ω L R).mpr hfull)














































theorem bc123_status :
    
    (∀ {V : Type} (G : SimpleGraph V) (u t₁ t₂ t₃ : V),
      ¬ (G.deleteIncidenceSet u).Reachable t₁ t₂ →
      ¬ (G.deleteIncidenceSet u).Reachable t₁ t₃ →
      ¬ (G.deleteIncidenceSet u).Reachable t₂ t₃ →
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (((SimpleGraph.fromEdgeSet {s((0 : Fin 3), 2), s((1 : Fin 3), 2)}).deleteIncidenceSet
        (0 : Fin 3)).Reachable 2 1) ∧
    
    (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L →
      bc112_SeparatedArmGraph ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc112_BoundaryLeafResidue ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V G u t₁ t₂ t₃ hc₁₂ hc₁₃ hc₂₃; exact bc123_within_hub_distinct G hc₁₂ hc₁₃ hc₂₃
  · intro V _ _ G _ hacyc hmin; exact bc123_count_tolerates_shared_leaves G hacyc hmin
  · exact bc123_shared_tip_breaks_cut
  · intro hd ω L R hL; exact bc123_gap1_finiteCarrier hd ω L R hL
  · intro ω L R h; exact bc123_count_from_boundaryLeafResidue ω L R h

end StatMech.Walls
