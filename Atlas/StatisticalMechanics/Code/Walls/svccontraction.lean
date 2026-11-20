/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Walls.bc112sepcontract
import Code.Walls.bc120closure
import Code.Walls.bgfglobalforest
import Code.Walls.bslspantree

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














theorem svc_gap1_discharged (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hL : 3 ≤ L) :
    bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_holds hd ω L R hL













theorem svc_full_separated_iff_gap2 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R :=
  bc112_boundaryLeafResidue_iff_full ω L R






theorem svc_full_separated_of_gap1_and_boundaryLeaf
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (hSfin : Fintype (↑S : Type)) (hSne : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (hGdec : DecidableRel G.Adj)
    (hFdec : DecidableRel (osf_spanForest G).Adj) (ιU : Site d → (↑S : Type))
    (hnbr : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y →
      ∃ v₁ v₂ v₃ : (↑S : Type),
        G.Adj (ιU y) v₁ ∧ G.Adj (ιU y) v₂ ∧ G.Adj (ιU y) v₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₂ v₃)
    (hιinj : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∀ z, z ∈ box d R →
      bc106_SeparatedCoarseTrif ω L z → ιU y = ιU z → y = z)
    (hmin : ∀ v, 1 ≤ (osf_spanForest G).degree v)
    (hleaf : ∀ v : (↑S : Type), (osf_spanForest G).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    bc106_SeparatedContractedTrifGraph ω L R :=
  bc106_separatedContracted_of_gap1_gap2 ω L R hSfin hSne G hGdec hFdec ιU hnbr hιinj hmin hleaf










theorem svc_separated_count_le_boundary_of_full (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc106_SeparatedContractedTrifGraph ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc106_separatedCount_of_contractedGraph ω L R h














theorem svc_count_absorbs_sharing {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc102_leaf_count_absorbs_shared G hacyc hmin




theorem svc_origin_event_eq (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d) :=
  bc106_origin_event_eq ω L





theorem svc_separated_drives_dichotomy
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc106_separated_drives_dichotomy μ hd L hexp hforest hexist














theorem svc_horn_A_leaf_in_box (hd : 1 ≤ d) {L : ℕ} (hL : 3 ≤ L) (y : Site d)
    {k : ℤ} (hk : k ∈ bc112_shifts) :
    bc112_leaf hd y k ∈ bc61_boxAround d L y :=
  bc112_leaf_mem_own_box hd hL y hk





















theorem svc_horn_incompatibility :
    ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4 :=
  bsl_perNode_cut_still_cross_hub




theorem svc_horn_incompatibility_connected :
    (SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).Reachable 1 4 :=
  bsl_obstruction_carrier_is_connected













theorem svc_withinHub_boundary_targets (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
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
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, z₂, z₃, hzb, _hr, _hsep, hdist⟩ :=
    bgf_gnTrif_three_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, hzb, hdist⟩














theorem svc_bk_top_null_of_gap2
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp hforest hexist







theorem svc_bk_uniqueness_of_gap2 (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  (bc120_bk_uniqueness_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute).2.2






theorem svc_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) {z₀ : Site d}
    (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
    bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_of_noTrif (z₀ := z₀) ω L R hno

















































theorem svc_status :
    
    (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L →
      bc112_SeparatedArmGraph ω L R) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R) ∧
    
    (∀ (hd : 1 ≤ d) (L : ℕ), 3 ≤ L → ∀ (y : Site d) {k : ℤ}, k ∈ bc112_shifts →
      bc112_leaf hd y k ∈ bc61_boxAround d L y) ∧
    
    (((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hd ω L R hL; exact svc_gap1_discharged hd ω L R hL
  · intro V _ _ G _ hac hmin; exact svc_count_absorbs_sharing G hac hmin
  · intro ω L R; exact svc_full_separated_iff_gap2 ω L R
  · intro hd L hL y k hk; exact svc_horn_A_leaf_in_box hd hL y hk
  · exact svc_horn_incompatibility

end StatMech.Walls
