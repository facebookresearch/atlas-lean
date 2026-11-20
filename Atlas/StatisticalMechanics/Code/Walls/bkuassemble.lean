/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.bktcuttransfer
import Code.Walls.svccontraction

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













def bku_armPathCarrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type)) : Prop :=
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
    ∃ t₁ t₂ t₃ : (↑S : Type),
      bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
      ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
      G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
      ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃






theorem bku_armPathCarrier_closes_bc69
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (harm : bku_armPathCarrier ω L R G ιU)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R :=
  bkf_connectedForest_closes ω L R G hGac ιU harm hinj hFmin














theorem bku_armPathCarrier_of_cutTransfer
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type))
    (htrans : bkf_CutTransfer ω L R G ιU)
    (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d)) :
    bku_armPathCarrier ω L R G ιU :=
  bkf_harm_of_cutTransfer_and_targets ω L R G ιU htrans htargets





theorem bku_bc69_of_cutTransfer_and_targets
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (htrans : bkf_CutTransfer ω L R G ιU)
    (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d))
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R :=
  bkf_connectedForest_closes_of_cutTransfer ω L R G hGac ιU htrans htargets hinj hFmin













theorem bku_within_hub_boundary_targets (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
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
      ((bc67_contractedLattice ω L y).Reachable a₁ z₁ ∧
       (bc67_contractedLattice ω L y).Reachable a₂ z₂ ∧
       (bc67_contractedLattice ω L y).Reachable a₃ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) :=
  bkf_arm_reaches_boundary_targets ω L R hR y a₁ a₂ a₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃







theorem bku_perHub_cutTransfer_holds (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
    ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) :=
  bkt_perHub_cutTransfer ω L y a b hcut








open Classical in







theorem bku_bk_closes_of_armPathCarrier (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  (bc120_bk_uniqueness_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute).2.2
























theorem bku_overconnection_relocated :
    ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4 :=
  bgf_perNode_cut_needs_common_carrier







theorem bku_box_overconnects (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y)
    (hia : bc67_GnIncident ω L y a) (hib : bc67_GnIncident ω L y b) :
    (bkt_ctrGraph ω L y).Reachable (some a) (some b) :=
  bkt_box_overconnects ω L y a b ha hb hia hib






theorem bku_horn_A_leaf_in_box (hd : 1 ≤ d) {L : ℕ} (hL : 3 ≤ L) (y : Site d)
    {k : ℤ} (hk : k ∈ bc112_shifts) :
    bc112_leaf hd y k ∈ bc61_boxAround d L y :=
  svc_horn_A_leaf_in_box hd hL y hk







theorem bku_armPathCarrier_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type))
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bku_armPathCarrier ω L R G ιU := by
  intro y hybox htri; exact absurd htri (hno y hybox)




theorem bku_route_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bkf_nonvacuous ω L R hz₀ hz₁ hzne hno





















































theorem bku_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
      {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
      (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic →
      ∀ (ιU : Site d → (↑S : Type)), bku_armPathCarrier ω L R G ιU →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) →
      (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
        (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
        (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
          G.Reachable a b → F.Reachable a b) →
        ∀ v : (↑S : Type), 1 ≤ F.degree v) →
      bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d),
      ¬ (bc67_contractedLattice ω L y).Reachable a b →
      ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b)) ∧
    
    (((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R S _ _ G _ hGac ιU harm hinj hFmin
    exact bku_armPathCarrier_closes_bc69 ω L R G hGac ιU harm hinj hFmin
  · intro ω L y a b hcut; exact bku_perHub_cutTransfer_holds ω L y a b hcut
  · exact bku_overconnection_relocated

end StatMech.Walls
