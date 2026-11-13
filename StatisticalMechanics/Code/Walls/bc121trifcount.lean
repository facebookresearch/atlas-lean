/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.Walls.bc112sepcontract
import Code.Walls.bc118pathmember

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






noncomputable def bc121_badLeaves {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : V → Prop) [DecidablePred B] : Finset V :=
  univ.filter (fun v => G.degree v = 1 ∧ ¬ B v)



def bc121_BAnchored {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (B : V → Prop) : Prop :=
  F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v)








theorem bc121_leaf_has_neighbour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} (hv : G.degree v = 1) : ∃ w, G.Adj v w := by
  classical
  have : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree, hv]; exact one_pos
  obtain ⟨w, hw⟩ := this
  exact ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mp hw⟩



theorem bc121_leaf_neighbour_unique {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w w' : V} (hv : G.degree v = 1) (hw : G.Adj v w) (hw' : G.Adj v w') :
    w = w' := by
  classical
  have hcard : (G.neighborFinset v).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hv
  have hmemw : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw
  have hmemw' : w' ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw'
  exact Finset.card_le_one.mp (le_of_eq hcard) w hmemw w' hmemw'















theorem bc121_leaf_delete_reachable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hdeg : G.degree v = 1) (hvw : G.Adj v w)
    {a b : V} (ha : a ≠ v) (hb : b ≠ v) (hreach : G.Reachable a b) :
    (G.deleteEdges {s(v, w)}).Reachable a b := by
  classical
  obtain ⟨p⟩ := hreach
  
  
  
  suffices H : ∀ (n : ℕ) {x y : V} (q : G.Walk x y), q.length ≤ n → x ≠ v → y ≠ v →
      (G.deleteEdges {s(v, w)}).Reachable x y by
    exact H p.length p le_rfl ha hb
  intro n
  induction n with
  | zero =>
    intro x y q hlen hx hy
    
    rw [Nat.le_zero, SimpleGraph.Walk.length_eq_zero_iff] at hlen
    cases hlen; exact Reachable.refl _
  | succ n ih =>
    intro x y q hlen hx hy
    cases q with
    | nil => exact Reachable.refl _
    | @cons x c y hxc r =>
      
      have hrlen : r.length ≤ n := by
        simp only [SimpleGraph.Walk.length_cons] at hlen; omega
      by_cases hcv : c = v
      · 
        
        have hxv : G.Adj x v := hcv ▸ hxc
        have hxw : x = w := (bc121_leaf_neighbour_unique G hdeg hvw hxv.symm).symm
        cases r with
        | nil => rw [hcv] at hy; exact absurd rfl hy  
        | @cons c e y hce s =>
          have hve : G.Adj v e := hcv ▸ hce
          have hew : e = w := (bc121_leaf_neighbour_unique G hdeg hvw hve).symm
          have hene : e ≠ v := by rw [hew]; exact hvw.ne'
          have hslen : s.length ≤ n := by
            simp only [SimpleGraph.Walk.length_cons] at hrlen; omega
          have hr : (G.deleteEdges {s(v, w)}).Reachable e y := ih s hslen hene hy
          
          have hxe : x = e := by rw [hxw, hew]
          rw [hxe]; exact hr
      · 
        have hedge : (G.deleteEdges {s(v, w)}).Adj x c := by
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hxc, ?_⟩
          intro hmem
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
          rcases hmem with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hx h1
          · exact hcv h2
        exact (hedge.reachable).trans (ih r hrlen hcv hy)







theorem bc121_deleteEdge_card_lt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hvw : G.Adj v w)
    [DecidableRel (G.deleteEdges {s(v, w)}).Adj] :
    (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))]
  refine ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw, ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges]
  intro hmem
  exact hmem.2 (Set.mem_singleton _)


theorem bc121_deleteEdge_acyclic {V : Type*} (G : SimpleGraph V) (hacyc : G.IsAcyclic)
    (s : Set (Sym2 V)) : (G.deleteEdges s).IsAcyclic :=
  hacyc.anti (SimpleGraph.deleteEdges_le s)




















theorem bc121_boundaryAnchored_subforest {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : V → Prop) [DecidablePred B] (hacyc : G.IsAcyclic) :
    ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
      F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
      (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) := by
  classical
  
  suffices H : ∀ (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic →
      G.edgeFinset.card ≤ n →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
        (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) by
    exact H G.edgeFinset.card G hacyc le_rfl
  intro n
  induction n with
  | zero =>
    
    intro G _ hac hcard
    refine ⟨G, inferInstance, le_refl G, hac, ?_, fun a b _ _ h => h⟩
    intro v hv
    
    exfalso
    obtain ⟨w, hvw⟩ := bc121_leaf_has_neighbour G hv
    have : 1 ≤ G.edgeFinset.card := by
      apply Finset.card_pos.mpr
      exact ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw⟩
    omega
  | succ n ih =>
    intro G _ hac hcard
    by_cases hbad : ∃ v, G.degree v = 1 ∧ ¬ B v
    · 
      obtain ⟨v, hvdeg, hvB⟩ := hbad
      obtain ⟨w, hvw⟩ := bc121_leaf_has_neighbour G hvdeg
      have hG'ac : (G.deleteEdges {s(v, w)}).IsAcyclic := bc121_deleteEdge_acyclic G hac _
      have hlt : (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card :=
        bc121_deleteEdge_card_lt G hvw
      have hle' : (G.deleteEdges {s(v, w)}).edgeFinset.card ≤ n := by omega
      obtain ⟨F, hFdec, hFle, hFac, hFleaf, hFpres⟩ :=
        ih (G.deleteEdges {s(v, w)}) hG'ac hle'
      refine ⟨F, hFdec, le_trans hFle (SimpleGraph.deleteEdges_le _), hFac, hFleaf, ?_⟩
      intro a b hBa hBb hab
      apply hFpres a b hBa hBb
      have hav : a ≠ v := fun h => hvB (h ▸ hBa)
      have hbv : b ≠ v := fun h => hvB (h ▸ hBb)
      exact bc121_leaf_delete_reachable G hvdeg hvw hav hbv hab
    · 
      simp only [not_exists, not_and, not_not] at hbad
      exact ⟨G, inferInstance, le_refl G, hac, fun v hv => hbad v hv, fun a b _ _ h => h⟩















theorem bc121_firstNeighbour_of_reachable {V : Type*} {F : SimpleGraph V} {u t : V}
    (hne : u ≠ t) (hreach : F.Reachable u t) :
    ∃ w, F.Adj u w ∧ (F.deleteIncidenceSet u).Reachable w t := by
  classical
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ w _ hadjuw q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hqpath, huq⟩ := hp
    refine ⟨w, hadjuw, ?_⟩
    
    have hqavoid : ∀ x ∈ q.support, x ≠ u := by
      intro x hx hxu; subst hxu; exact huq hx
    
    exact bc103_reachable_deleteIncidence_of_walk_avoiding (le_refl F) u q hqavoid






theorem bc121_deg3_of_three_reached_targets {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] {u t₁ t₂ t₃ : V}
    (hne₁ : u ≠ t₁) (hne₂ : u ≠ t₂) (hne₃ : u ≠ t₃)
    (hr₁ : F.Reachable u t₁) (hr₂ : F.Reachable u t₂) (hr₃ : F.Reachable u t₃)
    (hcut₁₂ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂)
    (hcut₁₃ : ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃)
    (hcut₂₃ : ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃) :
    3 ≤ F.degree u := by
  classical
  obtain ⟨w₁, hw₁adj, hw₁r⟩ := bc121_firstNeighbour_of_reachable hne₁ hr₁
  obtain ⟨w₂, hw₂adj, hw₂r⟩ := bc121_firstNeighbour_of_reachable hne₂ hr₂
  obtain ⟨w₃, hw₃adj, hw₃r⟩ := bc121_firstNeighbour_of_reachable hne₃ hr₃
  have hw12 : w₁ ≠ w₂ := by
    intro h; apply hcut₁₂; exact hw₁r.symm.trans (h ▸ hw₂r)
  have hw13 : w₁ ≠ w₃ := by
    intro h; apply hcut₁₃; exact hw₁r.symm.trans (h ▸ hw₃r)
  have hw23 : w₂ ≠ w₃ := by
    intro h; apply hcut₂₃; exact hw₂r.symm.trans (h ▸ hw₃r)
  exact bc71_deg3_of_three_neighbours F hw₁adj hw₂adj hw₃adj hw12 hw13 hw23






















def bc121_Protected (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (ιU : Site d → (↑S : Type)) (v : (↑S : Type)) : Prop :=
  (v : Site d) ∈ vertexBoundary d R ∨
    (∃ y, y ∈ box d R ∧ bc67_IsGnTrifurcation ω L y ∧ ιU y = v)

open Classical in














theorem bc121_globalForest_of_peel2
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
    bc69_Gn_globalForest ω L R := by
  classical
  
  set P : (↑S : Type) → Prop := bc121_Protected ω L R ιU with hP
  haveI : DecidablePred P := Classical.decPred _
  obtain ⟨F, hFdec, hFle, hFac, hFleafP, hFpres⟩ :=
    bc121_boundaryAnchored_subforest G P hGac
  
  have hFmin' : ∀ v : (↑S : Type), 1 ≤ F.degree v := hFmin F hFle hFac hFleafP hFpres
  
  have hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ F.degree (ιU y) := by
    intro y hybox htri
    obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, hne₁, hne₂, hne₃, hgr₁, hgr₂, hgr₃,
      hgc₁₂, hgc₁₃, hgc₂₃⟩ := harm y hybox htri
    
    have hhubP : P (ιU y) := Or.inr ⟨y, hybox, htri, rfl⟩
    
    have hfr₁ : F.Reachable (ιU y) t₁ := hFpres _ _ hhubP hp₁ hgr₁
    have hfr₂ : F.Reachable (ιU y) t₂ := hFpres _ _ hhubP hp₂ hgr₂
    have hfr₃ : F.Reachable (ιU y) t₃ := hFpres _ _ hhubP hp₃ hgr₃
    
    have hdile : F.deleteIncidenceSet (ιU y) ≤ G.deleteIncidenceSet (ιU y) := by
      intro a b hab
      rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
      exact ⟨hFle hab.1, hab.2.1, hab.2.2⟩
    have hcutmono : ∀ t t' : (↑S : Type),
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t t' →
        ¬ (F.deleteIncidenceSet (ιU y)).Reachable t t' := by
      intro t t' hg hf
      exact hg (hf.mono hdile)
    exact bc121_deg3_of_three_reached_targets F hne₁ hne₂ hne₃ hfr₁ hfr₂ hfr₃
      (hcutmono t₁ t₂ hgc₁₂) (hcutmono t₁ t₃ hgc₁₃) (hcutmono t₂ t₃ hgc₂₃)
  
  
  have hFleaf : ∀ v : (↑S : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d R := by
    intro v hv
    rcases hFleafP v hv with hb | ⟨y, hybox, htri, hyv⟩
    · exact hb
    · 
      exfalso
      have : 3 ≤ F.degree v := hyv ▸ hdeg3 y hybox htri
      omega
  exact ⟨S, hSfin, hSne, F, hFdec, ιU, hFac, hFmin', hdeg3, hinj, hFleaf⟩








theorem bc121_count_via_peel2
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
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R
    (bc121_globalForest_of_peel2 ω L R G hGac ιU harm hinj hFmin)






theorem bc121_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R (bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)











































theorem bc121_status :
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (B : V → Prop) [DecidablePred B], G.IsAcyclic →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
        (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b)) ∧
    
    (∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj] (u t₁ t₂ t₃ : V),
      u ≠ t₁ → u ≠ t₂ → u ≠ t₃ →
      F.Reachable u t₁ → F.Reachable u t₂ → F.Reachable u t₃ →
      ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂ →
      ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃ →
      ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃ →
      3 ≤ F.degree u) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ G _ B _ hac; exact bc121_boundaryAnchored_subforest G B hac
  · intro V _ F _ u t₁ t₂ t₃ h₁ h₂ h₃ r₁ r₂ r₃ c₁₂ c₁₃ c₂₃
    exact bc121_deg3_of_three_reached_targets F h₁ h₂ h₃ r₁ r₂ r₃ c₁₂ c₁₃ c₂₃
  · intro ω L R h; exact bc118_count_closes_via_forest ω L R h

end StatMech.Walls
