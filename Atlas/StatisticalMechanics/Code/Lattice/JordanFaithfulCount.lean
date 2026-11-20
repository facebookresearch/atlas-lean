/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanOuterFaceUnique
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.JordanCycleRank
import Code.Lattice.JordanSeparationFinish
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional

open SimpleGraph Set

namespace StatMech

namespace Lattice


















theorem jfc_whb_sup_edge (G : SimpleGraph (Site 2)) {p q f0 g0 : Site 2} (hpq : p ≠ q)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q)) :
    whb_faceRegion (G ⊔ edge p q) = (whb_faceRegion G).deleteEdges {s(f0, g0)} := by
  ext f g
  rw [whb_faceRegion_adj, deleteEdges_adj, whb_faceRegion_adj]
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, not_or, Set.mem_singleton_iff]
  have hmem : sharedPrimalEdge f g ∈ (edge p q).edgeSet ↔ sharedPrimalEdge f g = s(p, q) :=
    jsf_mem_edgeSet_edge hpq _
  constructor
  · rintro ⟨hadj, hnG, hnE⟩
    refine ⟨⟨hadj, hnG⟩, ?_⟩
    intro heq
    apply hnE
    have : sharedPrimalEdge f g = sharedPrimalEdge f0 g0 :=
      (jce_sharedPrimalEdge_inj hadj hfg).mp heq
    rw [hmem, this, hshared]
  · rintro ⟨⟨hadj, hnG⟩, hne⟩
    refine ⟨hadj, hnG, ?_⟩
    intro hE
    apply hne
    rw [hmem, ← hshared] at hE
    exact (jce_sharedPrimalEdge_inj hadj hfg).mpr hE




theorem jfc_whb_bot : whb_faceRegion (⊥ : SimpleGraph (Site 2)) = hypercubicLattice 2 := by
  ext f g
  rw [whb_faceRegion_adj, SimpleGraph.edgeSet_bot]
  simp
















theorem jfc_sharedPrimalEdge_endpoint_not_box (R : ℕ) {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g)
    (hf : (f 0).natAbs ≥ R + 2 ∨ (f 1).natAbs ≥ R + 2) {v : Site 2}
    (hv : v ∈ sharedPrimalEdge f g) : v ∉ box 2 R := by
  intro hbox
  rw [mem_box] at hbox
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  unfold sharedPrimalEdge at hv
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0] at hv
    rw [Sym2.mem_iff] at hv
    have h0nat := hbox 0; have h1nat := hbox 1
    rcases hv with rfl | rfl <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0nat h1nat) <;> omega
  · rw [if_neg h0] at hv
    rw [Sym2.mem_iff] at hv
    have h0nat := hbox 0; have h1nat := hbox 1
    rcases hv with rfl | rfl <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0nat h1nat) <;> omega






theorem jfc_exterior_sharedEdge_not_mem (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2} (hf : f ∈ exterior 2 (R + 1))
    (hadj : (hypercubicLattice 2).Adj f g) : sharedPrimalEdge f g ∉ H.edgeSet := by
  intro hmem
  rw [mem_exterior] at hf
  obtain ⟨i, hi⟩ := hf
  have hfbig : (f 0).natAbs ≥ R + 2 ∨ (f 1).natAbs ≥ R + 2 := by
    fin_cases i
    · left; simpa using hi
    · right; simpa using hi
  
  obtain ⟨p, q, hpq_eq, _⟩ := sharedPrimalEdge_isLatticeEdge hadj
  rw [hpq_eq, SimpleGraph.mem_edgeSet] at hmem
  have hpsupp : p ∈ H.support := ⟨q, hmem⟩
  have hpbox : p ∈ box 2 R := hR _ hpsupp
  exact jfc_sharedPrimalEdge_endpoint_not_box R hadj hfbig (hpq_eq ▸ Sym2.mem_mk_left p q) hpbox




theorem jfc_whb_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2}
    (hf : f ∈ exterior 2 (R + 1)) (hadj : (hypercubicLattice 2).Adj f g) :
    (whb_faceRegion H).Adj f g :=
  ⟨hadj, jfc_exterior_sharedEdge_not_mem H R hR hf hadj⟩






theorem jfc_whb_regionComponents_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    Finite (whb_faceRegion H).ConnectedComponent := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box H.support (jei_support_finite H hfin)
  set RG := whb_faceRegion H with hRG
  set S : Set (Site 2) := box 2 (R + 1) ∪ {beacon 2 (R + 1)} with hS
  have hSfin : S.Finite := (box_finite 2 (R + 1)).union (Set.finite_singleton _)
  have hb_ext : beacon 2 (R + 1) ∈ exterior 2 (R + 1) := beacon_mem_exterior (R + 1) (by omega)
  have hExtMk : ∀ x : Site 2, x ∈ exterior 2 (R + 1) →
      RG.connectedComponentMk x = RG.connectedComponentMk (beacon 2 (R + 1)) := by
    intro x hx
    refine ConnectedComponent.sound ?_
    have hconn := box_exterior_connected (R + 1) (by omega) x (beacon 2 (R + 1)) hx hb_ext
    have hmap := hconn.map
      (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 (R + 1))) →g RG)
    · simpa using hmap
    · intro a b hab
      exact jfc_whb_adj_of_exterior H R (fun v hv => hR hv) a.2 hab
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 (R + 1)
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 (R + 1) := by rw [exterior_eq_compl_box]; exact hxbox
    refine ⟨beacon 2 (R + 1), Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 (R + 1)) = c
    rw [← hExtMk x hxext]; exact hx




theorem jfc_whb_pushGraph_regionComponents_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Finite (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent :=
  jfc_whb_regionComponents_finite _ (jei_pushGraph_edgeSet_finite P K)










theorem jfc_flankingFaces {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q) :
    ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧ sharedPrimalEdge f0 g0 = s(p, q) := by
  have hpq' := hpq
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq'
  have hadjface : ∀ a b : ℤ, (hypercubicLattice 2).Adj (![a, b] : Site 2) ![a - 1, b] := by
    intro a b; rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hadjface2 : ∀ a b : ℤ, (hypercubicLattice 2).Adj (![a, b] : Site 2) ![a, b - 1] := by
    intro a b; rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  by_cases h0 : p 0 = q 0
  · have hcase : q 1 = p 1 + 1 ∨ q 1 = p 1 - 1 := by omega
    rcases hcase with h1 | h1
    · refine ⟨![p 0, p 1], ![p 0 - 1, p 1], hadjface _ _, ?_⟩
      rw [sharedPrimalEdge_left (p 0) (p 1)]; unfold faceCorner00 faceCorner01
      have e1 : (![p 0, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp
      have e2 : (![p 0, p 1 + 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2]
    · refine ⟨![p 0, q 1], ![p 0 - 1, q 1], hadjface _ _, ?_⟩
      rw [sharedPrimalEdge_left (p 0) (q 1)]; unfold faceCorner00 faceCorner01
      have e1 : (![p 0, q 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      have e2 : (![p 0, q 1 + 1] : Site 2) = p := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2, Sym2.eq_swap]
  · have hcase : q 0 = p 0 + 1 ∨ q 0 = p 0 - 1 := by omega
    have h1 : p 1 = q 1 := by omega
    rcases hcase with h0' | h0'
    · refine ⟨![p 0, p 1], ![p 0, p 1 - 1], hadjface2 _ _, ?_⟩
      rw [sharedPrimalEdge_bottom (p 0) (p 1)]; unfold faceCorner00 faceCorner10
      have e1 : (![p 0, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp
      have e2 : (![p 0 + 1, p 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2]
    · refine ⟨![q 0, p 1], ![q 0, p 1 - 1], hadjface2 _ _, ?_⟩
      rw [sharedPrimalEdge_bottom (q 0) (p 1)]; unfold faceCorner00 faceCorner10
      have e1 : (![q 0, p 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      have e2 : (![q 0 + 1, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2, Sym2.eq_swap]






theorem jfc_flankingEdge_present (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
    s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P K)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
  refine ⟨hfg, ?_⟩
  rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst_vars
  exact hnotK hKuv
















theorem jfc_whb_delete_dichotomy (G : SimpleGraph (Site 2)) {p q f0 g0 : Site 2}
    [Finite (whb_faceRegion G).ConnectedComponent]
    [Finite (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent]
    (hpq : p ≠ q) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hpres : s(f0, g0) ∈ (whb_faceRegion G).edgeSet) :
    (((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 →
        Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (whb_faceRegion G).ConnectedComponent) ∧
      (¬ ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 →
        Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (whb_faceRegion G).ConnectedComponent + 1) := by
  classical
  set RG := whb_faceRegion G with hRG
  set RGdel := RG.deleteEdges {s(f0, g0)} with hRGdel_def
  have hRGdel : whb_faceRegion (G ⊔ edge p q) = RGdel :=
    jfc_whb_sup_edge G hpq hfg hshared
  haveI hfinDel : Finite RGdel.ConnectedComponent :=
    hRGdel ▸ (inferInstance : Finite (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent)
  have hdecomp : RG = RGdel ⊔ edge f0 g0 := by
    rw [hRGdel_def]
    exact jsf_deleteEdges_sup_edge_eq RG f0 g0 hpres
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rw [hRGdel]
    have hkeep := jsf_card_components_sup_edge_keep RGdel (a := f0) (b := g0) hr
    conv_rhs => rw [hdecomp]
    exact hkeep.symm
  · rw [hRGdel]
    have hmerge := jsf_card_components_sup_edge_merge RGdel (a := f0) (b := g0) hr
    rw [hdecomp]
    omega














def jfc_WhbSync (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → ∀ {x y : P.V}, P.G.Adj x y → ¬ K.Adj x y →
    ∀ {f0 g0 : Site 2}, (hypercubicLattice 2).Adj f0 g0 →
      sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y) →
      (K.Reachable x y ↔
        ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0)
















theorem jfc_whb_count_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    ∀ (K : SimpleGraph P.V), K ≤ P.G →
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
  classical
  have hVfin : Finite P.V := P.finV
  have hVdec : DecidableEq P.V := P.decV
  intro K
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    intro hKle
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · 
      subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      rw [jei_pushGraph_bot, jfc_whb_bot]
      have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
        have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
          fun a b => pbs_reach_all a b
        have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
          ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
        haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
          ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
        rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
      rw [hlat]
      unfold faceCount nullity
      rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
    · 
      have hnonempty : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hnonempty
      obtain ⟨x, y⟩ := e
      set K' := K.deleteEdges {s(x, y)} with hK'
      have hKeq : K = K' ⊔ edge x y := deleteEdges_sup_edge_eq K x y he
      have hadjK : K.Adj x y := by rwa [SimpleGraph.mem_edgeSet] at he
      have hne_xy : x ≠ y := K.ne_of_adj hadjK
      have hadjG : P.G.Adj x y := hKle hadjK
      have hnotK' : ¬ K'.Adj x y := by simp [hK', deleteEdges_adj]
      have hK'le : K' ≤ P.G := (deleteEdges_le _).trans hKle
      have hdrop : K'.edgeSet.ncard + 1 = K.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one K x y he
      have hn' : K'.edgeSet.ncard = n - 1 := by omega
      have ihK' : Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent = faceCount K' :=
        ih (n - 1) (by omega) K' hn' hK'le
      haveI hfinK' : Finite (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent :=
        jfc_whb_pushGraph_regionComponents_finite P K'
      haveI hfinK : Finite (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent :=
        jfc_whb_pushGraph_regionComponents_finite P K
      set p := P.emb x with hp
      set q := P.emb y with hq
      have hpushEq : jei_pushGraph P K = jei_pushGraph P K' ⊔ edge p q := by
        rw [hKeq, jei_pushGraph_sup_edge P K' x y hne_xy]
      have hpq : p ≠ q := fun h => hne_xy (P.emb.injective h)
      
      have hlatpq : (hypercubicLattice 2).Adj p q := P.isSub hadjG
      obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces hlatpq
      have hpres : s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P K')).edgeSet :=
        jfc_flankingEdge_present P K' hadjG hnotK' hfg hshared
      haveI hfinSup :
          Finite (whb_faceRegion (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [← hpushEq]; exact hfinK
      have hdich := jfc_whb_delete_dichotomy (jei_pushGraph P K') (p := p) (q := q)
        (f0 := f0) (g0 := g0) hpq hfg hshared hpres
      have hsyncK' := hsync K' hK'le hadjG hnotK' hfg hshared
      set DR := ((whb_faceRegion (jei_pushGraph P K')).deleteEdges
          {s(f0, g0)}).Reachable f0 g0 with hDR
      have hcardPush : Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
          = Nat.card (whb_faceRegion (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [hpushEq]
      by_cases hr : K'.Reachable x y
      · have hnotDR : ¬ DR := hsyncK'.mp hr
        have hdualCard := hdich.2 hnotDR
        have hface : faceCount K = faceCount K' + 1 := by
          rw [hKeq]; exact faceCount_sup_edge_of_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]
      · have hDRtrue : DR := by
          by_contra hcon
          exact hr (hsyncK'.mpr hcon)
        have hdualCard := hdich.1 hDRtrue
        have hface : faceCount K = faceCount K' := by
          rw [hKeq]; exact faceCount_sup_edge_of_not_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]












theorem jfc_imageGraph_support_box (P : PlanarZ2Subgraph) :
    ∀ v ∈ (imageGraph P).support, v ∈ box 2 (outerBoxRadius P) := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  rw [imageGraph_adj] at hw
  obtain ⟨s, t, _, hs, _⟩ := hw
  rw [← hs]; exact outerBoxRadius_spec P s



noncomputable def jfc_whb_outerRegion (P : PlanarZ2Subgraph) :
    (whb_faceRegion (imageGraph P)).ConnectedComponent :=
  (whb_faceRegion (imageGraph P)).connectedComponentMk (beacon 2 (outerBoxRadius P + 1))




theorem jfc_whb_exterior_in_outerRegion (P : PlanarZ2Subgraph) {x : Site 2}
    (hx : x ∈ exterior 2 (outerBoxRadius P + 1)) :
    (whb_faceRegion (imageGraph P)).connectedComponentMk x = jfc_whb_outerRegion P := by
  set R := outerBoxRadius P with hR
  set RG := whb_faceRegion (imageGraph P) with hRG
  have hb_ext : beacon 2 (R + 1) ∈ exterior 2 (R + 1) := beacon_mem_exterior (R + 1) (by omega)
  refine ConnectedComponent.sound ?_
  have hconn := box_exterior_connected (R + 1) (by omega) x (beacon 2 (R + 1)) hx hb_ext
  have hmap := hconn.map
    (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 (R + 1))) →g RG)
  · simpa using hmap
  · intro a b hab
    exact jfc_whb_adj_of_exterior (imageGraph P) R (jfc_imageGraph_support_box P) a.2 hab



theorem jfc_whb_outerRegion_infinite (P : PlanarZ2Subgraph) :
    (jfc_whb_outerRegion P).supp.Infinite := by
  set R := outerBoxRadius P with hR
  have : Infinite ↥(exterior 2 (R + 1)) := (exterior_infinite (R + 1) (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 (R + 1)) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact jfc_whb_exterior_in_outerRegion P w.2



theorem jfc_whb_infiniteComponent_meets_exterior (P : PlanarZ2Subgraph)
    {C : (whb_faceRegion (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P + 1) := by
  set R := outerBoxRadius P with hR
  by_contra hcon
  push Not at hcon
  have hsubbox : C.supp ⊆ box 2 (R + 1) := by
    intro v hv
    have hvnotext : v ∉ exterior 2 (R + 1) := hcon v hv
    rw [exterior_eq_compl_box, Set.mem_compl_iff, not_not] at hvnotext
    exact hvnotext
  exact hC ((box_finite 2 (R + 1)).subset hsubbox)





theorem jfc_whb_unique_infinite_component (P : PlanarZ2Subgraph) :
    ∃! C : (whb_faceRegion (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  refine ⟨jfc_whb_outerRegion P, jfc_whb_outerRegion_infinite P, ?_⟩
  intro C hCinf
  obtain ⟨x, hx_supp, hx_ext⟩ := jfc_whb_infiniteComponent_meets_exterior P hCinf
  have h1 : (whb_faceRegion (imageGraph P)).connectedComponentMk x = C :=
    (C.mem_supp_iff x).mp hx_supp
  have h2 : (whb_faceRegion (imageGraph P)).connectedComponentMk x = jfc_whb_outerRegion P :=
    jfc_whb_exterior_in_outerRegion P hx_ext
  rw [← h1, h2]




theorem jfc_whb_bounded_iff_ne_outer (P : PlanarZ2Subgraph)
    (C : (whb_faceRegion (imageGraph P)).ConnectedComponent) :
    C.supp.Finite ↔ C ≠ jfc_whb_outerRegion P := by
  constructor
  · intro hfin hcon
    rw [hcon] at hfin
    exact (jfc_whb_outerRegion_infinite P) hfin
  · intro hne
    by_contra hinf
    rw [Set.not_finite] at hinf
    exact hne ((jfc_whb_unique_infinite_component P).unique hinf (jfc_whb_outerRegion_infinite P))









theorem jfc_whb_bounded_add_one_eq_card (P : PlanarZ2Subgraph) :
    whc_faithfulRegionCount P + 1 =
      Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P)
      (Set.toFinite (imageGraph P).edgeSet)
  unfold whc_faithfulRegionCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight (jfc_whb_bounded_iff_ne_outer P)),
    card_subtype_ne_add_one (jfc_whb_outerRegion P)]










theorem jfc_whb_total_count_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jfc_whb_count_of_sync P hsync P.G le_rfl
  rwa [jei_pushGraph_G P] at h




theorem jfc_whb_faithfulRegionCount_eq_nullity_of_sync (P : PlanarZ2Subgraph)
    (hsync : jfc_WhbSync P) : whc_faithfulRegionCount P = nullity P.G := by
  have htot := jfc_whb_total_count_of_sync P hsync
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega








theorem jfc_faithfulDiscreteJordan_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jfc_whb_faithfulRegionCount_eq_nullity_of_sync P hsync
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩










theorem jfc_pushGraph_le_lattice (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G) :
    jei_pushGraph P K ≤ hypercubicLattice 2 := by
  rintro a b ⟨x, y, hadj, rfl, rfl⟩
  exact P.isSub (hKle hadj)


noncomputable def jfc_pushGraph_locallyFinite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G) : SimpleGraph.LocallyFinite (jei_pushGraph P K) := fun v =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun w hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (jfc_pushGraph_le_lattice P K hKle hw)))







theorem jfc_whbSync_step_of_evenContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G) {x y : P.V} (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
    (K.Reachable x y ↔
      ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
  classical
  haveI := jfc_pushGraph_locallyFinite P K hKle
  haveI hft : Fintype (jei_pushGraph P K).edgeSet := (jei_pushGraph_edgeSet_finite P K).fintype
  have htoFinset : @Set.toFinset _ (jei_pushGraph P K).edgeSet hft
      = (jei_pushGraph_edgeSet_finite P K).toFinset := by
    apply Finset.ext; intro e
    rw [Set.mem_toFinset, Set.Finite.mem_toFinset]
  rw [← htoFinset] at hcc
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
    rintro ⟨u, v, hKuv, hu, hv⟩
    exact hnotK ((P.emb.injective hu) ▸ (P.emb.injective hv) ▸ hKuv)
  have hbicond := jeb_correctWhitney_of_evenDegree (jei_pushGraph P K)
    (jfc_pushGraph_le_lattice P K hKle) (P.emb x) (P.emb y) f0 g0 (P.isSub hadjG) hnpq hfg
    hshared hcc
  rwa [jei_push_reachable_iff P K x y] at hbicond



















def jfc_EvenDegreeThreading : Prop :=
  ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jfc_WhbSync P





theorem jfc_faithfulCountResidue_of_threading (hthr : jfc_EvenDegreeThreading) :
    jeb_FaithfulCountResidue :=
  fun P hP => jfc_faithfulDiscreteJordan_of_sync P (hthr P hP)




theorem jfc_evenDegreeThreading_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jfc_WhbSync P := by
  intro K _ x y hadjG _ _ _ _ _
  rw [hG] at hadjG
  exact absurd hadjG (by simp)















theorem jfc_latadj_E (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jfc_latadj_N (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp




theorem jfc_sq_adj_of_ne_origin {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (hf : f ≠ ![0, 0]) (hg : g ≠ ![0, 0]) :
    (whb_faceRegion (imageGraph jbc_Pce)).Adj f g := by
  refine ⟨hadj, ?_⟩
  intro hmem
  rw [whc_shared_mem_square_iff f g hadj] at hmem
  rcases hmem with h | h | h | h <;>
    (rw [Sym2.eq_iff] at h;
     rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | exact hf rfl | exact hg rfl)



theorem jfc_sq_row_east (b : ℤ) (hb : b ≠ 0) (a : ℤ) (n : ℕ) :
    (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a + n, b] := by
  induction n with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have e : (![a + (↑(k + 1) : ℤ), b] : Site 2) = ![(a + (k : ℤ)) + 1, b] := by
      push_cast; funext i; fin_cases i <;> simp <;> ring
    rw [e]
    apply (jfc_sq_adj_of_ne_origin (jfc_latadj_E _ _) ?_ ?_).reachable
    · intro h; have := congrFun h 1; simp at this; omega
    · intro h; have := congrFun h 1; simp at this; omega



theorem jfc_sq_col_north (a : ℤ) (ha : a ≠ 0) (b : ℤ) (n : ℕ) :
    (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![a, b] ![a, b + n] := by
  induction n with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have e : (![a, b + (↑(k + 1) : ℤ)] : Site 2) = ![a, (b + (k : ℤ)) + 1] := by
      push_cast; funext i; fin_cases i <;> simp <;> ring
    rw [e]
    apply (jfc_sq_adj_of_ne_origin (jfc_latadj_N _ _) ?_ ?_).reachable
    · intro h; have := congrFun h 0; simp at this; omega
    · intro h; have := congrFun h 0; simp at this; omega



theorem jfc_sq_farEast_exterior (M : ℕ) (a b : ℤ) :
    (![a + ((M + 1 + a.natAbs : ℕ) : ℤ), b] : Site 2) ∈ exterior 2 M := by
  rw [mem_exterior]
  refine ⟨0, ?_⟩
  have h : ((M + 1 + a.natAbs : ℕ) : ℤ) = (M : ℤ) + 1 + (a.natAbs : ℤ) := by push_cast; ring
  simp only [Matrix.cons_val_zero, h]
  omega







theorem jfc_sq_reach_outerRegion {v : Site 2} (hv : v ≠ ![0, 0]) :
    (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk v = jfc_whb_outerRegion jbc_Pce := by
  set R := outerBoxRadius jbc_Pce with hR
  
  have hvform : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  
  by_cases hv1 : v 1 = 0
  · 
    have hv0 : v 0 ≠ 0 := by
      intro h; exact hv (by rw [hvform, h, hv1])
    have hnorth : (whb_faceRegion (imageGraph jbc_Pce)).Reachable ![v 0, v 1] ![v 0, v 1 + 1] := by
      have h := jfc_sq_col_north (v 0) hv0 (v 1) 1
      simpa using h
    have heast := jfc_sq_row_east (v 1 + 1) (by omega) (v 0)
        (R + 1 + 1 + (v 0).natAbs)
    have hext : (![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1 + 1] : Site 2)
        ∈ exterior 2 (R + 1) := jfc_sq_farEast_exterior (R + 1) (v 0) (v 1 + 1)
    have hmk := jfc_whb_exterior_in_outerRegion jbc_Pce hext
    rw [hvform]
    calc (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![v 0, v 1]
        = (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk
            ![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1 + 1] :=
          ConnectedComponent.sound (hnorth.trans heast)
      _ = jfc_whb_outerRegion jbc_Pce := hmk
  · 
    have heast := jfc_sq_row_east (v 1) hv1 (v 0) (R + 1 + 1 + (v 0).natAbs)
    have hext : (![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1] : Site 2)
        ∈ exterior 2 (R + 1) := jfc_sq_farEast_exterior (R + 1) (v 0) (v 1)
    have hmk := jfc_whb_exterior_in_outerRegion jbc_Pce hext
    rw [hvform]
    calc (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![v 0, v 1]
        = (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk
            ![v 0 + ((R + 1 + 1 + (v 0).natAbs : ℕ) : ℤ), v 1] :=
          ConnectedComponent.sound heast
      _ = jfc_whb_outerRegion jbc_Pce := hmk


noncomputable def jfc_sq_interior : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent :=
  (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]


theorem jfc_sq_interior_bounded : jfc_sq_interior.supp.Finite :=
  whb_faceRegion_interior_bounded





theorem jfc_sq_bounded_eq_interior
    (C : {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite}) :
    C = ⟨jfc_sq_interior, jfc_sq_interior_bounded⟩ := by
  classical
  obtain ⟨x, hx⟩ := Quot.exists_rep C.1
  refine Subtype.ext ?_
  by_cases hx0 : x = ![0, 0]
  · rw [← hx, hx0]; rfl
  · exfalso
    have hmk : (whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk x = C.1 := hx
    have houter : C.1 = jfc_whb_outerRegion jbc_Pce := by
      rw [← hmk]; exact jfc_sq_reach_outerRegion hx0
    have hinf : C.1.supp.Infinite := houter ▸ jfc_whb_outerRegion_infinite jbc_Pce
    exact hinf C.2



theorem jfc_sq_faithfulRegionCount : whc_faithfulRegionCount jbc_Pce = 1 := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph jbc_Pce)
      (Set.toFinite (imageGraph jbc_Pce).edgeSet)
  unfold whc_faithfulRegionCount
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => (jfc_sq_bounded_eq_interior a).trans (jfc_sq_bounded_eq_interior b).symm⟩, ?_⟩
  exact ⟨⟨jfc_sq_interior, jfc_sq_interior_bounded⟩⟩


theorem jfc_sq_nullity : nullity jbc_Pce.G = 1 := by
  have h : faceCount jbc_Pce.G = 2 := whb_square_faceCount
  rw [faceCount] at h
  omega








theorem jfc_faithfulDiscreteJordan_unitSquare : whc_FaithfulDiscreteJordan jbc_Pce := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph jbc_Pce)
      (Set.toFinite (imageGraph jbc_Pce).edgeSet)
  have heq : whc_faithfulRegionCount jbc_Pce = nullity jbc_Pce.G := by
    rw [jfc_sq_faithfulRegionCount, jfc_sq_nullity]
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩

















theorem jfc_summary :
    whc_FaithfulDiscreteJordan jbc_Pce ∧
      (jfc_EvenDegreeThreading → jeb_FaithfulCountResidue) :=
  ⟨jfc_faithfulDiscreteJordan_unitSquare, jfc_faithfulCountResidue_of_threading⟩

end Lattice

end StatMech
