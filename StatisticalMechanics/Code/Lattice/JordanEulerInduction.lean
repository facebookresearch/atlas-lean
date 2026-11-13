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
import Code.Lattice.JordanOuterFaceUnique
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.JordanCycleRank
import Code.Lattice.JordanSeparationFinish

open SimpleGraph Set

namespace StatMech

namespace Lattice










theorem jei_sym2_mem_finite (e : Sym2 (Site 2)) : {x : Site 2 | x ∈ e}.Finite := by
  induction e with
  | _ a b =>
    apply Set.Finite.subset ((Set.finite_singleton a).insert b)
    intro x hx
    rw [Set.mem_setOf_eq, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert _ _




theorem jei_support_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    H.support.Finite := by
  classical
  apply Set.Finite.subset
    (Set.Finite.biUnion hfin (fun e (_ : e ∈ H.edgeSet) => jei_sym2_mem_finite e))
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  rw [Set.mem_iUnion₂]
  exact ⟨s(v, w), by rwa [SimpleGraph.mem_edgeSet], Sym2.mem_mk_left v w⟩






theorem jei_exterior_dual_edge_not_deleted (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2} (hf : f ∉ box 2 R) :
    crossEdge.symm s(f, g) ∉ H.edgeSet := by
  intro hmem
  have hsymm : crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
    simp [crossEdge, sym2Congr]
  rw [hsymm, SimpleGraph.mem_edgeSet] at hmem
  have hsupp : rot90Inv f ∈ H.support := ⟨rot90Inv g, hmem⟩
  have hrf : rot90Inv f ∈ box 2 R := hR _ hsupp
  have hf_eq : f = rot90Fun (rot90Inv f) := by
    have := rot90Equiv.right_inv f
    simpa [rot90Equiv] using this.symm
  exact hf (hf_eq ▸ rot90Fun_mem_box R hrf)




theorem jei_regionGraph_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2}
    (hf : f ∉ box 2 R) (hadj : (hypercubicLattice 2).Adj f g) :
    (regionGraph H).Adj f g :=
  ⟨hadj, jei_exterior_dual_edge_not_deleted H R hR hf⟩








theorem jei_regionComponents_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    Finite (regionGraph H).ConnectedComponent := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box H.support (jei_support_finite H hfin)
  set RG := regionGraph H with hRG
  set S : Set (Site 2) := box 2 R ∪ {beacon 2 R} with hS
  have hSfin : S.Finite := (box_finite 2 R).union (Set.finite_singleton _)
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  have hExtMk : ∀ x : Site 2, x ∈ exterior 2 R →
      RG.connectedComponentMk x = RG.connectedComponentMk (beacon 2 R) := by
    intro x hx
    refine ConnectedComponent.sound ?_
    have hconn := box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext
    have hmap := hconn.map
      (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 R)) →g RG)
    · simpa using hmap
    · intro a b hab
      have haext : (a : Site 2) ∉ box 2 R := mem_box_compl_of_exterior a.2
      exact jei_regionGraph_adj_of_exterior H R (fun v hv => hR hv) haext hab
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 R
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hxbox
    refine ⟨beacon 2 R, Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 R) = c
    rw [← hExtMk x hxext]; exact hx










noncomputable def jei_pushGraph (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := by rintro a b ⟨x, y, hadj, rfl, rfl⟩; exact ⟨y, x, hadj.symm, rfl, rfl⟩
  loopless := ⟨by
    rintro a ⟨x, y, hadj, hx, hy⟩
    have : x = y := P.emb.injective (hx.trans hy.symm)
    exact K.irrefl (this ▸ hadj)⟩

@[simp] theorem jei_pushGraph_adj (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (a b : Site 2) :
    (jei_pushGraph P K).Adj a b ↔ ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b := Iff.rfl



theorem jei_pushGraph_G (P : PlanarZ2Subgraph) : jei_pushGraph P P.G = imageGraph P := by
  ext a b; rw [jei_pushGraph_adj, imageGraph_adj]



theorem jei_pushGraph_bot (P : PlanarZ2Subgraph) : jei_pushGraph P ⊥ = ⊥ := by
  ext a b; rw [jei_pushGraph_adj]
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨x, y, hadj, _, _⟩; exact hadj.elim



theorem jei_pushGraph_edgeSet_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    (jei_pushGraph P K).edgeSet.Finite := by
  have hV : Finite P.V := P.finV
  apply Set.Finite.subset (Set.finite_range (Sym2.map P.emb : Sym2 P.V → Sym2 (Site 2)))
  intro e he
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj] at he
    obtain ⟨x, y, hK, rfl, rfl⟩ := he
    exact ⟨s(x, y), by simp⟩




theorem jei_pushGraph_regionComponents_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Finite (regionGraph (jei_pushGraph P K)).ConnectedComponent :=
  jei_regionComponents_finite _ (jei_pushGraph_edgeSet_finite P K)







theorem jei_pushGraph_sup_edge (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V)
    (hne : x ≠ y) :
    jei_pushGraph P (K ⊔ edge x y) = jei_pushGraph P K ⊔ edge (P.emb x) (P.emb y) := by
  ext a b
  simp only [jei_pushGraph_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨u, v, huv, rfl, rfl⟩
    rcases huv with hK | ⟨hxy, _⟩
    · exact Or.inl ⟨u, v, hK, rfl, rfl⟩
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h)⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h).symm⟩
  · rintro (⟨u, v, hK, rfl, rfl⟩ | ⟨hab, hne'⟩)
    · exact ⟨u, v, Or.inl hK, rfl, rfl⟩
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, y, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩, rfl, rfl⟩
      · exact ⟨y, x, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩, rfl, rfl⟩







theorem jei_push_reachable_iff (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V) :
    (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) ↔ K.Reachable x y := by
  constructor
  · rintro ⟨w⟩
    suffices h : ∀ (a b : Site 2) (w : (jei_pushGraph P K).Walk a b) (za zb : P.V),
        P.emb za = a → P.emb zb = b → K.Reachable za zb by
      exact h _ _ w x y rfl rfl
    intro a b w
    induction w with
    | nil =>
      intro za zb hza hzb
      have : za = zb := P.emb.injective (hza.trans hzb.symm)
      subst this; exact Reachable.refl za
    | @cons c d e hcd wde ih =>
      intro za zb hza hzb
      obtain ⟨u, v, hKuv, hu, hv⟩ := hcd
      have hzau : za = u := P.emb.injective (hza.trans hu.symm)
      subst hzau
      exact (hKuv.reachable).trans (ih v zb hv hzb)
  · intro h
    refine h.map (⟨P.emb, ?_⟩ : K →g jei_pushGraph P K)
    intro a b hab; exact ⟨a, b, hab, rfl, rfl⟩













theorem jei_crossEdge_present (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) :
    crossEdge s(P.emb x, P.emb y) ∈ (regionGraph (jei_pushGraph P K)).edgeSet := by
  rw [crossEdge_mk, SimpleGraph.mem_edgeSet, regionGraph_adj]
  refine ⟨(rot90_adj _ _).mpr (P.isSub hadjG), ?_⟩
  rw [← crossEdge_mk, Equiv.symm_apply_apply, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst_vars
  exact hnotK hKuv























def jei_BridgeCycleDual (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → ∀ {x y : P.V}, P.G.Adj x y → ¬ K.Adj x y →
    (K.Reachable x y ↔
      ¬ ((regionGraph (jei_pushGraph P K)).deleteEdges
          {crossEdge s(P.emb x, P.emb y)}).Reachable (rot90Fun (P.emb x)) (rot90Fun (P.emb y)))

















theorem jei_dualCount_eq_faceCount_of_sync (P : PlanarZ2Subgraph)
    (hsync : jei_BridgeCycleDual P) :
    ∀ (K : SimpleGraph P.V), K ≤ P.G →
      Nat.card (regionGraph (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
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
      rw [jei_pushGraph_bot, jsf_regionGraph_bot]
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
      have ihK' : Nat.card (regionGraph (jei_pushGraph P K')).ConnectedComponent = faceCount K' :=
        ih (n - 1) (by omega) K' hn' hK'le
      haveI hfinK' : Finite (regionGraph (jei_pushGraph P K')).ConnectedComponent :=
        jei_pushGraph_regionComponents_finite P K'
      haveI hfinK : Finite (regionGraph (jei_pushGraph P K)).ConnectedComponent :=
        jei_pushGraph_regionComponents_finite P K
      set p := P.emb x with hp
      set q := P.emb y with hq
      have hpushEq : jei_pushGraph P K = jei_pushGraph P K' ⊔ edge p q := by
        rw [hKeq, jei_pushGraph_sup_edge P K' x y hne_xy]
      have hpq : p ≠ q := fun h => hne_xy (P.emb.injective h)
      have hfg : crossEdge s(p, q) = s(rot90Fun p, rot90Fun q) := crossEdge_mk p q
      have hpres : crossEdge s(p, q) ∈ (regionGraph (jei_pushGraph P K')).edgeSet :=
        jei_crossEdge_present P K' hadjG hnotK'
      haveI hfinSup :
          Finite (regionGraph (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [← hpushEq]; exact hfinK
      have hdich := jsf_dual_delete_dichotomy (jei_pushGraph P K') (p := p) (q := q)
        (f := rot90Fun p) (g := rot90Fun q) hpq hfg hpres
      have hsyncK' := hsync K' hK'le hadjG hnotK'
      set DR := ((regionGraph (jei_pushGraph P K')).deleteEdges
          {crossEdge s(p, q)}).Reachable (rot90Fun p) (rot90Fun q) with hDR
      have hcardPush : Nat.card (regionGraph (jei_pushGraph P K)).ConnectedComponent
          = Nat.card (regionGraph (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [hpushEq]
      by_cases hr : K'.Reachable x y
      · 
        have hnotDR : ¬ DR := hsyncK'.mp hr
        have hdualCard := hdich.2 hnotDR
        have hface : faceCount K = faceCount K' + 1 := by
          rw [hKeq]; exact faceCount_sup_edge_of_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]
      · 
        have hDRtrue : DR := by
          by_contra hcon
          exact hr (hsyncK'.mpr hcon)
        have hdualCard := hdich.1 hDRtrue
        have hface : faceCount K = faceCount K' := by
          rw [hKeq]; exact faceCount_sup_edge_of_not_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]












theorem jei_dualEulerCount_of_sync (P : PlanarZ2Subgraph) (hsync : jei_BridgeCycleDual P) :
    jcr_DualEulerCount P := by
  unfold jcr_DualEulerCount
  rw [← jei_pushGraph_G P]
  exact jei_dualCount_eq_faceCount_of_sync P hsync P.G le_rfl



theorem jei_planarCutCycleDuality_of_sync (P : PlanarZ2Subgraph)
    (hsync : jei_BridgeCycleDual P) : jsf_PlanarCutCycleDuality P :=
  jei_dualEulerCount_of_sync P hsync





theorem jei_discreteJordan_of_sync (P : PlanarZ2Subgraph) (hsync : jei_BridgeCycleDual P) :
    DiscreteJordanSeparation P :=
  jcr_discreteJordan_of_dual P (jei_dualEulerCount_of_sync P hsync)










theorem jei_bridgeCycleDual_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jei_BridgeCycleDual P := by
  intro K _ x y hadjG _
  rw [hG] at hadjG
  exact absurd hadjG (by simp)





theorem jei_dualEulerCount_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jcr_DualEulerCount P :=
  jei_dualEulerCount_of_sync P (jei_bridgeCycleDual_of_bot hG)

end Lattice

end StatMech
