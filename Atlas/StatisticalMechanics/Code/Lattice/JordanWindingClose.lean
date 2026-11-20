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
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.WindingColoring
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanEulerInduction
import Code.Lattice.JordanFaithfulCount
import Code.Lattice.JordanCrossingCount

open SimpleGraph Set

namespace StatMech

namespace Lattice













theorem jwc_faceAdj_NE_NW (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c, d] ![c - 1, d] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_NW_SW (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c - 1, d] ![c - 1, d - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_SW_SE (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c - 1, d - 1] ![c, d - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_SE_NE (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c, d - 1] ![c, d] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega



noncomputable def jwc_vertexLoop (c d : ℤ) :
    (hypercubicLattice 2).Walk ![c, d] ![c, d] :=
  .cons (jwc_faceAdj_NE_NW c d)
    (.cons (jwc_faceAdj_NW_SW c d)
      (.cons (jwc_faceAdj_SW_SE c d)
        (.cons (jwc_faceAdj_SE_NE c d) .nil)))


theorem jwc_shared_eval (f0 f1 g0 g1 : ℤ) :
    sharedPrimalEdge ![f0, f1] ![g0, g1] =
      if f0 = g0 then
        s(![f0, max f1 g1], ![f0 + 1, max f1 g1])
      else
        s(![max f0 g0, f1], ![max f0 g0, f1 + 1]) := by
  unfold sharedPrimalEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]



theorem jwc_shared_NE_NW (c d : ℤ) :
    sharedPrimalEdge ![c, d] ![c - 1, d] = s(![c, d], ![c, d + 1]) := by
  rw [jwc_shared_eval, if_neg (by omega)]
  rw [show max c (c - 1) = c by omega, Sym2.eq_iff]; tauto



theorem jwc_shared_NW_SW (c d : ℤ) :
    sharedPrimalEdge ![c - 1, d] ![c - 1, d - 1] = s(![c - 1, d], ![c, d]) := by
  rw [jwc_shared_eval, if_pos rfl]
  rw [show max d (d - 1) = d by omega, Sym2.eq_iff]
  left; refine ⟨rfl, ?_⟩; funext i; fin_cases i <;> simp



theorem jwc_shared_SW_SE (c d : ℤ) :
    sharedPrimalEdge ![c - 1, d - 1] ![c, d - 1] = s(![c, d - 1], ![c, d]) := by
  rw [jwc_shared_eval, if_neg (by omega)]
  rw [show max (c - 1) c = c by omega, Sym2.eq_iff]
  left; refine ⟨rfl, ?_⟩; funext i; fin_cases i <;> simp



theorem jwc_shared_SE_NE (c d : ℤ) :
    sharedPrimalEdge ![c, d - 1] ![c, d] = s(![c, d], ![c + 1, d]) := by
  rw [jwc_shared_eval, if_pos rfl]
  rw [show max (d - 1) d = d by omega, Sym2.eq_iff]; tauto










theorem jwc_vertexLoop_flipCount (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d) =
      (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0)
    + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
  classical
  unfold jwc_vertexLoop
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  
  
  
  have hcollapse : ∀ (a b : Site 2), (hypercubicLattice 2).Adj a b →
      ((jce_edgeFlip E a b ∨ jce_edgeFlip E b a) ↔ sharedPrimalEdge a b ∈ E) := by
    intro a b hab
    unfold jce_edgeFlip
    rw [sharedPrimalEdge_comm_of_adj hab, or_self]
  have e1 := hcollapse _ _ (jwc_faceAdj_NE_NW c d)
  have e2 := hcollapse _ _ (jwc_faceAdj_NW_SW c d)
  have e3 := hcollapse _ _ (jwc_faceAdj_SW_SE c d)
  have e4 := hcollapse _ _ (jwc_faceAdj_SE_NE c d)
  rw [jwc_shared_NE_NW] at e1
  rw [jwc_shared_NW_SW] at e2
  rw [jwc_shared_SW_SE] at e3
  rw [jwc_shared_SE_NE] at e4
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl, if_congr e3 rfl rfl, if_congr e4 rfl rfl]




theorem jwc_jce_degree_eq (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    jce_degree (E : Set (Sym2 (Site 2))) ![c, d] =
      (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0)
    + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
  classical
  unfold jce_degree jce_nbr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_coe]
  rw [Finset.card_filter, Fin.sum_univ_four]
  
  rw [show s((![c, d] : Site 2), ![c - 1, d]) = s((![c - 1, d] : Site 2), ![c, d]) from Sym2.eq_swap,
    show s((![c, d] : Site 2), ![c, d - 1]) = s((![c, d - 1] : Site 2), ![c, d]) from Sym2.eq_swap]
  ring




theorem jwc_vertexLoop_even_iff (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    Even (wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d)) ↔
      Even (jce_degree (E : Set (Sym2 (Site 2))) ![c, d]) := by
  rw [jwc_vertexLoop_flipCount, jwc_jce_degree_eq]












theorem jwc_closedContour_of_edgeFlip_closedEven (E : Finset (Sym2 (Site 2)))
    (hce : wcl_ClosedEven (jce_edgeFlip E)) : jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
  intro v
  have hvform : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hvform]
  rw [← jwc_vertexLoop_even_iff E (v 0) (v 1)]
  exact hce (jwc_vertexLoop (v 0) (v 1))






theorem jwc_edgeFlip_closedEven_iff_closedContour (E : Finset (Sym2 (Site 2))) :
    wcl_ClosedEven (jce_edgeFlip E) ↔ jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
  constructor
  · exact jwc_closedContour_of_edgeFlip_closedEven E
  · exact jce_edgeFlip_closedEven jce_horizStepResidue_holds E




















theorem jwc_cutFlip_closedEven_iff_closedContour (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔
      jce_ClosedContour
        ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
          : Set (Sym2 (Site 2))) := by
  set E := insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset with hE
  have hagree : ∀ a b, (hypercubicLattice 2).Adj a b →
      (wcl_cutFlip H f0 g0 a b ↔ jce_edgeFlip E a b) :=
    fun a b hab => jce_cutFlip_eq_edgeFlip H f0 g0 hfg hab
  constructor
  · intro hce
    apply (jwc_edgeFlip_closedEven_iff_closedContour E).mp
    exact jce_closedEven_congr (jce_edgeFlip E) (wcl_cutFlip H f0 g0)
      (fun a b hab => (hagree a b hab).symm) hce
  · intro hcc
    exact jce_closedEven_congr (wcl_cutFlip H f0 g0) (jce_edgeFlip E) hagree
      ((jwc_edgeFlip_closedEven_iff_closedContour E).mpr hcc)













theorem jwc_separated_of_closedContour (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_deleted_separated_of_closedEven H hfg
    ((jwc_cutFlip_closedEven_iff_closedContour H f0 g0 hfg).mpr hcc)





















theorem jwc_faithfulDiscreteJordan_of_evenPeelable (P : PlanarZ2Subgraph)
    (hpe : jcx_IsEvenPeelable P.G) : whc_FaithfulDiscreteJordan P :=
  jcx_faithfulDiscreteJordan P hpe































theorem jwc_faceRegion_antitone {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) :
    whb_faceRegion G2 ≤ whb_faceRegion G1 := by
  intro f g hfg
  rw [whb_faceRegion_adj] at hfg ⊢
  exact ⟨hfg.1, fun hmem => hfg.2 (SimpleGraph.edgeSet_mono h hmem)⟩



theorem jwc_deleted_antitone {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) (f0 g0 : Site 2) :
    (whb_faceRegion G2).deleteEdges {s(f0, g0)} ≤
      (whb_faceRegion G1).deleteEdges {s(f0, g0)} := by
  intro f g hfg
  rw [deleteEdges_adj] at hfg ⊢
  exact ⟨jwc_faceRegion_antitone h hfg.1, hfg.2⟩






theorem jwc_separated_mono {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) {f0 g0 : Site 2}
    (hsep : ¬ ((whb_faceRegion G1).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    ¬ ((whb_faceRegion G2).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  intro hreach
  exact hsep (hreach.mono (jwc_deleted_antitone h f0 g0))








theorem jwc_syncMerge_of_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  haveI := jfc_pushGraph_locallyFinite P K hKle
  haveI hft : Fintype (jei_pushGraph P K).edgeSet := (jei_pushGraph_edgeSet_finite P K).fintype
  have htoFinset : @Set.toFinset _ (jei_pushGraph P K).edgeSet hft
      = (jei_pushGraph_edgeSet_finite P K).toFinset := by
    apply Finset.ext; intro e
    rw [Set.mem_toFinset, Set.Finite.mem_toFinset]
  rw [← htoFinset] at hcc
  exact jwc_separated_of_closedContour (jei_pushGraph P K) f0 g0 hfg hcc















theorem jwc_pushGraph_mono (P : PlanarZ2Subgraph) {A B : SimpleGraph P.V} (h : A ≤ B) :
    jei_pushGraph P A ≤ jei_pushGraph P B := by
  rintro a b ⟨x, y, hxy, hx, hy⟩
  exact ⟨x, y, h hxy, hx, hy⟩




noncomputable def jwc_cyclePath {V : Type*} [DecidableEq V] {K : SimpleGraph V} {x y : V}
    (hreach : K.Reachable x y) : SimpleGraph V :=
  (hreach.symm).some.toPath.val.toSubgraph.spanningCoe


theorem jwc_cyclePath_le {V : Type*} [DecidableEq V] {K : SimpleGraph V} {x y : V}
    (hreach : K.Reachable x y) : jwc_cyclePath hreach ≤ K := by
  intro a b hab
  rw [jwc_cyclePath, Subgraph.spanningCoe_adj] at hab
  exact (hreach.symm).some.toPath.val.toSubgraph.adj_sub hab




theorem jwc_cyclePath_sup_edge_isEven {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    {x y : V} (hreach : K.Reachable x y) (hne : x ≠ y) (hnadj : ¬ K.Adj x y) :
    jcx_IsEven (jwc_cyclePath hreach ⊔ edge x y) := by
  classical
  set q : K.Walk y x := (hreach.symm).some.toPath.val with hq
  have hqpath : q.IsPath := (hreach.symm).some.toPath.prop
  set G := K ⊔ edge x y with hG
  have hxy_adj : G.Adj x y := by
    rw [hG, sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  set qG : G.Walk y x := q.mapLe le_sup_left with hqG
  have hqGpath : qG.IsPath := (SimpleGraph.Walk.mapLe_isPath le_sup_left).mpr hqpath
  set cyc : G.Walk x x := Walk.cons hxy_adj qG with hcyc
  have hcycIsCycle : cyc.IsCycle := by
    rw [hcyc, Walk.cons_isCycle_iff]
    refine ⟨hqGpath, ?_⟩
    intro hmem
    rw [hqG, SimpleGraph.Walk.edges_mapLe_eq_edges] at hmem
    exact hnadj (q.adj_of_mem_edges hmem)
  have hcyclesCyc : cyc.toSubgraph.spanningCoe.IsCycles :=
    hcycIsCycle.isCycles_spanningCoe_toSubgraph
  have hspanEq : qG.toSubgraph.spanningCoe = jwc_cyclePath hreach := by
    rw [jwc_cyclePath, ← hq]
    ext a b
    rw [Subgraph.spanningCoe_adj, hqG, Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have heq : cyc.toSubgraph.spanningCoe = jwc_cyclePath hreach ⊔ edge x y := by
    rw [hcyc, jvp_consSpanningCoe hxy_adj qG, hspanEq, sup_comm]
  rw [← heq]
  exact jcx_isEven_of_isCycles hcyclesCyc







theorem jwc_syncMerge (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G)
    {x y : P.V} (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) (hreach : K.Reachable x y) :
    ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  have hne : x ≠ y := hadjG.ne
  set Cw := jwc_cyclePath hreach with hCw
  have hCwle : Cw ≤ K := jwc_cyclePath_le hreach
  have hCwG : Cw ≤ P.G := hCwle.trans hKle
  haveI : DecidableRel (Cw ⊔ edge x y).Adj := Classical.decRel _
  have hev : jcx_IsEven (Cw ⊔ edge x y) := jwc_cyclePath_sup_edge_isEven hreach hne hnotK
  have hCwEdge_le : Cw ⊔ edge x y ≤ P.G := by
    refine sup_le hCwG ?_
    intro a b hab; rw [edge_adj] at hab
    rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadjG
    · exact hadjG.symm
  
  have hccPush : jce_ClosedContour (jei_pushGraph P (Cw ⊔ edge x y)).edgeSet :=
    jcx_pushGraph_closedContour P (Cw ⊔ edge x y) hCwEdge_le hev
  
  have hcontourEq : ((insert (sharedPrimalEdge f0 g0)
        (jei_pushGraph_edgeSet_finite P Cw).toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))
      = (jei_pushGraph P (Cw ⊔ edge x y)).edgeSet := by
    rw [Finset.coe_insert, Set.Finite.coe_toFinset, hshared,
      jei_pushGraph_sup_edge P Cw x y hne, SimpleGraph.edgeSet_sup]
    ext e
    refine e.ind (fun a c => ?_)
    have hpq : P.emb x ≠ P.emb y := fun h => hne (P.emb.injective h)
    simp only [Set.mem_insert_iff, Set.mem_union, SimpleGraph.mem_edgeSet, SimpleGraph.edge_adj]
    constructor
    · rintro (h | h)
      · right; rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
        · exact ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hpq⟩
      · exact Or.inl h
    · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
      · exact Or.inr h
      · left; rfl
      · left; rw [Sym2.eq_swap]
  have hccFinset : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P Cw).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    rw [hcontourEq]; exact hccPush
  
  have hsepCw := jwc_syncMerge_of_closedContour P Cw hCwG hfg hccFinset
  
  exact jwc_separated_mono (jwc_pushGraph_mono P hCwle) hsepCw
















def jwc_KeepResidue (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → ∀ {x y : P.V}, P.G.Adj x y → ¬ K.Adj x y →
    ∀ {f0 g0 : Site 2}, (hypercubicLattice 2).Adj f0 g0 →
      sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y) →
      ¬ K.Reachable x y →
        ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0






theorem jwc_whbSync_of_keepResidue (P : PlanarZ2Subgraph) (hkeep : jwc_KeepResidue P) :
    jfc_WhbSync P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared
  constructor
  · intro hreach
    exact jwc_syncMerge P K hKle hadjG hnotK hfg hshared hreach
  · intro hsep
    by_contra hnr
    exact hsep (hkeep K hKle hadjG hnotK hfg hshared hnr)







theorem jwc_faithfulDiscreteJordan_of_keepResidue (P : PlanarZ2Subgraph)
    (hkeep : jwc_KeepResidue P) : whc_FaithfulDiscreteJordan P :=
  jfc_faithfulDiscreteJordan_of_sync P (jwc_whbSync_of_keepResidue P hkeep)













theorem jwc_square_edgeFlip_closedEven :
    wcl_ClosedEven (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset) := by
  classical
  apply (jwc_edgeFlip_closedEven_iff_closedContour _).mpr
  rw [Set.coe_toFinset]
  exact jeb_square_closedContour





theorem jwc_square_vertexLoop_even (c d : ℤ) :
    Even (wcl_flipCount (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset)
      (jwc_vertexLoop c d)) := by
  classical
  rw [jwc_vertexLoop_even_iff]
  have := (jwc_edgeFlip_closedEven_iff_closedContour
    ((imageGraph jbc_Pce).edgeSet.toFinset)).mp jwc_square_edgeFlip_closedEven
  have h := this ![c, d]
  simpa using h














theorem jwc_keep_of_freeHead (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {x y : P.V} (hadjG : P.G.Adj x y) (hfree : ∀ w, ¬ (jei_pushGraph P K).Adj (P.emb x) w)
    {f0 g0 : Site 2} (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
    ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  have hlatpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  obtain ⟨f0', g0', hfg', hshared', hreach'⟩ :=
    jic_dangling_bridge (jei_pushGraph P K) hfree hlatpq.symm
  
  have hedgeEq : s(f0, g0) = s(f0', g0') := by
    apply (jce_sharedPrimalEdge_inj hfg hfg').mpr
    rw [hshared, hshared', Sym2.eq_swap]
  rw [hedgeEq]
  
  have : ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0', g0')}).Reachable f0' g0' := hreach'
  
  rw [Sym2.eq_iff] at hedgeEq
  rcases hedgeEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hreach'
  · exact hreach'.symm


























theorem jwc_summary :
    (∀ (H : SimpleGraph (Site 2)) [Fintype H.edgeSet] (f0 g0 : Site 2),
        (hypercubicLattice 2).Adj f0 g0 →
        (wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔
          jce_ClosedContour
            ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
              : Set (Sym2 (Site 2))))) ∧
      (∀ (P : PlanarZ2Subgraph), jwc_KeepResidue P → whc_FaithfulDiscreteJordan P) ∧
      (∀ (P : PlanarZ2Subgraph), jcx_IsEvenPeelable P.G → whc_FaithfulDiscreteJordan P) :=
  ⟨fun H _ f0 g0 hfg => jwc_cutFlip_closedEven_iff_closedContour H f0 g0 hfg,
    jwc_faithfulDiscreteJordan_of_keepResidue,
    jwc_faithfulDiscreteJordan_of_evenPeelable⟩

end Lattice

end StatMech
