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
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanFaithfulCount
import Code.Lattice.JordanVeblenStep
import Code.Lattice.JordanIsCyclesCount
import Code.Lattice.JordanGeneralCount

open SimpleGraph Set

namespace StatMech

namespace Lattice









def jcx_IsEven {V : Type*} (K : SimpleGraph V) : Prop :=
  ∀ v : V, Even (Nat.card (K.neighborSet v))


theorem jcx_isEven_of_isCycles {V : Type*} [Finite V] {K : SimpleGraph V} (hcyc : K.IsCycles) :
    jcx_IsEven K :=
  fun v => jvp_isCycles_even hcyc v




theorem jcx_cycle_neighborCard {V : Type*} [Finite V] {K : SimpleGraph V}
    {v : V} (p : K.Walk v v) (hp : p.IsCycle) (u : V) :
    Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 0 ∨
      Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 2 := by
  have hcyc := hp.isCycles_spanningCoe_toSubgraph
  rw [Nat.card_coe_set_eq]
  by_cases hne : (p.toSubgraph.spanningCoe.neighborSet u).Nonempty
  · right; exact hcyc hne
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp



theorem jcx_neighborSet_deleteCycle {V : Type*} [DecidableEq V] (K : SimpleGraph V)
    {v : V} (p : K.Walk v v) (u : V) :
    (K.deleteEdges p.toSubgraph.edgeSet).neighborSet u =
      K.neighborSet u \ p.toSubgraph.spanningCoe.neighborSet u := by
  ext w
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_diff, Subgraph.spanningCoe_adj]
  constructor
  · rintro ⟨hK, hnotin⟩
    exact ⟨hK, fun hadj => hnotin (by rw [Subgraph.mem_edgeSet]; exact hadj)⟩
  · rintro ⟨hK, hnotin⟩
    refine ⟨hK, fun hin => hnotin ?_⟩
    rwa [Subgraph.mem_edgeSet] at hin






theorem jcx_isEven_deleteCycle {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    (hev : jcx_IsEven K) {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    jcx_IsEven (K.deleteEdges p.toSubgraph.edgeSet) := by
  classical
  intro u
  
  have hsub : p.toSubgraph.spanningCoe.neighborSet u ⊆ K.neighborSet u := by
    intro w hw
    rw [mem_neighborSet, Subgraph.spanningCoe_adj] at hw
    rw [mem_neighborSet]; exact p.toSubgraph.adj_sub hw
  have hset := jcx_neighborSet_deleteCycle K p u
  
  have hcardK := hev u
  have hcardCyc := jcx_cycle_neighborCard p hp u
  haveI : Finite (K.neighborSet u) := Set.finite_coe_iff.mpr (Set.toFinite _)
  have hdiff : Nat.card ((K.deleteEdges p.toSubgraph.edgeSet).neighborSet u)
      = Nat.card (K.neighborSet u) - Nat.card (p.toSubgraph.spanningCoe.neighborSet u) := by
    rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_diff hsub (Set.toFinite _)]
  rw [hdiff]
  rcases hcardCyc with h0 | h2
  · rw [h0]; simpa using hcardK
  · rw [h2]
    rcases hcardK with ⟨k, hk⟩
    
    rw [hk]; exact ⟨k - 1, by omega⟩






theorem jcx_pushGraph_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    [DecidableRel K.Adj] (hKle : K ≤ P.G) (hev : jcx_IsEven K) :
    jce_ClosedContour (jei_pushGraph P K).edgeSet := by
  classical
  haveI : Fintype P.V := Fintype.ofFinite _
  haveI hlf : SimpleGraph.LocallyFinite (jei_pushGraph P K) := jfc_pushGraph_locallyFinite P K hKle
  haveI hlfK : SimpleGraph.LocallyFinite K := fun v => Fintype.ofFinite _
  have hsub : jei_pushGraph P K ≤ hypercubicLattice 2 := jfc_pushGraph_le_lattice P K hKle
  intro s
  rw [jeb_jce_degree_eq_degree (jei_pushGraph P K) hsub s]
  by_cases hs : ∃ v : P.V, P.emb v = s
  · obtain ⟨v, rfl⟩ := hs
    have hdeg : (jei_pushGraph P K).degree (P.emb v) = K.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      symm
      apply Finset.card_bij (fun w _ => P.emb w)
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj]
        exact ⟨v, w, hw, rfl, rfl⟩
      · intro a _ b _ h; exact P.emb.injective h
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
        obtain ⟨x, y, hxy, hx, hy⟩ := hw
        have hxv : x = v := P.emb.injective hx
        subst hxv
        exact ⟨y, by rw [SimpleGraph.mem_neighborFinset]; exact hxy, hy⟩
    rw [hdeg]
    have h := hev v
    rwa [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h
  · have hzero : (jei_pushGraph P K).degree s = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
        Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
      obtain ⟨x, y, _, hx, _⟩ := hw
      exact hs ⟨x, hx⟩
    rw [hzero]; exact ⟨0, rfl⟩
















theorem jcx_addWalk_tc (P : PlanarZ2Subgraph) :
    ∀ {x y : P.V} (q : P.G.Walk x y) (H : SimpleGraph P.V), q.IsPath →
      (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) →
      jic_tc P (H ⊔ q.toSubgraph.spanningCoe) = jic_tc P H := by
  intro x y q
  induction q with
  | nil =>
    intro H _ _; congr 1; exact jvp_sup_nil_spanningCoe x H
  | @cons x z y hadj p ih =>
    intro H hpath hiso
    obtain ⟨hpp, hxns⟩ := (Walk.cons_isPath_iff hadj p).mp hpath
    have hiso_p : ∀ u ∈ p.support, u ≠ y → ∀ w, ¬ H.Adj u w := fun u hu hne w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) hne w
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have ihHp : jic_tc P Hp = jic_tc P H := ih H hpp hiso_p
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxney : x ≠ y := by intro h; subst h; exact hxns (Walk.end_mem_support p)
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw; rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp hxney w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    have hlat : (hypercubicLattice 2).Adj (P.emb x) (P.emb z) := P.isSub hadj
    have hkeep := jic_tc_sup_edge_keep P Hp hxz hlat hxiso
    rw [hunion, hkeep, ihHp]



theorem jcx_walk_spanningCoe_reachable {V : Type*} {G : SimpleGraph V} {x y : V} (q : G.Walk x y) :
    q.toSubgraph.spanningCoe.Reachable x y := by
  induction q with
  | nil => exact Reachable.refl _
  | @cons a b c hadj p ih =>
    have hstep : (Walk.cons hadj p).toSubgraph.spanningCoe.Adj a b := by
      rw [Subgraph.spanningCoe_adj, Walk.toSubgraph]; left; rw [subgraphOfAdj_adj]
    have hmono : p.toSubgraph.spanningCoe ≤ (Walk.cons hadj p).toSubgraph.spanningCoe := by
      intro s t hst; rw [Subgraph.spanningCoe_adj] at hst ⊢
      rw [Walk.toSubgraph]; right; exact hst
    exact hstep.reachable.trans (ih.mono hmono)

























theorem jcx_tc_deleteCycle (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) [DecidableRel K.Adj]
    (hKle : K ≤ P.G) (hev : jcx_IsEven K) {v : P.V} (p : K.Walk v v) (hp : p.IsCycle)
    (hiso : ∀ u ∈ p.support, u ≠ v →
      ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
    jic_tc P K = jic_tc P (K.deleteEdges p.toSubgraph.edgeSet) + 1 := by
  classical
  haveI : Finite P.V := P.finV
  haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : P.V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, u ≠ v → ∀ w, ¬ K''.Adj u w :=
    fun u hu hne w => hiso u (hqsub u hu) hne w
  set qG : P.G.Walk z v := q.mapLe hKle with hqG
  have hqGpath : qG.IsPath := (SimpleGraph.Walk.mapLe_isPath hKle).mpr hqpath
  have hsupp : qG.support = q.support := by
    rw [hqG]; exact SimpleGraph.Walk.support_mapLe_eq_support hKle q
  have hspan : qG.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
    ext w x
    rw [hqG, Subgraph.spanningCoe_adj, Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have hisoQG : ∀ u ∈ qG.support, u ≠ v → ∀ w, ¬ K''.Adj u w := by
    intro u hu hne w; rw [hsupp] at hu; exact hisoQ u hu hne w
  have haddK'' : K'' ≤ P.G := (deleteEdges_le _).trans hKle
  have haddwalk := jcx_addWalk_tc P qG K'' hqGpath hisoQG
  set Kq := K'' ⊔ qG.toSubgraph.spanningCoe with hKqdef
  have hpspan : p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe ⊔ edge v z := by
    rw [hpeq]; exact jvp_consSpanningCoe hadj q
  have hKeq : K = K'' ⊔ p.toSubgraph.spanningCoe := by
    ext a c
    simp only [hK'', sup_adj, deleteEdges_adj, Subgraph.spanningCoe_adj]
    constructor
    · intro hKac
      by_cases hin : s(a, c) ∈ p.toSubgraph.edgeSet
      · right; rw [Subgraph.mem_edgeSet] at hin; exact hin
      · left; exact ⟨hKac, hin⟩
    · rintro (⟨hh, _⟩ | hh)
      · exact hh
      · exact p.toSubgraph.adj_sub hh
  have hKeq2 : K = Kq ⊔ edge v z := by rw [hKeq, hpspan, hKqdef, hspan]; ac_rfl
  
  have hqreach : Kq.Reachable z v := by
    have hle : qG.toSubgraph.spanningCoe ≤ Kq := le_sup_right
    exact (jcx_walk_spanningCoe_reachable qG).mono hle
  have hqspanle : q.toSubgraph.spanningCoe ≤ K := by
    intro a c h; exact q.toSubgraph.adj_sub (by rwa [Subgraph.spanningCoe_adj] at h)
  have hKqle : Kq ≤ P.G := by
    rw [hKqdef]
    exact sup_le haddK'' (by rw [hspan]; exact hqspanle.trans hKle)
  
  have hvz_in_p : s(v, z) ∈ p.toSubgraph.edgeSet := by
    rw [hpeq]
    have : s(v, z) ∈ (Walk.cons hadj q).edges := by
      rw [Walk.edges_cons]; exact List.mem_cons_self
    rw [(Walk.cons hadj q).mem_edges_toSubgraph]; exact this
  have hnotKq : ¬ Kq.Adj v z := by
    rw [hKqdef, sup_adj]
    rintro (h | h)
    · rw [hK'', deleteEdges_adj] at h
      exact h.2 hvz_in_p
    · rw [hspan, Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hadjG : P.G.Adj v z := hKle hadj
  have hccK : jce_ClosedContour (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet := by
    rw [← hKeq2]; exact jcx_pushGraph_closedContour P K hKle hev
  haveI : DecidableRel Kq.Adj := Classical.decRel _
  have hclose := jic_tc_close_edge P Kq hKqle hadjG hnotKq hqreach.symm hccK
  rw [hKeq2, hclose, hKqdef, haddwalk]











theorem jcx_addWalk_faceCount {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V} :
    ∀ {x y : V} (q : G.Walk x y) (H : SimpleGraph V), q.IsPath →
      (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) →
      faceCount (H ⊔ q.toSubgraph.spanningCoe) = faceCount H ∧
        (∀ u ∈ q.support, (H ⊔ q.toSubgraph.spanningCoe).Reachable x u) := by
  intro x y q
  induction q with
  | nil =>
    intro H _ _
    refine ⟨by rw [jvp_sup_nil_spanningCoe], ?_⟩
    intro u hu
    rw [Walk.support_nil, List.mem_singleton] at hu; subst hu
    exact (jvp_sup_nil_spanningCoe _ H).symm ▸ Reachable.refl u
  | @cons x z y hadj p ih =>
    intro H hpath hiso
    obtain ⟨hpp, hxns⟩ := (Walk.cons_isPath_iff hadj p).mp hpath
    have hiso_p : ∀ u ∈ p.support, u ≠ y → ∀ w, ¬ H.Adj u w := fun u hu hne w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) hne w
    obtain ⟨ihface, ihreach⟩ := ih H hpp hiso_p
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxney : x ≠ y := by intro h; subst h; exact hxns (Walk.end_mem_support p)
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw; rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp hxney w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    have hnr : ¬ Hp.Reachable x z := by
      rintro ⟨wk⟩; cases wk with
      | nil => exact hxz rfl
      | cons hh _ => exact hxiso _ hh
    have hadjHp : ¬ Hp.Adj x z := fun h => hxiso z h
    have hface : faceCount (Hp ⊔ edge x z) = faceCount Hp :=
      faceCount_sup_edge_of_not_reachable Hp hxz hadjHp hnr
    refine ⟨?_, ?_⟩
    · rw [hunion, hface, hHp]; exact ihface
    · intro u hu
      rw [Walk.support_cons, List.mem_cons] at hu
      rw [hunion]
      have hle : Hp ≤ Hp ⊔ edge x z := le_sup_left
      have hxz_reach : (Hp ⊔ edge x z).Reachable x z :=
        Adj.reachable (by rw [sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      rcases hu with rfl | hup
      · exact Reachable.refl _
      · exact hxz_reach.trans ((ihreach u hup).mono hle)










theorem jcx_faceCount_deleteCycle {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) [LocallyFinite K] {v : V} (p : K.Walk v v) (hp : p.IsCycle)
    (hiso : ∀ u ∈ p.support, u ≠ v →
      ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
    faceCount (K.deleteEdges p.toSubgraph.edgeSet) + 1 = faceCount K := by
  classical
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, u ≠ v → ∀ w, ¬ K''.Adj u w :=
    fun u hu hne w => hiso u (hqsub u hu) hne w
  obtain ⟨hqface, hqreach⟩ := jcx_addWalk_faceCount q K'' hqpath hisoQ
  have hpspan : p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe ⊔ edge v z := by
    rw [hpeq]; exact jvp_consSpanningCoe hadj q
  have hKeq : K = K'' ⊔ p.toSubgraph.spanningCoe := by
    ext a b
    simp only [hK'', sup_adj, deleteEdges_adj, Subgraph.spanningCoe_adj]
    constructor
    · intro hKab
      by_cases hin : s(a, b) ∈ p.toSubgraph.edgeSet
      · right; rw [Subgraph.mem_edgeSet] at hin; exact hin
      · left; exact ⟨hKab, hin⟩
    · rintro (⟨hh, _⟩ | hh)
      · exact hh
      · exact p.toSubgraph.adj_sub hh
  set Kq := K'' ⊔ q.toSubgraph.spanningCoe with hKq
  have hKeq2 : K = Kq ⊔ edge v z := by rw [hKeq, hpspan, hKq]; ac_rfl
  have hzv : Kq.Reachable z v := by rw [hKq]; exact hqreach v (Walk.end_mem_support q)
  have hvz : Kq.Reachable v z := hzv.symm
  have hvzne : v ≠ z := K.ne_of_adj hadj
  have hvz_in_p : s(v, z) ∈ p.toSubgraph.edgeSet := by
    rw [hpeq]
    have : s(v, z) ∈ (Walk.cons hadj q).edges := by
      rw [Walk.edges_cons]; exact List.mem_cons_self
    rw [(Walk.cons hadj q).mem_edges_toSubgraph]; exact this
  have hvznadj : ¬ Kq.Adj v z := by
    rw [hKq, sup_adj]
    rintro (h | h)
    · rw [hK'', deleteEdges_adj] at h; exact h.2 hvz_in_p
    · rw [Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hclose : faceCount (Kq ⊔ edge v z) = faceCount Kq + 1 :=
    faceCount_sup_edge_of_reachable Kq hvzne hvznadj hvz
  rw [hKeq2, hclose, hKq, hqface]























inductive jcx_IsEvenPeelable {V : Type*} : SimpleGraph V → Prop where
  | bot : jcx_IsEvenPeelable (⊥ : SimpleGraph V)
  | cycle {K : SimpleGraph V} (hev : jcx_IsEven K) {v : V} (p : K.Walk v v) (hp : p.IsCycle)
      (hiso : ∀ u ∈ p.support, u ≠ v → ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w)
      (hrec : jcx_IsEvenPeelable (K.deleteEdges p.toSubgraph.edgeSet)) : jcx_IsEvenPeelable K





theorem jcx_tc_eq_faceCount (P : PlanarZ2Subgraph) :
    ∀ {K : SimpleGraph P.V}, jcx_IsEvenPeelable K → K ≤ P.G → jic_tc P K = faceCount K := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  intro K hpe
  induction hpe with
  | bot =>
    intro _
    unfold jic_tc
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
  | @cycle K hev v p hp hiso hrec ih =>
    intro hKle
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    haveI hdec : DecidableRel K.Adj := Classical.decRel _
    have hK'le : K.deleteEdges p.toSubgraph.edgeSet ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    have hreg := jcx_tc_deleteCycle P K hKle hev p hp hiso
    have hface := jcx_faceCount_deleteCycle K p hp hiso
    rw [hreg, ihK']; omega



theorem jcx_total_count (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jcx_tc_eq_faceCount P hpe le_rfl
  unfold jic_tc at h
  rwa [jei_pushGraph_G P] at h


theorem jcx_faithfulRegionCount_eq_nullity (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jcx_total_count P hpe
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega











theorem jcx_faithfulDiscreteJordan (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jcx_faithfulRegionCount_eq_nullity P hpe
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩











theorem jcx_cycleVerts_isolated {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    [LocallyFinite K] (hcyc : K.IsCycles) {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    ∀ u ∈ p.support, ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w := by
  intro u hu w hadjw
  rw [deleteEdges_adj] at hadjw
  obtain ⟨hKadj, hnotin⟩ := hadjw
  have huv : u ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hu
  have := (hp.adj_toSubgraph_iff_of_isCycles hcyc huv w).mpr hKadj
  exact hnotin (by rw [Subgraph.mem_edgeSet]; exact this)






theorem jcx_isEvenPeelable_of_isCycles {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hcyc : K.IsCycles) : jcx_IsEvenPeelable K := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; exact jcx_IsEvenPeelable.bot
    · have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      have hnbr : (K.neighborSet a).Nonempty := ⟨b, he⟩
      obtain ⟨p, hpc, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (v := a) (c := K.connectedComponentMk a) rfl hnbr
      have hK'cyc : (K.deleteEdges p.toSubgraph.edgeSet).IsCycles :=
        jvp_isCycles_deleteCycle_isCycles hcyc p hpc
      have hlt : (K.deleteEdges p.toSubgraph.edgeSet).edgeSet.ncard < K.edgeSet.ncard :=
        jvp_ncard_deleteCycle_lt p hpc
      have hiso : ∀ u ∈ p.support, u ≠ a →
          ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w :=
        fun u hu _ w => jcx_cycleVerts_isolated hcyc p hpc u hu w
      exact jcx_IsEvenPeelable.cycle (jcx_isEven_of_isCycles hcyc) p hpc hiso
        (ih _ (by omega) _ hK'cyc rfl)

















def jcx_cross_emb (i : Fin 7) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![1, 1] | 3 => ![0, 1]
  | 4 => ![2, 1] | 5 => ![2, 2] | 6 => ![1, 2]

theorem jcx_cross_emb_inj : Function.Injective jcx_cross_emb := by decide +kernel


def jcx_cross_rel (i j : Fin 7) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) ||
  (i == 2 && j == 4) || (i == 4 && j == 2) || (i == 4 && j == 5) || (i == 5 && j == 4) ||
  (i == 5 && j == 6) || (i == 6 && j == 5) || (i == 6 && j == 2) || (i == 2 && j == 6)


def jcx_cross_G : SimpleGraph (Fin 7) where
  Adj i j := jcx_cross_rel i j
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jcx_cross_G_adj (i j : Fin 7) : jcx_cross_G.Adj i j ↔ jcx_cross_rel i j := Iff.rfl

theorem jcx_cross_isSub : ∀ ⦃i j : Fin 7⦄, jcx_cross_G.Adj i j →
    (hypercubicLattice 2).Adj (jcx_cross_emb i) (jcx_cross_emb j) := by
  intro i j h; rw [jcx_cross_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jcx_cross_rel, jcx_cross_emb]


noncomputable def jcx_cross_P : PlanarZ2Subgraph where
  V := Fin 7
  finV := inferInstance
  decV := inferInstance
  G := jcx_cross_G
  emb := ⟨jcx_cross_emb, jcx_cross_emb_inj⟩
  isSub := jcx_cross_isSub


theorem jcx_cross_deg2 : jcx_cross_G.neighborSet 2 = {1, 3, 4, 6} := by
  ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]





theorem jcx_cross_not_isCycles : ¬ jcx_cross_G.IsCycles := by
  intro hcyc
  have hv : (jcx_cross_G.neighborSet 2).Nonempty :=
    ⟨1, by rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; decide⟩
  have h2 := hcyc hv
  rw [jcx_cross_deg2, show ({1, 3, 4, 6} : Set (Fin 7)).ncard = 4 by
    rw [Set.ncard_eq_toFinset_card']; decide] at h2
  exact absurd h2 (by decide)



theorem jcx_cross_isEven : jcx_IsEven jcx_cross_G := by
  intro v
  rw [Nat.card_coe_set_eq]
  have key : (jcx_cross_G.neighborSet v).ncard = 2 ∨ (jcx_cross_G.neighborSet v).ncard = 4 := by
    fin_cases v
    · left; rw [show jcx_cross_G.neighborSet ⟨0, by omega⟩ = {1, 3} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨1, by omega⟩ = {0, 2} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · right; rw [show jcx_cross_G.neighborSet ⟨2, by omega⟩ = {1, 3, 4, 6} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      rw [Set.ncard_eq_toFinset_card']; decide
    · left; rw [show jcx_cross_G.neighborSet ⟨3, by omega⟩ = {2, 0} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨4, by omega⟩ = {2, 5} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨5, by omega⟩ = {4, 6} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨6, by omega⟩ = {5, 2} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
  rcases key with h | h <;> rw [h] <;> decide


def jcx_cross_cycB : jcx_cross_G.Walk 2 2 :=
  Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 2 4)
    (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 4 5)
      (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 5 6)
        (Walk.cons (by rw [jcx_cross_G_adj]; decide : jcx_cross_G.Adj 6 2) Walk.nil)))

theorem jcx_cross_cycB_isCycle : jcx_cross_cycB.IsCycle := by
  rw [jcx_cross_cycB, Walk.cons_isCycle_iff]
  exact ⟨by rw [Walk.isPath_def]; decide, by decide⟩


def jcx_cross_A_rel (i j : Fin 7) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3)


def jcx_cross_A : SimpleGraph (Fin 7) where
  Adj i j := jcx_cross_A_rel i j
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jcx_cross_A_adj (i j : Fin 7) : jcx_cross_A.Adj i j ↔ jcx_cross_A_rel i j := Iff.rfl


theorem jcx_cross_delete_eq_A :
    jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet = jcx_cross_A := by
  ext i j
  rw [deleteEdges_adj, jcx_cross_cycB.edgeSet_toSubgraph, jcx_cross_A_adj, jcx_cross_G_adj]
  have hedges : ∀ e, e ∈ jcx_cross_cycB.edgeSet ↔
      e ∈ [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)] := by
    intro e; rw [Walk.mem_edgeSet]
    have : jcx_cross_cycB.edges = [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)] := by decide
    rw [this]
  rw [show (s(i, j) ∈ jcx_cross_cycB.edgeSet)
      = (s(i, j) ∈ [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)]) from propext (hedges _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Sym2.eq_iff]
  revert i j; decide




theorem jcx_cross_cycB_iso : ∀ u ∈ jcx_cross_cycB.support, u ≠ 2 →
    ∀ w, ¬ (jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet).Adj u w := by
  intro u hu hne w hadj
  rw [jcx_cross_delete_eq_A, jcx_cross_A_adj] at hadj
  have hsupp : jcx_cross_cycB.support = [2, 4, 5, 6, 2] := by decide
  rw [hsupp] at hu
  fin_cases hu <;> first
    | (exact hne rfl)
    | (revert hadj; fin_cases w <;> simp [jcx_cross_A_rel])



theorem jcx_cross_A_isCycles : jcx_cross_A.IsCycles := by
  intro v hv
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]




theorem jcx_cross_isEvenPeelable : jcx_IsEvenPeelable jcx_cross_G := by
  refine jcx_IsEvenPeelable.cycle jcx_cross_isEven jcx_cross_cycB jcx_cross_cycB_isCycle
    jcx_cross_cycB_iso ?_
  rw [jcx_cross_delete_eq_A]
  exact jcx_isEvenPeelable_of_isCycles jcx_cross_A jcx_cross_A_isCycles










theorem jcx_faithfulDiscreteJordan_twoSquaresCorner :
    whc_FaithfulDiscreteJordan jcx_cross_P :=
  jcx_faithfulDiscreteJordan jcx_cross_P jcx_cross_isEvenPeelable





































end Lattice

end StatMech
