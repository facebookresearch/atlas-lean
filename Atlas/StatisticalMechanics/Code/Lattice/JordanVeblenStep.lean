/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Lattice.EulerFaces2

open SimpleGraph Set

namespace StatMech

namespace Lattice











theorem jvp_consSpanningCoe {V : Type*} {G : SimpleGraph V} {x z y : V} (hadj : G.Adj x z)
    (p : G.Walk z y) :
    (Walk.cons hadj p).toSubgraph.spanningCoe = p.toSubgraph.spanningCoe ⊔ edge x z := by
  ext a b
  simp only [Walk.toSubgraph, Subgraph.spanningCoe_adj, Subgraph.sup_adj, subgraphOfAdj_adj,
    sup_adj, edge_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  have hne : x ≠ z := G.ne_of_adj hadj
  constructor
  · rintro (h | hp)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩
    · exact Or.inl hp
  · rintro (hp | ⟨h, _⟩)
    · exact Or.inr hp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)


theorem jvp_sup_nil_spanningCoe {V : Type*} {G : SimpleGraph V} (x : V) (H : SimpleGraph V) :
    H ⊔ (Walk.nil : G.Walk x x).toSubgraph.spanningCoe = H := by
  simp only [Walk.toSubgraph]
  ext a b
  simp only [sup_adj, Subgraph.spanningCoe_adj, singletonSubgraph_adj, Pi.bot_apply,
    Prop.bot_eq_false, or_false]







theorem jvp_addWalk_faceCount {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V} :
    ∀ {x y : V} (q : G.Walk x y) (H : SimpleGraph V), q.IsPath →
      (∀ u ∈ q.support, ∀ w, ¬ H.Adj u w) →
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
    have hiso_p : ∀ u ∈ p.support, ∀ w, ¬ H.Adj u w := fun u hu w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) w
    obtain ⟨ihface, ihreach⟩ := ih H hpp hiso_p
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw
      rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    have hnr : ¬ Hp.Reachable x z := by
      rintro ⟨wk⟩
      cases wk with
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













theorem jvp_faceCount_deleteCycle {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) [LocallyFinite K] (hcyc : K.IsCycles)
    {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    faceCount (K.deleteEdges p.toSubgraph.edgeSet) + 1 = faceCount K := by
  classical
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  
  have hisoAll : ∀ u ∈ p.support, ∀ w, ¬ K''.Adj u w := by
    intro u hu w hadjw
    rw [hK'', deleteEdges_adj] at hadjw
    obtain ⟨hKadj, hnotin⟩ := hadjw
    have huv : u ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hu
    have := (hp.adj_toSubgraph_iff_of_isCycles hcyc huv w).mpr hKadj
    exact hnotin (by rw [Subgraph.mem_edgeSet]; exact this)
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, ∀ w, ¬ K''.Adj u w := fun u hu w => hisoAll u (hqsub u hu) w
  obtain ⟨hqface, hqreach⟩ := jvp_addWalk_faceCount q K'' hqpath hisoQ
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
  have hvznadj : ¬ Kq.Adj v z := by
    intro hh
    rw [hKq, sup_adj] at hh
    rcases hh with h | h
    · exact hisoAll v (by rw [hpeq, Walk.support_cons]; exact List.mem_cons_self) z h
    · rw [Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hclose : faceCount (Kq ⊔ edge v z) = faceCount Kq + 1 :=
    faceCount_sup_edge_of_reachable Kq hvzne hvznadj hvz
  rw [hKeq2, hclose, hKq, hqface]







theorem jvp_isCycles_deleteCycle_isCycles {V : Type*} [Finite V] [DecidableEq V]
    {K : SimpleGraph V} [LocallyFinite K] (hcyc : K.IsCycles)
    {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    (K.deleteEdges p.toSubgraph.edgeSet).IsCycles := by
  classical
  intro u hu
  obtain ⟨w, hw⟩ := hu
  rw [mem_neighborSet, deleteEdges_adj] at hw
  obtain ⟨hKuw, hnotin⟩ := hw
  have hunotp : u ∉ p.support := by
    intro hin
    have huv : u ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hin
    have := (hp.adj_toSubgraph_iff_of_isCycles hcyc huv w).mpr hKuw
    exact hnotin (by rw [Subgraph.mem_edgeSet]; exact this)
  have heq : (K.deleteEdges p.toSubgraph.edgeSet).neighborSet u = K.neighborSet u := by
    ext x
    simp only [mem_neighborSet, deleteEdges_adj]
    refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
    intro hin2
    rw [p.mem_edges_toSubgraph] at hin2
    exact hunotp (p.fst_mem_support_of_mem_edges hin2)
  rw [heq]
  exact hcyc ⟨w, hKuw⟩



theorem jvp_ncard_deleteCycle_lt {V : Type*} [Finite V] [DecidableEq V]
    {K : SimpleGraph V} {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    (K.deleteEdges p.toSubgraph.edgeSet).edgeSet.ncard < K.edgeSet.ncard := by
  classical
  rw [edgeSet_deleteEdges]
  have hsub : p.toSubgraph.edgeSet ⊆ K.edgeSet := by
    intro e he; rw [p.edgeSet_toSubgraph] at he; exact p.edges_subset_edgeSet he
  obtain ⟨e, he⟩ : p.toSubgraph.edgeSet.Nonempty := by
    rw [p.edgeSet_toSubgraph]
    have h3 := hp.three_le_length
    have hne : p.edges ≠ [] := by
      intro hnil
      have : p.length = 0 := by rw [← Walk.length_edges, hnil]; rfl
      omega
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨e, he⟩
  have hssub : K.edgeSet \ p.toSubgraph.edgeSet ⊂ K.edgeSet := by
    refine ⟨Set.diff_subset, fun hcontra => ?_⟩
    exact (hcontra (hsub he)).2 he
  exact Set.ncard_lt_ncard hssub (Set.toFinite _)














theorem jvp_isCycles_veblenStep {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) [LocallyFinite K] (hcyc : K.IsCycles) (hne : K.edgeSet.Nonempty) :
    ∃ K' : SimpleGraph V, K' ≤ K ∧ K'.IsCycles ∧
      K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K := by
  classical
  
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b⟩ := e
  rw [SimpleGraph.mem_edgeSet] at he
  have hn : (K.neighborSet a).Nonempty := ⟨b, he⟩
  obtain ⟨p, hpc, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (v := a) (c := K.connectedComponentMk a) rfl hn
  refine ⟨K.deleteEdges p.toSubgraph.edgeSet, deleteEdges_le _,
    jvp_isCycles_deleteCycle_isCycles hcyc p hpc,
    jvp_ncard_deleteCycle_lt p hpc, jvp_faceCount_deleteCycle K hcyc p hpc⟩




theorem jvp_isCycles_even {V : Type*} [Finite V] {K : SimpleGraph V} (hcyc : K.IsCycles)
    (v : V) : Even (Nat.card (K.neighborSet v)) := by
  rw [Nat.card_coe_set_eq]
  by_cases hn : (K.neighborSet v).Nonempty
  · rw [hcyc hn]; exact ⟨1, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, Set.ncard_empty]; exact ⟨0, rfl⟩






















theorem jvp_veblen_note {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) [LocallyFinite K] (hcyc : K.IsCycles) (hne : K.edgeSet.Nonempty) :
    (∃ K' : SimpleGraph V, K' ≤ K ∧ K'.IsCycles ∧
        K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K) ∧
      (∀ v : V, Even (Nat.card (K.neighborSet v))) :=
  ⟨jvp_isCycles_veblenStep K hcyc hne, jvp_isCycles_even hcyc⟩

end Lattice

end StatMech
