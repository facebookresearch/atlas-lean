/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CoeffMatch










namespace StatMech.Onsager

open Finset SimpleGraph
open StatMech.Ising

universe u

section

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def ons_edgeSubgraph (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 V))

instance ons_edgeSubgraph_decidableAdj (F : Finset (Sym2 V)) :
    DecidableRel (ons_edgeSubgraph F).Adj := by
  dsimp [ons_edgeSubgraph]
  infer_instance

theorem ons_evenSubgraph_disjoint_diag (F : Finset (Sym2 V))
    (hFsub : F ⊆ G.edgeFinset) :
    Disjoint (F : Set (Sym2 V)) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e heF hediag
  have heG : e ∈ G.edgeSet := by
    rw [← SimpleGraph.coe_edgeFinset]
    exact hFsub heF
  exact (G.not_isDiag_of_mem_edgeSet heG) (by simpa [Sym2.mem_diagSet] using hediag)

theorem ons_edgeSubgraph_edgeSet (F : Finset (Sym2 V))
    (hFsub : F ⊆ G.edgeFinset) :
    (ons_edgeSubgraph F).edgeSet = (F : Set (Sym2 V)) := by
  rw [ons_edgeSubgraph, SimpleGraph.edgeSet_fromEdgeSet,
    sdiff_eq_left.mpr (ons_evenSubgraph_disjoint_diag G F hFsub)]

theorem ons_edgeSubgraph_edgeFinset (F : Finset (Sym2 V))
    (hFsub : F ⊆ G.edgeFinset) :
    (ons_edgeSubgraph F).edgeFinset = F := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, ons_edgeSubgraph_edgeSet G F hFsub]
  rfl

theorem ons_incCount_eq_edgeSubgraph_degree (F : Finset (Sym2 V))
    (hFsub : F ⊆ G.edgeFinset) (v : V) :
    incCount F v = (ons_edgeSubgraph F).degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,
    SimpleGraph.incidenceFinset_eq_filter,
    ons_edgeSubgraph_edgeFinset G F hFsub]
  rfl

theorem ons_edgeSubgraph_le (F : Finset (Sym2 V))
    (hFsub : F ⊆ G.edgeFinset) :
    ons_edgeSubgraph F ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet, ons_edgeSubgraph_edgeSet G F hFsub,
    ← SimpleGraph.coe_edgeFinset]
  exact_mod_cast hFsub



theorem ons_isCycles_of_trivalent_even (hdeg : ∀ v, G.degree v ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) :
    (ons_edgeSubgraph F).IsCycles := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFsub : F ⊆ G.edgeFinset := hdata.1
  intro v hv
  have hinc := ons_incCount_eq_edgeSubgraph_degree G F hFsub v
  have hpos : 0 < (ons_edgeSubgraph F).degree v :=
    SimpleGraph.degree_pos_iff_nonempty.mpr hv
  have hle : incCount F v ≤ 3 := by
    rw [hinc]
    exact (SimpleGraph.degree_le_of_le (ons_edgeSubgraph_le G F hFsub)).trans (hdeg v)
  obtain ⟨r, hr⟩ := hdata.2 v
  have htwo : incCount F v = 2 := by omega
  calc
    ((ons_edgeSubgraph F).neighborSet v).ncard =
        (ons_edgeSubgraph F).degree v := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
        exact SimpleGraph.card_neighborSet_eq_degree (ons_edgeSubgraph F) v
    _ = incCount F v := hinc.symm
    _ = 2 := htwo



theorem ons_trivalent_even_component_cycle (hdeg : ∀ v, G.degree v ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G)
    (c : (ons_edgeSubgraph F).ConnectedComponent) {v : V}
    (hv : v ∈ c.supp) (hn : ((ons_edgeSubgraph F).neighborSet v).Nonempty) :
    ∃ p : (ons_edgeSubgraph F).Walk v v,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  exact SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (ons_isCycles_of_trivalent_even G hdeg F hF) hv hn



theorem ons_trivalent_even_exists_cycle (hdeg : ∀ v, G.degree v ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) (hne : F.Nonempty) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edges.toFinset ⊆ F := by
  obtain ⟨e, heF⟩ := hne
  obtain ⟨a, b⟩ := e
  have hFsub : F ⊆ G.edgeFinset := by
    have h := hF
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at h
    exact h.1
  have habH : (ons_edgeSubgraph F).Adj a b := by
    rw [ons_edgeSubgraph, SimpleGraph.fromEdgeSet_adj]
    refine ⟨heF, ?_⟩
    intro hab
    subst b
    have hdiag : s(a, a) ∈ Sym2.diagSet := by simp [Sym2.mem_diagSet]
    exact (Set.disjoint_left.mp (ons_evenSubgraph_disjoint_diag G F hFsub)) heF hdiag
  let c := (ons_edgeSubgraph F).connectedComponentMk a
  obtain ⟨q, hqcycle, _⟩ := ons_trivalent_even_component_cycle G hdeg F hF c
    (by rfl) ⟨b, habH⟩
  let p : G.Walk a a := q.mapLe (ons_edgeSubgraph_le G F hFsub)
  refine ⟨a, p, ?_, ?_⟩
  · simpa [p] using hqcycle.mapLe (ons_edgeSubgraph_le G F hFsub)
  · intro e he
    have heq : e ∈ q.edges.toFinset := by
      rw [show p.edges = q.edges from q.edges_mapLe_eq_edges
        (ons_edgeSubgraph_le G F hFsub)] at he
      exact he
    have heH : e ∈ (ons_edgeSubgraph F).edgeSet :=
      q.edges_subset_edgeSet (List.mem_toFinset.mp heq)
    rw [ons_edgeSubgraph_edgeSet G F hFsub] at heH
    exact heH


theorem ons_cycle_edges_evenSubgraph {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) :
    p.edges.toFinset ∈ evenSubgraphs G := by
  let F := p.edges.toFinset
  have hFsub : F ⊆ G.edgeFinset := by
    intro edge hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp hedge)
  have hgraph : ons_edgeSubgraph F = p.toSubgraph.spanningCoe := by
    ext a b
    rw [ons_edgeSubgraph, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    constructor
    · rintro ⟨hab, _⟩
      exact List.mem_toFinset.mp hab
    · intro hab
      refine ⟨List.mem_toFinset.mpr hab, ?_⟩
      have hadj : G.Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact p.edges_subset_edgeSet hab
      exact hadj.ne
  have hcyc : (ons_edgeSubgraph F).IsCycles := by
    rw [hgraph]
    exact hp.isCycles_spanningCoe_toSubgraph
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨hFsub, ?_⟩
  intro w
  rw [ons_incCount_eq_edgeSubgraph_degree G F hFsub w]
  by_cases hn : ((ons_edgeSubgraph F).neighborSet w).Nonempty
  · have hcard : (ons_edgeSubgraph F).degree w = 2 := by
      calc
        (ons_edgeSubgraph F).degree w =
            ((ons_edgeSubgraph F).neighborSet w).ncard := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
            SimpleGraph.card_neighborSet_eq_degree]
        _ = 2 := hcyc hn
    rw [hcard]
    exact even_two
  · have hzero : (ons_edgeSubgraph F).degree w = 0 := by
      have hnotpos : ¬ 0 < (ons_edgeSubgraph F).degree w := by
        rwa [SimpleGraph.degree_pos_iff_nonempty]
      omega
    rw [hzero]
    exact ⟨0, by simp⟩



theorem ons_trivalent_even_cycle_decomposition (hdeg : ∀ v, G.degree v ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → V) (p : (i : ι) → G.Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      F = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) := by
  classical
  let H := ons_edgeSubgraph F
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFsub : F ⊆ G.edgeFinset := hdata.1
  have hHG : H ≤ G := by simpa [H] using ons_edgeSubgraph_le G F hFsub
  have hcyc : H.IsCycles := by
    simpa [H] using ons_isCycles_of_trivalent_even G hdeg F hF
  let ι := {c : H.ConnectedComponent //
    ∃ v : V, v ∈ c.supp ∧ (H.neighborSet v).Nonempty}
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  choose base hbase using fun c : ι => c.property
  have hex : ∀ c : ι, ∃ q : H.Walk (base c) (base c),
      q.IsCycle ∧ q.toSubgraph.verts = c.1.supp := by
    intro c
    exact hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (hbase c).1 (hbase c).2
  choose q hq using hex
  let p : (c : ι) → G.Walk (base c) (base c) := fun c => (q c).mapLe hHG
  refine ⟨ι, inferInstance, inferInstance, base, p, ?_, ?_, ?_, ?_⟩
  · intro c
    simpa [p] using (hq c).1.mapLe hHG
  · apply Finset.ext
    intro e
    constructor
    · intro heF
      obtain ⟨a, b⟩ := e
      have habH : H.Adj a b := by
        rw [← SimpleGraph.mem_edgeSet, show H.edgeSet = (F : Set (Sym2 V)) by
          simpa [H] using ons_edgeSubgraph_edgeSet G F hFsub]
        exact heF
      let c : ι := ⟨H.connectedComponentMk a,
        ⟨a, by rfl, ⟨b, habH⟩⟩⟩
      have haVert : a ∈ (q c).toSubgraph.verts := by
        rw [(hq c).2]
        rfl
      have habq : (q c).toSubgraph.Adj a b :=
        ((hq c).1.adj_toSubgraph_iff_of_isCycles hcyc haVert b).mpr habH
      rw [Finset.mem_biUnion]
      refine ⟨c, Finset.mem_univ _, ?_⟩
      change s(a, b) ∈ (p c).edges.toFinset
      rw [show (p c).edges = (q c).edges from (q c).edges_mapLe_eq_edges hHG]
      rw [List.mem_toFinset, ← (q c).mem_edges_toSubgraph,
        SimpleGraph.Subgraph.mem_edgeSet]
      exact habq
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨c, _, hec⟩ := he
      have heq : e ∈ (q c).edges.toFinset := by
        simpa only [p, (q c).edges_mapLe_eq_edges hHG] using hec
      have heH : e ∈ H.edgeSet :=
        (q c).edges_subset_edgeSet (List.mem_toFinset.mp heq)
      rw [show H.edgeSet = (F : Set (Sym2 V)) by
        simpa [H] using ons_edgeSubgraph_edgeSet G F hFsub] at heH
      exact heH
  · intro c _ d _ hcd
    change Disjoint (p c).edges.toFinset (p d).edges.toFinset
    rw [Finset.disjoint_left]
    intro e hec hed
    have hecq : e ∈ (q c).edges.toFinset := by
      simpa only [p, (q c).edges_mapLe_eq_edges hHG] using hec
    have hedq : e ∈ (q d).edges.toFinset := by
      simpa only [p, (q d).edges_mapLe_eq_edges hHG] using hed
    obtain ⟨a, b⟩ := e
    have haC : a ∈ c.1.supp := by
      rw [← (hq c).2, SimpleGraph.Walk.mem_verts_toSubgraph]
      exact (q c).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hecq)
    have haD : a ∈ d.1.supp := by
      rw [← (hq d).2, SimpleGraph.Walk.mem_verts_toSubgraph]
      exact (q d).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hedq)
    have hcomp : c.1 = d.1 := by
      have hc := (c.1.mem_supp_iff a).mp haC
      have hd := (d.1.mem_supp_iff a).mp haD
      exact hc.symm.trans hd
    apply hcd
    exact Subtype.ext hcomp
  · intro c _ d _ hcd
    change Disjoint (p c).toSubgraph.verts (p d).toSubgraph.verts
    rw [Set.disjoint_left]
    intro v hvc hvd
    have hvcq : v ∈ (q c).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hvc ⊢
      change v ∈ ((q c).mapLe hHG).support at hvc
      rw [(q c).support_mapLe_eq_support] at hvc
      exact hvc
    have hvdq : v ∈ (q d).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hvd ⊢
      change v ∈ ((q d).mapLe hHG).support at hvd
      rw [(q d).support_mapLe_eq_support] at hvd
      exact hvd
    have hvC : v ∈ c.1.supp := by simpa only [(hq c).2] using hvcq
    have hvD : v ∈ d.1.supp := by simpa only [(hq d).2] using hvdq
    have hcomp : c.1 = d.1 := by
      have hc := (c.1.mem_supp_iff v).mp hvC
      have hd := (d.1.mem_supp_iff v).mp hvD
      exact hc.symm.trans hd
    apply hcd
    exact Subtype.ext hcomp

end

end StatMech.Onsager
