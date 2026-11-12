/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.ContourCountInjection

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable








namespace EulerianExistence

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem degree_eq_card_filter_edges (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.degree x = (G.edgeFinset.filter (fun e => x ∈ e)).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]


theorem edgeFinset_deleteEdges_finset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) :
    (G.deleteEdges (S : Set (Sym2 V))).edgeFinset = G.edgeFinset \ S := by
  classical
  have hdec : DecidableRel (G.deleteEdges (S : Set (Sym2 V))).Adj := Classical.decRel _
  apply Finset.coe_injective
  rw [Finset.coe_sdiff, coe_edgeFinset, coe_edgeFinset, SimpleGraph.edgeSet_deleteEdges]





theorem even_degree_deleteEdges_closedTrail (G : SimpleGraph V) [DecidableRel G.Adj]
    {u : V} {p : G.Walk u u} (hp : p.IsTrail) (x : V) (hx : Even (G.degree x)) :
    Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  classical
  have hdec : DecidableRel (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj :=
    Classical.decRel _
  rw [degree_eq_card_filter_edges, edgeFinset_deleteEdges_finset]
  have hfsd : (G.edgeFinset \ p.edges.toFinset).filter (fun e => x ∈ e)
      = G.edgeFinset.filter (fun e => x ∈ e) \ (p.edges.toFinset).filter (fun e => x ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfsd]
  set A := G.edgeFinset.filter (fun e => x ∈ e) with hA
  set B := (p.edges.toFinset).filter (fun e => x ∈ e) with hB
  have hAeven : Even A.card := by rw [hA, ← degree_eq_card_filter_edges]; exact hx
  
  have hBA : B ⊆ A := by
    intro e he
    rw [hB, Finset.mem_filter] at he
    rw [hA, Finset.mem_filter]
    exact ⟨(SimpleGraph.mem_edgeFinset).mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he.1)),
      he.2⟩
  
  have hBeven : Even B.card := by
    have hnd : p.edges.Nodup := hp.edges_nodup
    have hcard : B.card = (p.edges.filter (fun e => decide (x ∈ e))).length := by
      rw [hB]
      have : ({e ∈ p.edges.toFinset | x ∈ e} : Finset (Sym2 V))
          = (p.edges.filter (fun e => decide (x ∈ e))).toFinset := by
        rw [List.toFinset_filter]; apply Finset.filter_congr; intro e _
        simp [decide_eq_true_eq]
      rw [this, List.toFinset_card_of_nodup (hnd.filter _)]
    rw [hcard, ← List.countP_eq_length_filter]
    exact (hp.even_countP_edges_iff x).mpr (fun h => absurd rfl h)
  
  rw [Finset.card_sdiff_of_subset hBA]
  exact (Nat.even_sub (Finset.card_le_card hBA)).mpr (iff_of_true hAeven hBeven)






omit [DecidableEq V] in



theorem exists_maximal_closed_trail (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    ∃ p : G.Walk u u, p.IsTrail ∧
      ∀ q : G.Walk u u, q.IsTrail → q.length ≤ p.length := by
  classical
  
  set P : ℕ → Prop := fun k => ∃ q : G.Walk u u, q.IsTrail ∧ q.length = k with hP
  have hP0 : P 0 := ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsTrail.nil, rfl⟩
  
  have hbound : ∀ k, P k → k ≤ G.edgeFinset.card := by
    rintro k ⟨q, hq, rfl⟩; exact hq.length_le_card_edgeFinset
  
  set N := Nat.findGreatest P G.edgeFinset.card with hN
  have hNP : P N := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨p, hp, hplen⟩ := hNP
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hqlen : q.length ≤ G.edgeFinset.card := hq.length_le_card_edgeFinset
  have hqP : P q.length := ⟨q, hq, rfl⟩
  rw [hplen]
  exact Nat.le_findGreatest hqlen hqP






noncomputable def spliceWalk (G : SimpleGraph V) {u w : V} (p : G.Walk u u)
    (hw : w ∈ p.support) (c : G.Walk w w) : G.Walk u u :=
  (p.takeUntil w hw).append (c.append (p.dropUntil w hw))

omit [Fintype V] in

theorem spliceWalk_length (G : SimpleGraph V) {u w : V} (p : G.Walk u u)
    (hw : w ∈ p.support) (c : G.Walk w w) :
    (spliceWalk G p hw c).length = p.length + c.length := by
  unfold spliceWalk
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append]
  have hspec := congrArg SimpleGraph.Walk.length (p.take_spec hw)
  rw [SimpleGraph.Walk.length_append] at hspec
  omega

omit [Fintype V] in

theorem spliceWalk_edges (G : SimpleGraph V) {u w : V} (p : G.Walk u u)
    (hw : w ∈ p.support) (c : G.Walk w w) :
    (spliceWalk G p hw c).edges
      = (p.takeUntil w hw).edges ++ (c.edges ++ (p.dropUntil w hw).edges) := by
  unfold spliceWalk
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]

omit [Fintype V] in



theorem spliceWalk_isTrail (G : SimpleGraph V) {u w : V} {p : G.Walk u u}
    (hp : p.IsTrail) (hw : w ∈ p.support) {c : G.Walk w w} (hc : c.IsTrail)
    (hdisj : ∀ e ∈ c.edges, e ∉ p.edges) :
    (spliceWalk G p hw c).IsTrail := by
  classical
  rw [SimpleGraph.Walk.isTrail_def, spliceWalk_edges]
  
  have hpsplit : p.edges = (p.takeUntil w hw).edges ++ (p.dropUntil w hw).edges := by
    conv_lhs => rw [← p.take_spec hw]
    rw [SimpleGraph.Walk.edges_append]
  have hpnd : p.edges.Nodup := hp.edges_nodup
  rw [hpsplit, List.nodup_append] at hpnd
  obtain ⟨hntd, hndd, hdisjpd⟩ := hpnd
  have hcnd : c.edges.Nodup := hc.edges_nodup
  
  have htsub : ∀ e ∈ (p.takeUntil w hw).edges, e ∈ p.edges := fun e he => by
    rw [hpsplit]; exact List.mem_append_left _ he
  have hdsub : ∀ e ∈ (p.dropUntil w hw).edges, e ∈ p.edges := fun e he => by
    rw [hpsplit]; exact List.mem_append_right _ he
  rw [List.nodup_append]
  refine ⟨hntd, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hcnd, hndd, ?_⟩
    
    intro a hac b hbd hab
    subst hab
    exact hdisj a hac (hdsub a hbd)
  · 
    intro a hat b hbcd hab
    subst hab
    rw [List.mem_append] at hbcd
    rcases hbcd with hac | had
    · exact hdisj a hac (htsub a hat)
    · exact hdisjpd a hat a had rfl



omit [Fintype V] [DecidableEq V] in


theorem exists_boundary_edge_of_walk (G : SimpleGraph V) {A : Set V} :
    ∀ {a b : V} (q : G.Walk a b), a ∈ A → b ∉ A →
      ∃ c d : V, G.Adj c d ∧ c ∈ A ∧ d ∉ A ∧ s(c, d) ∈ q.edges := by
  intro a b q
  induction q with
  | nil => intro ha hb; exact absurd ha hb
  | @cons a m b hadj q ih =>
    intro ha hb
    by_cases hm : m ∈ A
    · 
      obtain ⟨c, d, hcd, hcA, hdA, hmem⟩ := ih hm hb
      exact ⟨c, d, hcd, hcA, hdA, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hmem⟩
    · 
      exact ⟨a, m, hadj, ha, hm, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self⟩















theorem exists_closed_eulerian (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (heven : ∀ x, Even (G.degree x)) (u : V) :
    ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeFinset, e ∈ p.edges := by
  classical
  obtain ⟨p, hp, hmax⟩ := exists_maximal_closed_trail G u
  refine ⟨p, hp, ?_⟩
  
  by_contra hcover
  push Not at hcover
  obtain ⟨e₀, he₀G, he₀p⟩ := hcover
  
  set Gpp := G.deleteEdges (p.edges.toFinset : Set (Sym2 (V))) with hGpp
  have hGpp_le : Gpp ≤ G := SimpleGraph.deleteEdges_le _
  haveI : DecidableRel Gpp.Adj := Classical.decRel _
  
  have he₀Gpp : e₀ ∈ Gpp.edgeSet := by
    rw [hGpp, SimpleGraph.edgeSet_deleteEdges]
    refine ⟨(SimpleGraph.mem_edgeFinset).mp he₀G, ?_⟩
    rw [Finset.mem_coe, List.mem_toFinset]
    exact he₀p
  
  have hGpp_even : ∀ x, Even (Gpp.degree x) := by
    intro x
    have h := even_degree_deleteEdges_closedTrail G hp x (heven x)
    
    rw [← SimpleGraph.card_neighborSet_eq_degree] at h ⊢
    convert h using 2
  
  obtain ⟨w, z, hwz, hwsup⟩ :
      ∃ w z : V, Gpp.Adj w z ∧ w ∈ p.support := by
    
    induction e₀ with
    | h a₀ b₀ =>
      rw [SimpleGraph.mem_edgeSet] at he₀Gpp
      by_cases ha₀ : a₀ ∈ p.support
      · exact ⟨a₀, b₀, he₀Gpp, ha₀⟩
      · 
        have hreach : G.Reachable u a₀ := hconn.preconnected u a₀
        obtain ⟨q⟩ := hreach
        obtain ⟨c, d, hcd, hcsup, hdsup, hmem⟩ :=
          exists_boundary_edge_of_walk G (A := {v | v ∈ p.support}) q
            (p.start_mem_support) ha₀
        
        have hcdp : s(c, d) ∉ p.edges := by
          intro hcontra
          exact hdsup (p.snd_mem_support_of_mem_edges hcontra)
        
        have hcdGpp : Gpp.Adj c d := by
          rw [hGpp, SimpleGraph.deleteEdges_adj]
          refine ⟨hcd, ?_⟩
          rw [Finset.mem_coe, List.mem_toFinset]
          exact hcdp
        exact ⟨c, d, hcdGpp, hcsup⟩
  
  obtain ⟨x, C, hCcyc, hCedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even Gpp hGpp_even hwz
  have hwC : w ∈ C.support := C.fst_mem_support_of_mem_edges hCedge
  set Cw := C.rotate w hwC with hCw
  have hCwcyc : Cw.IsCycle := hCcyc.rotate hwC
  
  set Cg := Cw.mapLe hGpp_le with hCg
  have hCgcyc : Cg.IsCycle := hCwcyc.mapLe hGpp_le
  have hCgedges : Cg.edges = Cw.edges := Cw.edges_mapLe_eq_edges hGpp_le
  
  have hdisj : ∀ e ∈ Cg.edges, e ∉ p.edges := by
    intro e he hep
    rw [hCgedges] at he
    
    have heGpp : e ∈ Gpp.edgeSet := Cw.edges_subset_edgeSet he
    rw [hGpp, SimpleGraph.edgeSet_deleteEdges] at heGpp
    apply heGpp.2
    rw [Finset.mem_coe, List.mem_toFinset]
    exact hep
  
  have hsplice_trail : (spliceWalk G p hwsup Cg).IsTrail :=
    spliceWalk_isTrail G hp hwsup hCgcyc.isTrail hdisj
  have hsplice_len : (spliceWalk G p hwsup Cg).length = p.length + Cg.length :=
    spliceWalk_length G p hwsup Cg
  have hClen : 3 ≤ Cg.length := hCgcyc.three_le_length
  have hcontra := hmax (spliceWalk G p hwsup Cg) hsplice_trail
  rw [hsplice_len] at hcontra
  omega




theorem closed_eulerian_length_eq_edgeFinset_card (G : SimpleGraph V) [DecidableRel G.Adj] {u : V}
    {p : G.Walk u u} (hp : p.IsTrail) (hcov : ∀ e ∈ G.edgeFinset, e ∈ p.edges) :
    p.length = G.edgeFinset.card := by
  classical
  
  have hset : p.edges.toFinset = G.edgeFinset := by
    apply Finset.ext
    intro e
    rw [List.mem_toFinset, SimpleGraph.mem_edgeFinset]
    constructor
    · intro he; exact p.edges_subset_edgeSet he
    · intro he; exact hcov e (SimpleGraph.mem_edgeFinset.mpr he)
  
  rw [← SimpleGraph.Walk.length_edges, ← List.toFinset_card_of_nodup hp.edges_nodup, hset]

omit [DecidableEq V] in




theorem exists_closed_eulerian_length (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (heven : ∀ x, Even (G.degree x)) (u : V) :
    ∃ p : G.Walk u u, p.IsTrail ∧ (∀ e ∈ G.edgeFinset, e ∈ p.edges) ∧
      p.length = G.edgeFinset.card := by
  obtain ⟨p, hp, hcov⟩ := exists_closed_eulerian G hconn heven u
  exact ⟨p, hp, hcov, closed_eulerian_length_eq_edgeFinset_card G hp hcov⟩

end EulerianExistence







namespace EulerianExistence

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]

omit [DecidableEq V] in
open scoped Classical in






theorem exists_closed_eulerian_of_finite_support
    (T : Finset V) (hsupp : G.support ⊆ (T : Set V))
    (hconn : (G.induce (T : Set V)).Connected)
    (heven : ∀ x, Even (G.degree x)) {u : V} (huT : u ∈ (T : Set V)) :
    ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  classical
  set H := G.induce (T : Set V) with hH
  haveI : Fintype (T : Set V) := FinsetCoe.fintype T
  haveI : DecidableRel H.Adj := Classical.decRel _
  
  have hdegH : ∀ x : (T : Set V), H.degree x = G.degree (x : V) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    refine Fintype.card_congr ?_
    refine ⟨fun y => ⟨(y.1 : V), y.2⟩, fun y => ⟨⟨y.1, hsupp y.2.symm.mem_support_left⟩, y.2⟩,
      ?_, ?_⟩
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hHeven : ∀ x : (T : Set V), Even (H.degree x) := by
    intro x; rw [hdegH x]; exact heven _
  
  obtain ⟨p, hp, hcov⟩ :=
    exists_closed_eulerian H hconn hHeven (⟨u, huT⟩ : (T : Set V))
  
  let emb : H ↪g G := SimpleGraph.Embedding.induce (T : Set V)
  refine ⟨p.map emb.toHom,
    SimpleGraph.Walk.map_isTrail_of_injective emb.injective hp, ?_⟩
  intro e he
  
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    have haT : a ∈ (T : Set V) := hsupp he.mem_support_left
    have hbT : b ∈ (T : Set V) := hsupp he.symm.mem_support_left
    have hadjH : H.Adj ⟨a, haT⟩ ⟨b, hbT⟩ := he
    have hmemH : s((⟨a, haT⟩ : (T : Set V)), (⟨b, hbT⟩ : (T : Set V))) ∈ p.edges :=
      hcov _ (SimpleGraph.mem_edgeFinset.mpr hadjH)
    
    have hmap := SimpleGraph.Walk.edges_map (f := emb.toHom) (p := p)
    have hgoal : s(a, b)
        = Sym2.map emb.toHom s((⟨a, haT⟩ : (T : Set V)), (⟨b, hbT⟩ : (T : Set V))) := by
      simp only [Sym2.map_mk]; rfl
    have hin : s(a, b) ∈ List.map (Sym2.map emb.toHom) p.edges := by
      rw [List.mem_map]; exact ⟨_, hmemH, hgoal.symm⟩
    rwa [← hmap] at hin

end EulerianExistence




















def FaceBoundaryConnected (K : Set (Site 2)) (T : Finset (Site 2)) : Prop :=
  ((faceBoundaryGraph K).induce (T : Set (Site 2))).Connected











theorem faceBoundaryGraph_single_dualCircuit {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (T : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges :=
  EulerianExistence.exists_closed_eulerian_of_finite_support (faceBoundaryGraph K) T hsupp hconn
    (degree_faceBoundaryGraph_even K) hf₀



noncomputable def boundarySupport {K : Set (Site 2)} (hK : K.Finite) : Finset (Site 2) :=
  (exists_finset_support_faceBoundaryGraph K hK).choose

theorem boundarySupport_spec {K : Set (Site 2)} (hK : K.Finite) :
    (faceBoundaryGraph K).support ⊆ (boundarySupport hK : Set (Site 2)) :=
  (exists_finset_support_faceBoundaryGraph K hK).choose_spec







theorem exists_single_dualCircuit_of_connected {K : Set (Site 2)} (hK : K.Finite)
    (hconn : FaceBoundaryConnected K (boundarySupport hK))
    {f₀ : Site 2} (hf₀ : f₀ ∈ (boundarySupport hK : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit (boundarySupport_spec hK) hconn hf₀










theorem faceBoundaryConnected_satisfiable_iff {K : Set (Site 2)} {T : Finset (Site 2)} :
    FaceBoundaryConnected K T ↔ ((faceBoundaryGraph K).induce (T : Set (Site 2))).Connected :=
  Iff.rfl









theorem triangle_connected : (completeGraph (Fin 3)).Connected := SimpleGraph.connected_top


theorem triangle_even_degree (v : Fin 3) : Even ((completeGraph (Fin 3)).degree v) := by
  rw [SimpleGraph.complete_graph_degree]
  decide





theorem triangle_eulerian :
    ∃ p : (completeGraph (Fin 3)).Walk 0 0,
      p.IsTrail ∧ (∀ e ∈ (completeGraph (Fin 3)).edgeFinset, e ∈ p.edges) ∧
        p.length = (completeGraph (Fin 3)).edgeFinset.card :=
  EulerianExistence.exists_closed_eulerian_length (completeGraph (Fin 3))
    triangle_connected triangle_even_degree 0


theorem triangle_edge_card : (completeGraph (Fin 3)).edgeFinset.card = 3 := by decide

end Lattice

end StatMech
