/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Sharpness.BkCriterion

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {V : Type*}







lemma shk_edges_subset_openSub (G : SimpleGraph V) (ω ω' : ConfigSpace (Sym2 V))
    {u x : V} (p : (openSub G ω).Walk u x)
    (hagree : agreeOn {e : Sym2 V | e ∈ p.edges} ω ω') :
    ∀ e ∈ p.edges, e ∈ (openSub G ω').edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨hGadj, hopen⟩ := p.adj_of_mem_edges he
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hGadj, by rw [hagree s(a, b) he]; exact hopen⟩






lemma shk_occursOn_connEvent_of_walk (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (S : Set V) (u x : V) (huS : u ∈ S) (hxS : x ∈ S)
    (p : (openSub G ω).Walk u x) (hsupp : ∀ z ∈ p.support, z ∈ S) :
    OccursOn (connEvent G S u {x}) {e : Sym2 V | e ∈ p.edges} ω := by
  intro ω' hagree
  refine ⟨huS, x, hxS, rfl, ?_⟩
  unfold ConnWithin
  set htrans := p.transfer (openSub G ω') (shk_edges_subset_openSub G ω ω' p hagree) with htdef
  have hsupp' : ∀ z ∈ htrans.support, z ∈ S := by
    intro z hz
    rw [htdef, SimpleGraph.Walk.support_transfer] at hz
    exact hsupp z hz
  exact ⟨(htrans.induce S hsupp').copy rfl rfl⟩




lemma shk_occursOn_connToSet_of_walk (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (A : Set V) (y b : V) (B : Set V) (hyA : y ∈ A) (hbA : b ∈ A) (hbB : b ∈ B)
    (p : (openSub G ω).Walk y b) (hsupp : ∀ z ∈ p.support, z ∈ A) :
    OccursOn (connEvent G A y B) {e : Sym2 V | e ∈ p.edges} ω := by
  intro ω' hagree
  refine ⟨hyA, b, hbA, hbB, ?_⟩
  unfold ConnWithin
  set htrans := p.transfer (openSub G ω') (shk_edges_subset_openSub G ω ω' p hagree) with htdef
  have hsupp' : ∀ z ∈ htrans.support, z ∈ A := by
    intro z hz
    rw [htdef, SimpleGraph.Walk.support_transfer] at hz
    exact hsupp z hz
  exact ⟨(htrans.induce A hsupp').copy rfl rfl⟩



lemma shk_occursOn_edgeOpenEvent (x y : V) (ω : ConfigSpace (Sym2 V))
    (hopen : ω s(x, y) = true) :
    OccursOn (edgeOpenEvent x y) {s(x, y)} ω := by
  intro ω' hagree
  simp only [edgeOpenEvent, Set.mem_setOf_eq]
  rw [hagree s(x, y) (Set.mem_singleton _)]; exact hopen






lemma shk_edge_getElem {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (i : ℕ)
    (h : i < p.length) :
    p.edges[i]'(by rw [SimpleGraph.Walk.length_edges]; exact h)
      = s(p.getVert i, p.getVert (i + 1)) := by
  induction p generalizing i with
  | nil => simp at h
  | cons hadj q ih =>
    cases i with
    | zero =>
      simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_zero,
        SimpleGraph.Walk.getVert_zero]
      congr 1
      rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
    | succ n =>
      simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_succ]
      rw [SimpleGraph.Walk.length_cons] at h
      rw [ih n (by omega), SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_cons_succ]







lemma shk_walk_of_connToSet (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (A : Set V) (u : V) (B : Set V) (h : ConnToSet G ω A u B) :
    ∃ (b : V) (_ : b ∈ A) (_ : b ∈ B) (p : (openSub G ω).Walk u b),
      ∀ z ∈ p.support, z ∈ A := by
  obtain ⟨hu, b, hbA, hbB, hconn⟩ := h
  obtain ⟨w⟩ := hconn
  set emb := (SimpleGraph.Embedding.induce (G := openSub G ω) A) with hemb
  set p : (openSub G ω).Walk u b := (w.map emb.toHom).copy rfl rfl with hp
  refine ⟨b, hbA, hbB, p, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨m, hm, _⟩ := hz
  have hgv : p.getVert m = ((w.getVert m : A) : V) := by
    rw [hp, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map]; rfl
  rw [← hm, hgv]
  exact (w.getVert m).2







lemma shk_occursOn_congr_config {A : Set (ConfigSpace V)} {K : Set V}
    {ω ω' : ConfigSpace V} (h : OccursOn A K ω) (hagree : agreeOn K ω ω') :
    OccursOn A K ω' := fun ω'' hω'' => h ω'' (agreeOn_trans hagree hω'')






lemma shk_occursOn_disjointOccurrence_union {A B : Set (ConfigSpace V)} {K L : Set V}
    {ω : ConfigSpace V} (hKL : Disjoint K L)
    (hA : OccursOn A K ω) (hB : OccursOn B L ω) :
    OccursOn (disjointOccurrence A B) (K ∪ L) ω := by
  intro ω' hagree
  exact ⟨K, L, hKL, shk_occursOn_congr_config hA (agreeOn_mono Set.subset_union_left hagree),
    shk_occursOn_congr_config hB (agreeOn_mono Set.subset_union_right hagree)⟩


















theorem shk_firstExit_triple [DecidableEq V] (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (A S B : Set V) (u b : V) (huS : u ∈ S) (hbB : b ∈ B) (hbS : b ∉ S)
    (p : (openSub G ω).Walk u b) (hpath : p.IsPath) (hsuppA : ∀ z ∈ p.support, z ∈ A) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y ∧
      ω ∈ disjointOccurrence (connEvent G S u {x})
        (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B)) := by
  classical
  have hbA : b ∈ A := hsuppA b (by simp [SimpleGraph.Walk.end_mem_support])
  
  obtain ⟨j, hjle, hjS, hbefore⟩ : ∃ j, j ≤ p.length ∧ p.getVert j ∉ S ∧
      ∀ i, i < j → p.getVert i ∈ S := by
    set Tt : Finset ℕ := (Finset.range (p.length + 1)).filter (fun n => p.getVert n ∉ S) with hT
    have hLmem : p.length ∈ Tt := by
      rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [p.getVert_length]; exact hbS⟩
    have hTne : Tt.Nonempty := ⟨p.length, hLmem⟩
    set j := Tt.min' hTne with hj
    have hjT : j ∈ Tt := Tt.min'_mem hTne
    rw [hT] at hjT
    simp only [Finset.mem_filter, Finset.mem_range] at hjT
    obtain ⟨hjle, hjD⟩ := hjT
    refine ⟨j, by omega, hjD, ?_⟩
    intro i hij
    by_contra hiD
    have hiT : i ∈ Tt := by
      rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hiD⟩
    have := Tt.min'_le i hiT
    rw [← hj] at this; omega
  
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h1
    · exact absurd huS (by rw [h0, p.getVert_zero] at hjS; exact hjS)
    · exact h1
  set x := p.getVert (j - 1) with hx
  set y := p.getVert j with hy
  have hxS : x ∈ S := hbefore (j - 1) (by omega)
  have hynS : y ∉ S := hjS
  have hjlen : j - 1 < p.length := by omega
  have hadj : (openSub G ω).Adj x y := by
    have := p.adj_getVert_succ hjlen
    rwa [show j - 1 + 1 = j from by omega] at this
  have hGadj : G.Adj x y := hadj.1
  have hopen : ω s(x, y) = true := hadj.2
  have hyA : y ∈ A := hsuppA y (by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]; exact ⟨j, rfl, hjle⟩)
  refine ⟨x, y, hxS, hynS, hGadj, ?_⟩
  
  have hpre_supp : ∀ z ∈ (p.take (j - 1)).support, z ∈ S := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨m, hm, _⟩ := hz
    rw [SimpleGraph.Walk.take_getVert] at hm
    rw [← hm]; exact hbefore (min (j - 1) m) (by omega)
  set ppre : (openSub G ω).Walk u x := (p.take (j - 1)).copy rfl rfl with hppre
  have hppre_supp : ∀ z ∈ ppre.support, z ∈ S := by
    intro z hz; rw [hppre, SimpleGraph.Walk.support_copy] at hz; exact hpre_supp z hz
  have hK1 : OccursOn (connEvent G S u {x}) {e : Sym2 V | e ∈ ppre.edges} ω :=
    shk_occursOn_connEvent_of_walk G ω S u x huS hxS ppre hppre_supp
  
  have hsuf_supp : ∀ z ∈ (p.drop j).support, z ∈ A := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨m, hm, _⟩ := hz
    rw [SimpleGraph.Walk.drop_getVert] at hm
    apply hsuppA
    rw [← hm, SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨j + m, rfl, by have := SimpleGraph.Walk.drop_length p j; omega⟩
  set psuf : (openSub G ω).Walk y b := (p.drop j).copy rfl rfl with hpsuf
  have hpsuf_supp : ∀ z ∈ psuf.support, z ∈ A := by
    intro z hz; rw [hpsuf, SimpleGraph.Walk.support_copy] at hz; exact hsuf_supp z hz
  have hK3 : OccursOn (connEvent G A y B) {e : Sym2 V | e ∈ psuf.edges} ω :=
    shk_occursOn_connToSet_of_walk G ω A y b B hyA hbA hbB psuf hpsuf_supp
  have hK2 : OccursOn (edgeOpenEvent x y) {s(x, y)} ω :=
    shk_occursOn_edgeOpenEvent x y ω hopen
  
  have hppre_edges : ppre.edges = List.take (j - 1) p.edges := by
    rw [hppre, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_take]
  have hpsuf_edges : psuf.edges = List.drop j p.edges := by
    rw [hpsuf, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_drop]
  
  have hnd : p.edges.Nodup := hpath.edges_nodup
  have hlenE : j - 1 < p.edges.length := by rw [SimpleGraph.Walk.length_edges]; omega
  have hxyedge : s(x, y) = p.edges[j - 1]'hlenE := by
    have := shk_edge_getElem p (j - 1) hjlen
    rw [show j - 1 + 1 = j from by omega] at this
    exact this.symm
  
  have hcons : List.drop (j - 1) p.edges = s(x, y) :: List.drop j p.edges := by
    rw [List.drop_eq_getElem_cons hlenE, show j - 1 + 1 = j from by omega, hxyedge]
  have hxy_mem_dropj1 : s(x, y) ∈ List.drop (j - 1) p.edges := by
    rw [hcons]; exact List.mem_cons_self
  have hnd_drop : (List.drop (j - 1) p.edges).Nodup := hnd.sublist (List.drop_sublist _ _)
  have hxy_notin_dropj : s(x, y) ∉ List.drop j p.edges := by
    rw [hcons] at hnd_drop; exact (List.nodup_cons.mp hnd_drop).1
  have hxy_notin_takej1 : s(x, y) ∉ List.take (j - 1) p.edges := fun hmem =>
    List.disjoint_take_drop hnd (le_refl (j - 1)) hmem hxy_mem_dropj1
  have hdisj13 : (List.take (j - 1) p.edges).Disjoint (List.drop j p.edges) :=
    List.disjoint_take_drop hnd (by omega)
  
  have hdisjK2K3 : Disjoint ({s(x, y)} : Set (Sym2 V)) {e : Sym2 V | e ∈ psuf.edges} := by
    rw [Set.disjoint_left]
    intro e he1 he3
    rw [Set.mem_singleton_iff] at he1; rw [he1, hpsuf_edges] at he3
    exact hxy_notin_dropj he3
  have hdisjK1K23 : Disjoint {e : Sym2 V | e ∈ ppre.edges}
      ({s(x, y)} ∪ {e : Sym2 V | e ∈ psuf.edges}) := by
    rw [Set.disjoint_left]
    intro e he1 he23
    rw [Set.mem_setOf_eq, hppre_edges] at he1
    rcases he23 with he2 | he3
    · rw [Set.mem_singleton_iff] at he2; rw [he2] at he1; exact hxy_notin_takej1 he1
    · rw [Set.mem_setOf_eq, hpsuf_edges] at he3; exact hdisj13 he1 he3
  
  have hinner : OccursOn (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B))
      ({s(x, y)} ∪ {e : Sym2 V | e ∈ psuf.edges}) ω :=
    shk_occursOn_disjointOccurrence_union hdisjK2K3 hK2 hK3
  exact ⟨{e : Sym2 V | e ∈ ppre.edges}, {s(x, y)} ∪ {e : Sym2 V | e ∈ psuf.edges},
    hdisjK1K23, hK1, hinner⟩






def shk_boundaryPairs [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    [DecidableRel G.Adj] : Finset (V × V) :=
  Finset.univ.filter (fun q => q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2)

@[simp] lemma shk_mem_boundaryPairs [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) [DecidableRel G.Adj] {q : V × V} :
    q ∈ shk_boundaryPairs G S ↔ q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2 := by
  simp [shk_boundaryPairs]
















theorem shk_firstExit_inclusion [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Set V) (S : Finset V) (B : Set V) (u : V)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent G A u B ⊆
      ⋃ q ∈ shk_boundaryPairs G S, disjointOccurrence (connEvent G (S : Set V) u {q.1})
        (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent G A q.2 B)) := by
  intro ω hω
  simp only [connEvent, Set.mem_setOf_eq] at hω
  obtain ⟨b, hbA, hbB, p, hpsupp⟩ := shk_walk_of_connToSet G ω A u B hω
  have hbypass_supp : ∀ z ∈ p.bypass.support, z ∈ A := fun z hz =>
    hpsupp z (p.support_bypass_subset hz)
  have hbS : b ∉ (S : Set V) := hBS b hbB
  obtain ⟨x, y, hxS, hynS, hGadj, htriple⟩ :=
    shk_firstExit_triple G ω A (S : Set V) B u b huS hbB hbS p.bypass p.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), by rw [shk_mem_boundaryPairs]; exact ⟨hxS, hynS, hGadj⟩, htriple⟩

end Sharpness

end StatMech
