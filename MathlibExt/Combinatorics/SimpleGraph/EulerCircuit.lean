/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Trails

/-!
# Euler circuits

This file proves the existence direction of Euler's theorem for finite simple graphs.
-/

@[expose] public section

namespace SimpleGraph

/-- **Edges at a vertex of an Eulerian trail.** Let $G$ be a finite simple graph and let $p$ be an
Eulerian trail in $G$, that is, a walk between any two vertices that uses every edge of $G$
exactly once. Then for every vertex $x$, the number of edges of $p$ that contain $x$, counted
with multiplicity along $p$, equals the degree of $x$ in $G$. -/
public theorem Walk.IsEulerian.countP_edges_eq_degree {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (hp : p.IsEulerian) (x : V) :
    p.edges.countP (x ∈ ·) = G.degree x := by
  calc
    p.edges.countP (x ∈ ·) =
        (hp.isTrail.edgesFinset.filter (x ∈ ·)).card := by
      rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
      change Multiset.card _ = Multiset.card _
      rw [Finset.filter_val]
    _ = (G.incidenceFinset x).card := by
      rw [hp.edgesFinset_eq, G.incidenceFinset_eq_filter]
    _ = G.degree x := G.card_incidenceFinset_eq_degree x

/-- **Euler circuits in connected even graphs.** Every finite connected simple graph in which every
vertex has even degree has a closed Eulerian trail, that is, a closed walk that uses every edge of
the graph exactly once. -/
public theorem Connected.exists_isEulerian {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  classical
  let _ : Nonempty V := hG.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length G
  have hend : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := by
    intro w hvw
    by_contra hvw_edges
    have hp' : (p.concat hvw).IsTrail := hp.concat hvw hvw_edges
    have hle := hmax u w (p.concat hvw) hp'
    simp only [SimpleGraph.Walk.length_concat] at hle
    omega
  have huv : u = v := by
    by_contra huv
    have hinc : hp.edgesFinset.filter (v ∈ ·) = G.incidenceFinset v := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, mem_incidenceFinset,
        mk'_mem_incidenceSet_iff, Sym2.mem_iff]
      constructor
      · rintro ⟨he, hve⟩
        exact ⟨p.edges_subset_edgeSet he, hve⟩
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨hend b hab, Or.inl rfl⟩
        · refine ⟨?_, Or.inr rfl⟩
          change s(a, v) ∈ p.edges
          rw [Sym2.eq_swap]
          exact hend a hab.symm
    have hcount : p.edges.countP (v ∈ ·) = G.degree v := by
      calc
        p.edges.countP (v ∈ ·) = (hp.edgesFinset.filter (v ∈ ·)).card := by
          rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
          change Multiset.card _ = Multiset.card _
          rw [Finset.filter_val]
        _ = (G.incidenceFinset v).card := congrArg Finset.card hinc
        _ = G.degree v := G.card_incidenceFinset_eq_degree v
    have hp_even : Even (p.edges.countP (v ∈ ·)) := by
      rw [hcount]
      exact heven v
    exact ((hp.even_countP_edges_iff v).mp hp_even huv).2 rfl
  subst v
  have hno_extend : ∀ {x y}, x ∈ p.support → G.Adj x y →
      s(x, y) ∉ p.edges → False := by
    intro x y hx hxy hxy_edges
    have hrotate : (p.rotate x hx).IsTrail := hp.rotate hx
    have hxy_rotate : s(x, y) ∉ (p.rotate x hx).edges := by
      intro hmem
      exact hxy_edges ((p.rotate_edges x hx).mem_iff.mp hmem)
    have hlonger : ((p.rotate x hx).concat hxy).IsTrail :=
      hrotate.concat hxy hxy_rotate
    have hle := hmax x y ((p.rotate x hx).concat hxy) hlonger
    simp only [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_rotate] at hle
    omega
  refine ⟨u, p, hp.isEulerian_of_forall_mem ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp he
      by_contra hab_edges
      obtain ⟨q⟩ := hG u a
      have hreach : ∀ {x y} (q : G.Walk x y), x ∈ p.support →
          y ∈ p.support ∨
            ∃ z w, z ∈ p.support ∧ G.Adj z w ∧ s(z, w) ∉ p.edges := by
        intro x y q hx
        induction q with
        | nil => exact Or.inl hx
        | @cons x z y hxz q ih =>
            by_cases hxz_edges : s(x, z) ∈ p.edges
            · exact ih (p.snd_mem_support_of_mem_edges hxz_edges)
            · exact Or.inr ⟨x, z, hx, hxz, hxz_edges⟩
      rcases hreach q p.start_mem_support with ha | ⟨x, y, hx, hxy, hxy_edges⟩
      · exact hno_extend ha hab hab_edges
      · exact hno_extend hx hxy hxy_edges

/-- Every vertex of a walk starting in the graph support is itself in the graph support. -/
private theorem Walk.support_subset_graph_support {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hu : u ∈ G.support) :
    ∀ z ∈ p.support, z ∈ G.support := by
  induction p with
  | nil => simpa
  | @cons u w v huw p ih =>
      intro z hz
      rw [Walk.support_cons] at hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact G.mem_support.mpr ⟨w, huw⟩
      · apply ih (G.mem_support.mpr ⟨u, huw.symm⟩)
        exact hz

/-- **Reachability among non-isolated vertices.** Let $G$ be a simple graph and let $u$ and $v$ be
non-isolated vertices of $G$, that is, vertices with at least one neighbour. If $v$ is reachable
from $u$ in $G$, then $v$ is reachable from $u$ in the subgraph of $G$ induced on the set of
non-isolated vertices. -/
public theorem Reachable.induce_support {V : Type*} {G : SimpleGraph V}
    {u v : V} (h : G.Reachable u v) (hu : u ∈ G.support) (hv : v ∈ G.support) :
    (G.induce G.support).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨p⟩ := h
  let q := p.induce G.support (p.support_subset_graph_support hu)
  exact ⟨q⟩

/-- **Euler circuits in simple graphs whose non-isolated vertices are connected.** Let $G$ be a
finite simple graph in which every vertex has even degree, and suppose that the subgraph of $G$
induced on its non-isolated vertices is connected (in particular nonempty, so $G$ has at least
one edge). Then $G$ has a closed Eulerian trail, that is, a closed walk that uses every edge of
$G$ exactly once.

Isolated vertices are irrelevant to an Euler tour. -/
public theorem ConnectedSupport.exists_isEulerian {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : (G.induce G.support).Connected)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  classical
  have hind_even : ∀ v : G.support, Even ((G.induce G.support).degree v) := by
    intro v
    rw [G.degree_induce_support]
    exact heven v
  obtain ⟨u, p, hp⟩ := hG.exists_isEulerian hind_even
  let f : G.induce G.support →g G := (Embedding.induce G.support).toHom
  let q := p.map f
  refine ⟨u.1, q, ?_⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext hab
  have htrail : q.IsTrail := hp.isTrail.map hf
  apply htrail.isEulerian_of_forall_mem
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp he
      have ha : a ∈ G.support := G.mem_support.mpr ⟨b, hab⟩
      have hb : b ∈ G.support := G.mem_support.mpr ⟨a, hab.symm⟩
      let a' : G.support := ⟨a, ha⟩
      let b' : G.support := ⟨b, hb⟩
      have hab' : (G.induce G.support).Adj a' b' := hab
      have hedge' : s(a', b') ∈ (G.induce G.support).edgeSet :=
        (G.induce G.support).mem_edgeSet.mpr hab'
      have hpedge : s(a', b') ∈ p.edges := hp.mem_edges_iff.mpr hedge'
      rw [SimpleGraph.Walk.edges_map]
      apply List.mem_map.mpr
      exact ⟨s(a', b'), hpedge, by simp [f, a', b']⟩

end SimpleGraph
