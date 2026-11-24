/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Vertex connectivity

A shared vertex-connectivity predicate for finite simple graphs.
-/

@[expose] public section

namespace SimpleGraph

/-- **$k$-vertex-connected graph.** Let $k$ be a natural number. A simple graph $G$ on a finite
vertex set $V$ is $k$-vertex-connected if $V$ has more than $k$ elements and, for every set $S$ of
fewer than $k$ vertices, the subgraph of $G$ induced on $V \setminus S$ is connected. -/
public def IsVertexConnected {V : Type*} [Fintype V] (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected

/-- **Characterization of $k$-vertex-connectivity by vertex deletion.** Let $k$ be a natural
number and let $G$ be a simple graph on a finite vertex set $V$. Then $G$ is $k$-vertex-connected
if and only if $V$ has more than $k$ elements and, for every set $S$ of fewer than $k$ vertices,
the subgraph of $G$ induced on $V \setminus S$ is connected. -/
public theorem isVertexConnected_iff {V : Type*} [Fintype V] {k : ℕ} {G : SimpleGraph V} :
    G.IsVertexConnected k ↔
      k < Fintype.card V ∧
        ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected :=
  Iff.rfl

/-- **Vertex count of a $k$-vertex-connected graph.** Let $k$ be a natural number. If a simple
graph $G$ on a finite vertex set $V$ is $k$-vertex-connected, then $V$ has more than $k$
elements. -/
public theorem IsVertexConnected.card_gt {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) : k < Fintype.card V :=
  hG.1

/-- **Deleting fewer than $k$ vertices from a $k$-vertex-connected graph.** Let $k$ be a natural
number and let $G$ be a $k$-vertex-connected simple graph on a finite vertex set $V$. Then for
every set $S$ of fewer than $k$ vertices, the subgraph of $G$ induced on $V \setminus S$ is
connected. -/
public theorem IsVertexConnected.connected_induce_compl {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (S : Finset V) (hS : S.card < k) :
    (G.induce (S : Set V)ᶜ).Connected :=
  hG.2 S hS

/-- **A $k$-vertex-connected graph with $k \ge 1$ is connected.** Let $k \ge 1$ be a natural
number. Every $k$-vertex-connected simple graph on a finite vertex set is connected. -/
public theorem IsVertexConnected.connected {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (hk : 0 < k) : G.Connected := by
  have h := hG.connected_induce_compl ∅ (by simpa using hk)
  have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by
    ext
    simp
  rw [hs] at h
  exact G.induceUnivIso.connected_iff.mp h

/-- **Deleting one vertex from a $k$-vertex-connected graph with $k \ge 2$.** Let $k \ge 2$ be a
natural number and let $G$ be a $k$-vertex-connected simple graph on a finite vertex set $V$.
Then for every vertex $v$, the subgraph of $G$ induced on $V \setminus \{v\}$ is connected. -/
public theorem IsVertexConnected.connected_compl_singleton {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (hk : 1 < k) (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
  classical
  exact hG.connected_induce_compl {v} (by simpa using hk)

/-- **Characterization of 2-vertex-connected graphs.** A simple graph $G$ on a finite vertex set
$V$ is 2-vertex-connected if and only if $V$ has more than two elements, $G$ is connected, and
for every vertex $v$ the subgraph of $G$ induced on $V \setminus \{v\}$ is connected. -/
public theorem isVertexConnected_two_iff {V : Type*} [Fintype V] {G : SimpleGraph V} :
    G.IsVertexConnected 2 ↔
      2 < Fintype.card V ∧ G.Connected ∧
        ∀ v, (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
  classical
  constructor
  · intro hG
    exact ⟨hG.card_gt, hG.connected (by omega),
      hG.connected_compl_singleton (by omega)⟩
  · rintro ⟨hcard, hconn, hdelete⟩
    refine ⟨hcard, fun S hS ↦ ?_⟩
    have hcardS : S.card = 0 ∨ S.card = 1 := by omega
    rcases hcardS with hzero | hone
    · rw [Finset.card_eq_zero.mp hzero]
      have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
      rw [hs]
      exact G.induceUnivIso.connected_iff.mpr hconn
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      exact hdelete v

/-- **Degrees in a 2-vertex-connected graph are at least two.** Every vertex of a 2-vertex-connected
simple graph on a finite vertex set has degree at least two. -/
public theorem IsVertexConnected.two_le_degree {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsVertexConnected 2) (v : V) :
    2 ≤ G.degree v := by
  classical
  have hcard : 2 < Fintype.card V := hG.card_gt
  have hconn : G.Connected := hG.connected (by omega)
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, huv⟩ := exists_adj_iff_not_isIsolated.mpr
    (hconn.preconnected.not_isIsolated v)
  have huv_ne : u ≠ v := (G.ne_of_adj huv).symm
  have hrest : ((Finset.univ.erase u).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      omega
    · exact Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ v⟩
  obtain ⟨w, hw⟩ := hrest
  rw [Finset.mem_erase, Finset.mem_erase] at hw
  let v' : {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨v, by simpa using huv_ne.symm⟩
  let w' : {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨w, by simpa using hw.2.1⟩
  let _ : Nontrivial {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨v', w', by
      intro h
      exact hw.1 (congrArg Subtype.val h).symm⟩
  have hdel := hG.connected_compl_singleton (by omega) u
  obtain ⟨z, hvz⟩ := exists_adj_iff_not_isIsolated.mpr
    (hdel.preconnected.not_isIsolated v')
  have hvzG : G.Adj v z := induce_adj.mp hvz
  have huz : u ≠ z := by
    have hzu : (z : V) ≠ u := by simpa using z.property
    exact hzu.symm
  have hsub : ({u, (z : V)} : Finset V) ⊆ G.neighborFinset v := by
    intro t ht
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [mem_neighborFinset]
    rcases ht with rfl | rfl
    · exact huv
    · exact hvzG
  rw [← card_neighborFinset_eq_degree]
  calc
    2 = ({u, (z : V)} : Finset V).card := (Finset.card_pair huz).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub

/-- **Cycles through each vertex of a 2-vertex-connected graph.** Let $G$ be a 2-vertex-connected
simple graph on a finite vertex set. Then for every vertex $x$ of $G$ there is a cycle in $G$
that starts and ends at $x$. -/
public theorem IsVertexConnected.exists_cycle_through {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.IsVertexConnected 2) (x : V) :
    ∃ c : G.Walk x x, c.IsCycle := by
  classical
  have hcard : 1 < (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    have := hG.two_le_degree x
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp hcard
  rw [mem_neighborFinset] at hu hv
  let s : Set V := (↑({x} : Finset V) : Set V)ᶜ
  let u' : s := ⟨u, by simpa [s] using (G.ne_of_adj hu).symm⟩
  let v' : s := ⟨v, by simpa [s] using (G.ne_of_adj hv).symm⟩
  obtain ⟨q, hq⟩ := (hG.connected_compl_singleton (by omega) x).exists_isPath u' v'
  let p : G.Walk u v := q.map (Embedding.induce s).toHom
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hx : x ∉ p.support := by
    change x ∉ (q.map (Embedding.induce s).toHom).support
    rw [Walk.support_map]
    intro hxmem
    obtain ⟨z, -, hzx⟩ := List.mem_map.mp hxmem
    exact z.property (by simpa [s, hzx])
  let r : G.Walk u x := p.concat hv.symm
  have hr : r.IsPath := hp.concat hx hv.symm
  let c : G.Walk x x := Walk.cons hu r
  refine ⟨c, (Walk.cons_isCycle_iff r hu).mpr ⟨hr, ?_⟩⟩
  intro he
  simp only [r, Walk.edges_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton] at he
  rcases he with he | he
  · exact hx (p.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨_, hux⟩ | ⟨_, huv'⟩
    · exact hu.ne hux.symm
    · exact huv huv'

end SimpleGraph
