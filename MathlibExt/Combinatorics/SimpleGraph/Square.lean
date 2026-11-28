/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

import MathlibExt.Combinatorics.SimpleGraph.HamiltonianCycle

/-!
# Squares of simple graphs

This file defines the square of a simple graph and proves its basic properties.
-/

@[expose] public section

namespace SimpleGraph

/-- **Square of a graph.** The square of a simple graph $G$ is the simple graph on the same vertex
set in which two distinct vertices $u$ and $v$ are adjacent when they are adjacent in $G$ or have
a common neighbor in $G$, that is, a vertex $w$ adjacent in $G$ to both $u$ and $v$. -/
public def square {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.elim (fun huv ↦ Or.inl huv.symm)
    (fun ⟨w, huw, hwv⟩ ↦ Or.inr ⟨w, hwv.symm, huw.symm⟩)⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- **Adjacency in the graph square.** For a simple graph $G$ and vertices $u$ and $v$, the
vertices $u$ and $v$ are adjacent in the square of $G$ if and only if $u \ne v$ and either $u$
and $v$ are adjacent in $G$ or there is a vertex $w$ with $u$ adjacent to $w$ and $w$ adjacent
to $v$ in $G$. -/
@[simp]
public theorem square_adj {V : Type*} (G : SimpleGraph V) (u v : V) :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) :=
  Iff.rfl

/-- **Monotonicity of the graph square.** Let $G$ and $H$ be simple graphs on the same vertex set
such that every edge of $G$ is an edge of $H$. Then every edge of the square of $G$ is an edge of
the square of $H$. -/
public theorem square_mono {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H) :
    G.square ≤ H.square := by
  rintro u v ⟨huv, h | ⟨w, huw, hwv⟩⟩
  · exact ⟨huv, Or.inl (hGH h)⟩
  · exact ⟨huv, Or.inr ⟨w, hGH huw, hGH hwv⟩⟩

/-- **The square of a connected graph is connected.** If a simple graph $G$ is connected, then
the square of $G$ is connected. -/
public theorem Connected.square {V : Type*} {G : SimpleGraph V} (hG : G.Connected) :
    G.square.Connected :=
  hG.mono fun _ _ h ↦ ⟨G.ne_of_adj h, Or.inl h⟩

/-- **Adding edges preserves a Hamiltonian square.** Let $G$ and $H$ be simple graphs on the same
finite vertex set such that every edge of $G$ is an edge of $H$. If the square of $G$ is
Hamiltonian, then the square of $H$ is Hamiltonian. -/
public theorem IsHamiltonian.square_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) (hG : G.square.IsHamiltonian) : H.square.IsHamiltonian :=
  hG.mono (SimpleGraph.square_mono hGH)

/-- **Characterization of the graph square.** Let $G$ and $H$ be simple graphs on the same vertex
set. Then $H$ equals the square of $G$ if and only if, for all vertices $u$ and $v$, the vertices
$u$ and $v$ are adjacent in $H$ exactly when $u \ne v$ and either $u$ and $v$ are adjacent in $G$
or there is a vertex $w$ with $u$ adjacent to $w$ and $w$ adjacent to $v$ in $G$. -/
public theorem eq_square_iff {V : Type*} {G H : SimpleGraph V} :
    H = G.square ↔
      ∀ u v, H.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
  constructor
  · rintro rfl u v
    exact square_adj G u v
  · intro h
    ext u v
    exact h u v

/-- **Skipping a vertex of a walk in the graph square.** Let $G$ be a simple graph and let
$u, w, v, x_1, \dots, x_k$ (with $k \ge 0$) be a sequence of vertices in which consecutive
vertices are adjacent in $G$. If $u \ne v$, then in the sequence $u, v, x_1, \dots, x_k$
consecutive vertices are adjacent in the square of $G$. -/
public theorem isChain_square_of_isChain_cons_cons {V : Type*} {G : SimpleGraph V}
    {u w v : V} {l : List V} (hchain : List.IsChain G.Adj (u :: w :: v :: l))
    (huv : u ≠ v) : List.IsChain G.square.Adj (u :: v :: l) := by
  have huw := (List.isChain_cons_cons.mp hchain).1
  have hrest := (List.isChain_cons_cons.mp hchain).2
  have hwv := (List.isChain_cons_cons.mp hrest).1
  have htail := (List.isChain_cons_cons.mp hrest).2
  rw [List.isChain_cons_cons]
  refine ⟨⟨huv, Or.inr ⟨w, huw, hwv⟩⟩, ?_⟩
  exact htail.imp fun ⦃_ _⦄ hab ↦ ⟨G.ne_of_adj hab, Or.inl hab⟩

/-- **A cyclic listing by square adjacencies gives a Hamiltonian square.** Let $G$ be a simple
graph on a finite vertex set $V$, and let $v_0, v_1, \dots, v_n$ be vertices with $n \ge 3$ and
$v_0 = v_n$, such that $v_1, \dots, v_n$ are pairwise distinct and every vertex of $V$ is among
them. If for each $i < n$ the vertices $v_i$ and $v_{i+1}$ are distinct and either adjacent in
$G$ or have a common neighbor in $G$, then the square of $G$ is Hamiltonian. -/
public theorem IsHamiltonian.square_of_cyclic_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l : List V) (hne : l ≠ [])
    (hclosed : l.head hne = l.getLast hne)
    (hsteps : l.IsChain fun u v ↦
      u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))
    (hnodup : l.tail.Nodup) (hmem : ∀ v, v ∈ l.tail)
    (hthree : 3 ≤ l.length - 1) : G.square.IsHamiltonian := by
  apply IsHamiltonian.of_cyclic_list G.square l hne hclosed
  · exact hsteps
  · exact hnodup
  · exact hmem
  · exact hthree

/-- **Minimum degree in the square of a 2-connected graph.** In a 2-vertex-connected simple graph
on a finite vertex set with at least five vertices, every vertex has at least four neighbors in
the square of the graph. -/
public theorem IsVertexConnected.four_le_square_degree
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.square.Adj] (hG : G.IsVertexConnected 2)
    (hcard : 5 ≤ Fintype.card V) (v : V) : 4 ≤ G.square.degree v := by
  classical
  have hdeg : 2 ≤ G.degree v := hG.two_le_degree v
  by_contra hfour
  have hsdeg : G.square.degree v ≤ 3 := by omega
  set N := G.neighborFinset v with hNdef
  set S := G.square.neighborFinset v with hSdef
  set T := S \ N with hTdef
  have hNS : N ⊆ S := by
    intro u hu
    rw [hNdef, mem_neighborFinset] at hu
    rw [hSdef, mem_neighborFinset]
    exact ⟨G.ne_of_adj hu, Or.inl hu⟩
  have hNcard : N.card = G.degree v := card_neighborFinset_eq_degree G v
  have hScard : S.card = G.square.degree v := card_neighborFinset_eq_degree G.square v
  have hTcard : T.card < 2 := by
    rw [hTdef, Finset.card_sdiff_of_subset hNS, hNcard, hScard]
    omega
  have hdel := hG.connected_induce_compl T hTcard
  have hvS : v ∉ S := by
    rw [hSdef, mem_neighborFinset]
    exact G.square.loopless.1 v
  have hcard_insert : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
  have hsmall : (insert v S).card < Fintype.card V := by
    rw [hcard_insert, hScard]
    omega
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ insert v S := by
    by_contra! hall
    have huniv : insert v S = Finset.univ := Finset.eq_univ_of_forall hall
    have hc := congrArg Finset.card huniv
    simp only [Finset.card_univ] at hc
    omega
  have hvT : v ∉ T := by
    intro hv
    exact hvS (Finset.mem_sdiff.mp hv).1
  have hwS : w ∉ S := fun h ↦ hw (Finset.mem_insert_of_mem h)
  have hwT : w ∉ T := by
    intro h
    exact hwS (Finset.mem_sdiff.mp h).1
  let v' : {x : V // x ∈ (↑T : Set V)ᶜ} := ⟨v, by simpa using hvT⟩
  let w' : {x : V // x ∈ (↑T : Set V)ᶜ} := ⟨w, by simpa using hwT⟩
  set A := insert v N with hAdef
  have hvA : v ∈ A := Finset.mem_insert_self v N
  have hwA : w ∉ A := by
    intro h
    rw [hAdef, Finset.mem_insert] at h
    rcases h with hwv | hN
    · exact hw (hwv ▸ Finset.mem_insert_self v S)
    · exact hwS (hNS hN)
  have hclosed : ∀ (x y : {z : V // z ∈ (↑T : Set V)ᶜ}),
      x.1 ∈ A → (G.induce (↑T : Set V)ᶜ).Adj x y → y.1 ∈ A := by
    intro x y hx hxy
    have hxyG : G.Adj x y := induce_adj.mp hxy
    rw [hAdef, Finset.mem_insert] at hx ⊢
    rcases hx with hx | hx
    · right
      rw [hx] at hxyG
      rw [hNdef, mem_neighborFinset]
      exact hxyG
    · by_cases hyv : (y : V) = v
      · exact Or.inl hyv
      · right
        have hvx : G.Adj v x := by
          rw [← mem_neighborFinset]
          exact hx
        have hyS : (y : V) ∈ S := by
          rw [hSdef, mem_neighborFinset]
          exact ⟨Ne.symm hyv, Or.inr ⟨x, hvx, hxyG⟩⟩
        have hyT : (y : V) ∉ T := by
          have h := y.property
          change (y : V) ∉ T at h
          exact h
        by_contra hyN
        exact hyT (Finset.mem_sdiff.mpr ⟨hyS, hyN⟩)
  have hwalk_closed : ∀ (x y : {z : V // z ∈ (↑T : Set V)ᶜ})
      (p : (G.induce (↑T : Set V)ᶜ).Walk x y), x.1 ∈ A → y.1 ∈ A := by
    intro x y p hx
    induction p with
    | nil => exact hx
    | @cons _ _ _ h p ih => exact ih (hclosed _ _ hx h)
  obtain ⟨p⟩ := hdel v' w'
  exact hwA (hwalk_closed v' w' p hvA)

end SimpleGraph
