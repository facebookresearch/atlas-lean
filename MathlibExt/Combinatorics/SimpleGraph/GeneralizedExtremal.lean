/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

/-!
# Generalized Turán number

Source: Alon and Shikhelman, "Many T copies in H-free graphs,"
arXiv:1409.4192v2, TeX lines 85-87:
"For two graphs T and H with no isolated vertices and for an integer n,
let ex(n,T,H) denote the maximum possible number of copies of T in an
H-free graph on n vertices."

This module defines `SimpleGraph.generalizedExtremalNumber` from that source,
using Mathlib's `SimpleGraph.copyCount`, `SimpleGraph.Free`, and the
`Finset.sup` pattern used by `SimpleGraph.extremalNumber`.

The source assumes `T` and `H` have no isolated vertices; this is documented
as the intended domain. The definition and lemmas below are stated more
generally without that hypothesis.
-/

namespace SimpleGraph

/-- **Generalized Turán number.** Let $n$ be a natural number and let $T$ and $H$ be simple graphs,
where $T$ has finitely many vertices. A copy of a graph in a graph $G$ is a subgraph of $G$
isomorphic to it, and $G$ is $H$-free if it contains no copy of $H$. The generalized Turán number
$\mathrm{ex}(n, T, H)$ is the largest number of copies of $T$ in an $H$-free simple graph on the
vertex set $\{0, 1, \dots, n-1\}$, and is $0$ if there is no such graph.

The source considers graphs $T$ and $H$ without isolated vertices; the definition does not require
this. -/
public noncomputable def generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β) : ℕ := by
  classical
  exact Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (fun G => G.copyCount T)

open Classical in
/-- **The generalized Turán number as a supremum.** Let $n$ be a natural number and let $T$ and $H$
be simple graphs, where $T$ has finitely many vertices. Then the generalized Turán number
$\mathrm{ex}(n, T, H)$ is the supremum in $\mathbb{N}$, with the supremum of the empty family taken
to be $0$, of the number of copies of $T$ in $G$ over all simple graphs $G$ on the vertex set
$\{0, 1, \dots, n-1\}$ that contain no copy of $H$ (a subgraph isomorphic to $H$). -/
public theorem generalizedExtremalNumber_eq_sup (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β) :
    generalizedExtremalNumber n T H =
      Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
        (fun G => G.copyCount T) := by
  classical
  unfold generalizedExtremalNumber
  rfl

/-- **The generalized Turán number is an upper bound.** Let $n$ be a natural number and let $T$ and
$H$ be simple graphs, where $T$ has finitely many vertices. If $G$ is a simple graph on the vertex
set $\{0, 1, \dots, n-1\}$ that contains no copy of $H$ (a subgraph isomorphic to $H$), then the
number of copies of $T$ in $G$ is at most the generalized Turán number $\mathrm{ex}(n, T, H)$. -/
public theorem copyCount_le_generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (G : SimpleGraph (Fin n)) (hG : H.Free G) :
    G.copyCount T ≤ generalizedExtremalNumber n T H := by
  classical
  unfold generalizedExtremalNumber
  apply Finset.le_sup (s := Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (f := fun G => G.copyCount T) (b := G)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩

/-- **Upper bounds for the generalized Turán number.** Let $n$ and $m$ be natural numbers and let
$T$ and $H$ be simple graphs, where $T$ has finitely many vertices. Then the generalized Turán
number $\mathrm{ex}(n, T, H)$ is at most $m$ if and only if every simple graph on the vertex set
$\{0, 1, \dots, n-1\}$ that contains no copy of $H$ (a subgraph isomorphic to $H$) has at most $m$
copies of $T$. -/
public theorem generalizedExtremalNumber_le_iff (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (m : ℕ) :
    generalizedExtremalNumber n T H ≤ m ↔
      ∀ G : SimpleGraph (Fin n), H.Free G → G.copyCount T ≤ m := by
  classical
  unfold generalizedExtremalNumber
  rw [Finset.sup_le_iff]
  constructor
  · intro h G hG
    exact h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩)
  · intro h b hb
    exact h b (Finset.mem_filter.mp hb).2

/-- **The generalized Turán number is attained.** Let $n$ be a natural number and let $T$ and $H$
be simple graphs, where $T$ has finitely many vertices. If some simple graph on the vertex set
$\{0, 1, \dots, n-1\}$ contains no copy of $H$ (a subgraph isomorphic to $H$), then some such graph
$G$ has exactly $\mathrm{ex}(n, T, H)$ copies of $T$, where $\mathrm{ex}(n, T, H)$ is the
generalized Turán number. -/
public theorem exists_free_copyCount_eq_generalizedExtremalNumber (n : ℕ)
    {α β : Type*} [Fintype α]
    (T : SimpleGraph α) (H : SimpleGraph β)
    (hne : ∃ G : SimpleGraph (Fin n), H.Free G) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.copyCount T = generalizedExtremalNumber n T H := by
  classical
  have hne' : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)).Nonempty := by
    obtain ⟨G0, hG0⟩ := hne
    exact ⟨G0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG0⟩⟩
  have hEx : ∃ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G),
      Finset.sup
        (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
        (fun G => G.copyCount T) = G.copyCount T :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)) hne'
      (fun G => G.copyCount T)
  obtain ⟨G, hGmem, hEq⟩ := hEx
  have hFree : H.Free G := (Finset.mem_filter.mp hGmem).2
  have hdef := generalizedExtremalNumber_eq_sup n T H
  exact ⟨G, hFree, hEq.symm.trans hdef.symm⟩

end SimpleGraph
