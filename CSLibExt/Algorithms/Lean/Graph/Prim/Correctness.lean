/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Prim.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Basic.Real.Basic

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import all CSLibExt.Algorithms.Lean.Graph.Prim.QueueInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.ParentInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.CutInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.Tree
import all CSLibExt.Algorithms.Lean.Graph.Prim.Exchange

/-!
# Prim parent edges and signed-real minimum spanning tree

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_safeCuts_history {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → ℝ)
    (parents : Vector (Option (Fin n)) n) (ids : List (Fin n))
    (hs : parentSafeCuts graph weight parents ids) : parentHistory parents ids := by
  intro v p hv hp
  obtain ⟨before, after, hsplit, hpmem, _⟩ := hs v p hv hp
  exact ⟨before, after, hsplit, hpmem⟩

private lemma parent_graph_on_respects_safeCuts {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → ℝ)
    (parents : Vector (Option (Fin n)) n) (ids : List (Fin n))
    (hn : ids.Nodup) (hs : parentSafeCuts graph weight parents ids) :
    SimpleGraph.RespectsCut (parentGraphOn parents ids) {v | v ∈ ids} := by
  intro u v h
  exact parent_graph_on_respects_suffix parents ids hn
    (parent_safeCuts_history graph weight parents ids hs) [] ids (by simp) u v h

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_cut_completion {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → ℝ)
    (parents : Vector (Option (Fin n)) n) (G : SimpleGraph (Fin n))
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (hsub : (SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u)) ≤ G)
    (ids : List (Fin n)) (hn : ids.Nodup)
    (hs : parentSafeCuts graph weight parents ids)
    (T : SimpleGraph (Fin n)) (hTG : T ≤ G) (hT : T.IsTree) :
    ∃ T' : SimpleGraph (Fin n), T' ≤ G ∧ T'.IsTree ∧
      parentGraphOn parents ids ≤ T' ∧
      SimpleGraph.totalEdgeWeight weight T' ≤ SimpleGraph.totalEdgeWeight weight T := by
  classical
  induction ids generalizing T with
  | nil =>
    have hbot : parentGraphOn parents [] = ⊥ := by
      ext u v
      simp [parentGraphOn, SimpleGraph.fromRel_adj]
    exact ⟨T, hTG, hT, by rw [hbot]; exact bot_le, le_rfl⟩
  | cons v tail ih =>
    have hnt : tail.Nodup := (List.nodup_cons.mp hn).2
    have hst := parent_safeCuts_tail graph weight parents v tail hn hs
    obtain ⟨T₁, hT₁G, hT₁, hcontain, hcost⟩ := ih hnt hst T hTG hT
    cases hp : parents[v] with
    | none =>
      exact ⟨T₁, hT₁G, hT₁, by
        rw [parent_graph_on_cons_none parents v tail hp]
        exact hcontain, hcost⟩
    | some p =>
      obtain ⟨hpmem, hminimum⟩ := parent_safeCuts_head graph weight parents v p tail hn hs hp
      have hvnot : v ∉ tail := (List.nodup_cons.mp hn).1
      have hpv : p ≠ v := by
        intro he
        exact hvnot (he ▸ hpmem)
      have hgv : G.Adj p v := hsub
        ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hpv, Or.inl hp⟩)
      have hlight : SimpleGraph.IsLightEdge G weight {w | w ∈ tail} p v := by
        refine ⟨hpmem, hvnot, hgv, ?_⟩
        intro a b hab ha hb
        exact hminimum a ha b hb ((hadj a b).mpr hab)
      have hrespect := parent_graph_on_respects_safeCuts graph weight parents tail hnt hst
      obtain ⟨T₂, hT₂G, hT₂, hcontain₂, hcost₂⟩ := SimpleGraph.respectedCut_exchange
        G T₁ (parentGraphOn parents tail) weight {w | w ∈ tail} p v
        hT₁G hT₁ hcontain hrespect hlight
      exact ⟨T₂, hT₂G, hT₂, by
        rw [parent_graph_on_cons_some parents v p tail hp]
        exact hcontain₂, hcost₂.trans hcost⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_graph_on_full {n : Nat}
    (parents : Vector (Option (Fin n)) n) (ids : List (Fin n))
    (hfull : ∀ v : Fin n, v ∈ ids) :
    parentGraphOn parents ids = SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u) := by
  ext u v
  simp only [parentGraphOn, SimpleGraph.fromRel_adj, hfull, true_and]

private lemma tree_eq_of_le {n : Nat} (A T : SimpleGraph (Fin n))
    (hA : A.IsTree) (hT : T.IsTree) (hAT : A ≤ T) : A = T := by
  classical
  have hc : A.edgeFinset.card = T.edgeFinset.card := Nat.add_right_cancel
    (hA.card_edgeFinset.trans hT.card_edgeFinset.symm)
  exact SimpleGraph.edgeFinset_inj.mp
    (Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hAT) hc.ge)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma prim_parent_minimum {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → ℝ)
    (root : Fin n) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (T : SimpleGraph (Fin n)) (hTG : T ≤ G) (hT : T.IsTree) :
    SimpleGraph.totalEdgeWeight weight
      (SimpleGraph.fromRel (fun u v : Fin n => (worker graph weight root).ret.parent[v] = some u)) ≤
        SimpleGraph.totalEdgeWeight weight T := by
  have hrun := prim_extracted_once graph weight root
  obtain ⟨T', hT'G, hT', hcontain, hcost⟩ := parent_cut_completion graph weight
    (worker graph weight root).ret.parent G hadj (prim_parent_graph_le graph weight root G hadj)
    ((worker graph weight root).ret.extracted.map Prod.snd) hrun.1
    (prim_parent_safeCuts graph weight root) T hTG hT
  rw [parent_graph_on_full _ _ hrun.2] at hcontain
  have heq := tree_eq_of_le _ _
    (prim_parent_graph_isTree graph weight root G hG hadj) hT' hcontain
  rw [heq]
  exact hcost

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma total_edge_weight_sum_any {n : Nat}
    (weight : Sym2 (Fin n) → ℝ) (G : SimpleGraph (Fin n)) [Fintype G.edgeSet] :
    (∑ e ∈ G.edgeFinset, weight e) = SimpleGraph.totalEdgeWeight weight G := by
  classical
  rw [SimpleGraph.totalEdgeWeight_eq_edgeFinset_sum]
  apply Finset.sum_congr
  · ext e
    simp
  · intro e he
    rfl

universe u

/-- **The root has no parent in Prim's algorithm.** Let $W$ be a linearly ordered type with a
zero element, let $D$ be a directed adjacency structure on the vertices $0, \dots, n-1$, let $w$
assign a weight in $W$ to every unordered pair of vertices, not necessarily distinct, and let
$r$ be a vertex. In the output of Prim's algorithm on $D$, $w$ and $r$, the vertex $r$ has no
parent. -/
public theorem prim_root {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (prim graph weight root).ret[root] = none :=
  Cslib.Algorithms.Lean.Prim.prim_root_parent graph weight root

/-- **Parents returned by Prim's algorithm are adjacency-list neighbors.** Let $W$ be a linearly
ordered type with a zero element, let $D$ be a directed adjacency structure on the vertices
$0, \dots, n-1$ with adjacency lists $A(u)$, let $w$ assign a weight in $W$ to every unordered
pair of vertices, not necessarily distinct, and let $r$ be a vertex. For all vertices $u$ and
$v$, if Prim's algorithm on $D$, $w$ and $r$ returns $u$ as the parent of $v$, then $v$ occurs
in $A(u)$. -/
public theorem prim_parent_edge {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ∀ u v : Fin n, (prim graph weight root).ret[v] = some u →
      v ∈ graph.adjacency u := by
  intro u v hp
  exact Cslib.Algorithms.Lean.Prim.prim_parent_edges graph weight root v u hp

/-- **Prim's algorithm returns a tree.** Let $W$ be a linearly ordered type with a zero element,
let $G$ be a connected simple graph on the vertices $0, \dots, n-1$, let $D$ be a directed
adjacency structure on the same vertices with adjacency lists $A(u)$ such that for all vertices
$u$ and $v$, $v$ occurs in $A(u)$ exactly when $u$ and $v$ are adjacent in $G$, let $w$ assign
a weight in $W$ to every unordered pair of vertices, not necessarily distinct, and let $r$ be a
vertex. Let $T$ be the simple graph on the vertices $0, \dots, n-1$ in which two distinct
vertices are adjacent when one of them is the parent of the other in the output of Prim's
algorithm on $D$, $w$ and $r$. Then $T$ is a tree. -/
public theorem prim_isTree {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) (hG : G.Connected) :
    (SimpleGraph.fromRel fun u v : Fin n => (prim graph weight root).ret[v] = some u).IsTree :=
  Cslib.Algorithms.Lean.Prim.prim_parent_graph_isTree graph weight root G hG hadj

/-- **Prim's algorithm returns a minimum spanning tree.** Let $G$ be a connected simple graph on
the vertices $0, \dots, n-1$, let $D$ be a directed adjacency structure on the same vertices with
adjacency lists $A(u)$ such that for all vertices $u$ and $v$, $v$ occurs in $A(u)$ exactly when
$u$ and $v$ are adjacent in $G$, let $w$ assign a real weight $w(e)$ to every unordered pair $e$
of vertices, not necessarily distinct, and let $r$ be a vertex. Let $T$ be the simple graph on
the vertices $0, \dots, n-1$ in which two distinct vertices are adjacent when one of them is the
parent of the other in the output of Prim's algorithm on $D$, $w$ and $r$, and write $E(H)$ for
the edge set of a graph $H$. Then every edge of $T$ is an edge of $G$, $T$ is a tree, and every
graph $H$ on the vertices $0, \dots, n-1$ that is a tree and whose edges are all edges of $G$
satisfies $\sum_{e \in E(T)} w(e) \le \sum_{e \in E(H)} w(e)$.

Weights are arbitrary signed real numbers, and ties are allowed. -/
public theorem prim_minimum_spanningTree {n : Nat} (graph : DirectedAdjacency (Fin n))
    (G : SimpleGraph (Fin n))
    (weight : Sym2 (Fin n) → ℝ) (root : Fin n) : by
    classical
    exact (∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) → G.Connected →
      let parents := (prim graph weight root).ret
      let T := SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u)
      T ≤ G ∧ T.IsTree ∧ ∀ H : SimpleGraph (Fin n), H ≤ G → H.IsTree →
        (∑ e ∈ T.edgeFinset, weight e) ≤ ∑ e ∈ H.edgeFinset, weight e := by
  classical
  intro hadj hG
  dsimp only
  refine ⟨Cslib.Algorithms.Lean.Prim.prim_parent_graph_le graph weight root G hadj,
    Cslib.Algorithms.Lean.Prim.prim_parent_graph_isTree graph weight root G hG hadj, ?_⟩
  intro H hHG hH
  rw [Cslib.Algorithms.Lean.Prim.total_edge_weight_sum_any,
    Cslib.Algorithms.Lean.Prim.total_edge_weight_sum_any]
  exact Cslib.Algorithms.Lean.Prim.prim_parent_minimum graph weight root G hG hadj H hHG hH

end Cslib.Algorithms.Lean.Prim
