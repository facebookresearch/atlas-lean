/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

/-!
# Ordered directed-edge erasure

This module removes every occurrence of one ordered edge while retaining the
canonical vertex and neighbor orders of a directed-adjacency graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacency

universe u

variable {V : Type u} {graph : DirectedAdjacency V}
variable {length : Nat} {source target left right : V}

/-- **Erasing a directed edge.** Given a directed-adjacency graph $G$ and vertices $s$ and $t$,
erasing the edge $s \to t$ gives the directed-adjacency graph with the same vertex enumeration as
$G$ whose out-neighbour list at $s$ is the out-neighbour list of $s$ in $G$ with every occurrence
of $t$ removed (the remaining entries keep their order), and whose out-neighbour list at every
other vertex is the same as in $G$. -/
def eraseEdge [DecidableEq V] (graph : DirectedAdjacency V)
    (source target : V) : DirectedAdjacency V where
  vertices := graph.vertices
  vertices_nodup := graph.vertices_nodup
  vertices_complete := graph.vertices_complete
  adjacency vertex :=
    if vertex = source then
      (graph.adjacency vertex).filter fun neighbor => decide (neighbor ≠ target)
    else
      graph.adjacency vertex

/-- **Erasing an edge keeps the vertex enumeration.** For every directed-adjacency graph $G$ and
vertices $s$ and $t$, the graph obtained from $G$ by erasing the edge $s \to t$ has the same
vertex enumeration as $G$: the same list of vertices, in the same order. -/
@[simp]
theorem vertices_eraseEdge [DecidableEq V] :
    (eraseEdge graph source target).vertices = graph.vertices :=
  rfl

/-- **Out-neighbours of the source after erasing an edge.** For every directed-adjacency graph
$G$ and vertices $s$ and $t$, the out-neighbour list of $s$ in the graph obtained from $G$ by
erasing the edge $s \to t$ is the out-neighbour list of $s$ in $G$ with every occurrence of $t$
removed, the remaining entries kept in their original order. -/
@[simp]
theorem adjacency_eraseEdge_source [DecidableEq V] :
    (eraseEdge graph source target).adjacency source =
      (graph.adjacency source).filter (fun vertex => decide (vertex ≠ target)) := by
  simp [eraseEdge]

/-- **Erasing an edge leaves the other out-neighbour lists unchanged.** For every
directed-adjacency graph $G$ and vertices $s$, $t$ and $u$ with $u \ne s$, the out-neighbour
list of $u$ in the graph obtained from $G$ by erasing the edge $s \to t$ equals the
out-neighbour list of $u$ in $G$. -/
theorem adjacency_eraseEdge_of_ne [DecidableEq V]
    (different : left ≠ source) :
    (eraseEdge graph source target).adjacency left = graph.adjacency left := by
  simp [eraseEdge, different]

/-- **Edges after erasing an edge.** For every directed-adjacency graph $G$ and vertices $s$,
$t$, $u$ and $v$, there is an edge from $u$ to $v$ in the graph obtained from $G$ by erasing
the edge $s \to t$ if and only if there is an edge from $u$ to $v$ in $G$ and it is not the case
that both $u = s$ and $v = t$. -/
@[simp]
theorem edge_eraseEdge [DecidableEq V] :
    (eraseEdge graph source target).Edge left right ↔
      graph.Edge left right ∧ ¬(left = source ∧ right = target) := by
  by_cases selected : left = source
  · subst left
    simp [Edge, eraseEdge]
  · simp [Edge, eraseEdge, selected]

/-- **The erased edge is absent.** For every directed-adjacency graph $G$ and vertices $s$ and
$t$, the Boolean edge lookup for $s \to t$ in the graph obtained from $G$ by erasing the edge
$s \to t$ returns false. -/
@[simp]
theorem hasEdge_eraseEdge_self [DecidableEq V] :
    (eraseEdge graph source target).hasEdge source target = false := by
  simp [hasEdge, eraseEdge]

/-- **Erasing an edge twice gives the same out-neighbour lists.** For every directed-adjacency
graph $G$ and vertices $s$ and $t$, erasing the edge $s \to t$ from $G$ and then erasing it
again gives, at every vertex, the same out-neighbour list as erasing it once. -/
theorem eraseEdge_idempotent [DecidableEq V] :
    (eraseEdge (eraseEdge graph source target) source target).adjacency =
      (eraseEdge graph source target).adjacency := by
  funext vertex
  by_cases selected : vertex = source
  · subst vertex
    simp [eraseEdge, List.filter_filter]
  · simp [eraseEdge, selected]

/-- **Walks after erasing an edge are walks in the original graph.** For every
directed-adjacency graph $G$, vertices $s$, $t$, $u$ and $v$, and natural number $n$, if there
is a walk of length $n$ from $u$ to $v$ in the graph obtained from $G$ by erasing the edge
$s \to t$, then there is a walk of length $n$ from $u$ to $v$ in $G$. -/
theorem walk_eraseEdge_imp [DecidableEq V]
    (walk : Walk (eraseEdge graph source target) length left right) :
    Walk graph length left right :=
  Relation.RelatesInSteps.map id
    (fun a b edge =>
      (edge_eraseEdge (graph := graph) (source := source) (target := target)
        (left := a) (right := b)).mp edge |>.1)
    walk

/-- **Reachability after erasing an edge implies reachability in the original graph.** For
every directed-adjacency graph $G$ and vertices $s$, $t$, $u$ and $v$, if $v$ is reachable from
$u$ in the graph obtained from $G$ by erasing the edge $s \to t$, then $v$ is reachable from $u$
in $G$. -/
theorem reachable_eraseEdge_imp [DecidableEq V]
    (reachable : (eraseEdge graph source target).Reachable left right) :
    graph.Reachable left right := by
  obtain ⟨walkLength, walk⟩ := reachable_iff_exists_walk.mp reachable
  exact reachable_iff_exists_walk.mpr
    ⟨walkLength, walk_eraseEdge_imp (graph := graph) (source := source)
      (target := target) walk⟩

end Cslib.Algorithms.Lean.DirectedAdjacency
