/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Multiset.Basic

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- **Cycles in a graph.** A cycle in a simple graph $G$ consists of a base vertex $v$ of $G$
together with a closed walk $v = v_0, v_1, \dots, v_n = v$ in $G$ such that $n \ge 1$, the $n$
edges $v_{k-1} v_k$ of the walk are pairwise distinct, and the vertices $v_1, \dots, v_n$ are
pairwise distinct. In a simple graph this forces $n \ge 3$.

The base vertex and the direction of traversal are part of the data, so a single cycle subgraph
of $G$ arises from several such cycles. -/
structure Cycle (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

/-- **Edges of a cycle.** The edges of a cycle $c$ in a simple graph form the list of the edges of
its closed walk, in the order in which $c$ traverses them starting from its base vertex; each edge
is the unordered pair of its two endpoints. -/
def Cycle.edges {G : SimpleGraph V} (c : Cycle G) : List (Sym2 V) :=
  c.walk.edges

/-- **Length of a cycle.** The length of a cycle in a simple graph is the number of edges of its
closed walk. -/
def Cycle.length {G : SimpleGraph V} (c : Cycle G) : ℕ :=
  c.walk.length

/-- **Cycle covers.** Let $G$ be a finite simple graph. A finite multiset $C$ of cycles in $G$ is a
cycle cover of $G$ when every edge of $G$ is an edge of at least one cycle in $C$. -/
def IsCycleCover (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeFinset, ∃ c ∈ C, e ∈ c.edges

/-- **Total length of a multiset of cycles.** The total length of a finite multiset $C$ of cycles in
a simple graph is the sum of the lengths of the cycles in $C$, each counted with its multiplicity.
-/
def totalLength {G : SimpleGraph V} (C : Multiset (Cycle G)) : ℕ :=
  (C.map Cycle.length).sum

end SimpleGraph
