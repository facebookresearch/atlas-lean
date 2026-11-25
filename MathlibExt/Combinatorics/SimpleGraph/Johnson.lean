/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finset.Card

/-!
# Johnson graphs

Adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean`.
-/

@[expose] public section

namespace SimpleGraph

/-- **Johnson graph.** For natural numbers $n$ and $k$, the Johnson graph $J(n, k)$ has as
vertices the $k$-element subsets of $\{0, 1, \dots, n-1\}$, and two vertices $s$ and $t$ are
adjacent when $|s \cap t| + 1 = k$, that is, when $s$ and $t$ share exactly $k - 1$ elements. -/
public def johnsonGraph (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj s t := (s.val ∩ t.val).card + 1 = k
  symm.symm s t h := by simpa [Finset.inter_comm]
  loopless.irrefl := by simp +contextual

/-- **Adjacency in the Johnson graph.** For natural numbers $n$ and $k$ and $k$-element subsets
$s$ and $t$ of $\{0, 1, \dots, n-1\}$, the vertices $s$ and $t$ of the Johnson graph $J(n, k)$
are adjacent if and only if $|s \cap t| + 1 = k$. -/
public theorem johnsonGraph_adj_iff (n k : ℕ)
    (s t : {s : Finset (Fin n) // s.card = k}) :
    (johnsonGraph n k).Adj s t ↔ (s.val ∩ t.val).card + 1 = k :=
  Iff.rfl

end SimpleGraph
