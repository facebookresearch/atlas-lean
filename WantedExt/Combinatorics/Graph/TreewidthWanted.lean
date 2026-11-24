/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Graph.GraphMinor
public import MathlibExt.Combinatorics.SimpleGraph.Bramble
public import MathlibExt.Combinatorics.SimpleGraph.TreeDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Tree-width: wanted theorems

Central theorems on tree-width whose proofs are deferred: minor-monotonicity, the tree-width
duality theorem of Seymour and Thomas, the grid theorem of Robertson and Seymour, and the
well-quasi-ordering of graphs of bounded tree-width (the bounded case of the graph minor theorem
`MetaMathlibExt.graph_minor_theorem`). Graph minors are
`MetaMathlibExt.IsMinor` on bundled finite graphs; tree-width is
`SimpleGraph.HasTreewidthAtMost`.

## References

* R. Diestel, *Graph Theory*, 6th edition, Chapter 12 (author's online preview of Chapter 12,
  PDF dated 28 June 2024, https://diestel-graph-theory.com/), Sections 12.4 and 12.6.
-/

@[expose] public section

namespace MetaMathlibExt

open SimpleGraph

/-- **Tree-width does not increase under taking minors.** If `H` is a minor of the finite graph
`G` and `G` has tree-width at most `k`, then so does `H` (Diestel, *Graph Theory*, 6th ed.,
Lemma 12.4.1, from Lemmas 12.3.2 and 12.3.3). -/
theorem_wanted IsMinor.hasTreewidthAtMost {H G : FinGraph} (h : IsMinor H G) {k : ℕ}
    (hG : G.G.HasTreewidthAtMost k) : H.G.HasTreewidthAtMost k

/-- **Tree-width duality theorem (Seymour–Thomas).** For every finite graph `G` and every
`k : ℕ`, `G` has tree-width at most `k` if and only if it contains no bramble of order greater
than `k + 1` (Diestel, *Graph Theory*, 6th ed., Theorem 12.4.3, "a graph has tree-width `< k` if
and only if it contains no bramble of order `> k`", applied with `k + 1`; P. D. Seymour and
R. Thomas, *Graph searching and a min-max theorem for tree-width*, J. Combin. Theory Ser. B 58
(1993) 22–33). The source's case `k = 0`, which concerns only the graph with no vertices, is not
part of this statement. -/
theorem_wanted hasTreewidthAtMost_iff_forall_bramble {V : Type*} [Finite V] (G : SimpleGraph V)
    (k : ℕ) :
    G.HasTreewidthAtMost k ↔ ∀ (B : Set (Set V)) (hB : G.IsBramble B), ¬hB.OrderGT (k + 1)

/-- **Grid theorem (Robertson–Seymour).** For every integer `r` there is an integer `k` such that
every finite graph of tree-width greater than `k` has the `r × r` grid as a minor; the grid is the
box product of two paths on `r` vertices, with vertex set `Fin r × Fin r` and edges between
pairs at distance one in one coordinate (Diestel, *Graph Theory*, 6th ed., Theorem 12.6.3, stated
there for tree-width at least `k`; N. Robertson and P. D. Seymour, *Graph minors. V. Excluding a
planar graph*, J. Combin. Theory Ser. B (1986)). -/
theorem_wanted exists_grid_minor_of_not_hasTreewidthAtMost (r : ℕ) :
    ∃ k : ℕ, ∀ G : FinGraph.{0}, ¬G.G.HasTreewidthAtMost k →
      IsMinor ⟨Fin r × Fin r, pathGraph r □ pathGraph r⟩ G

/-- **Graphs of bounded tree-width are well-quasi-ordered by minors (Robertson–Seymour).** For
every `k : ℕ`, every infinite sequence of finite graphs of tree-width at most `k` has two terms
`G i, G j` with `i < j` such that `G i` is a minor of `G j` (Diestel, *Graph Theory*, 6th ed.,
Theorem 12.4.2, stated there for tree-width `< k` with `k > 0`). -/
theorem_wanted exists_isMinor_of_hasTreewidthAtMost (k : ℕ) (G : ℕ → FinGraph.{0})
    (hG : ∀ n, (G n).G.HasTreewidthAtMost k) : ∃ i j, i < j ∧ IsMinor (G i) (G j)

end MetaMathlibExt
