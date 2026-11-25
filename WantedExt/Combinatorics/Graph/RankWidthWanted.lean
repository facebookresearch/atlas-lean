/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.RankWidthCliqueWidth
public import MathlibExt.Combinatorics.SimpleGraph.TreeDecomposition

/-!
# Rank-width: wanted theorems

Central theorems on rank-width whose proofs are deferred: the upper bound on rank-width in terms
of clique-width (Oum–Seymour), vertex-minor monotonicity, the bound of rank-width by tree-width, and
the excluded vertex-minor theorem.

## References

* S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100
  (author's revised preprint of 18 April 2005).
* S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory
  Ser. B 96 (2006) 514–528 (author's preprint of 20 October 2004).
* S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017)
  15–24, arXiv:1601.03800v2.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Rank-width is at most clique-width (Oum–Seymour).** If a finite graph has clique-width at
most `k`, it has rank-width at most `k`; this is the inequality `rw(G) ≤ cw(G)` of Oum and
Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006),
Proposition 6.3 (also Oum, arXiv:1601.03800v2, Theorem 2.1). -/
theorem_wanted HasCliqueWidthAtMost.hasRankWidthAtMost {G : SimpleGraph V} {k : ℕ}
    (h : G.HasCliqueWidthAtMost k) : G.HasRankWidthAtMost k

/-- **Rank-width does not increase under vertex-minors.** If `H` is a vertex-minor of the finite
graph `G` and `G` has rank-width at most `k`, then so does `H` (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Corollary 2.7, second statement: local
complementation preserves cut-rank and vertex deletion does not increase it). -/
theorem_wanted IsVertexMinor.hasRankWidthAtMost {W : Type*} [Fintype W] {H : SimpleGraph W}
    {G : SimpleGraph V} (h : H.IsVertexMinor G) {k : ℕ} (hG : G.HasRankWidthAtMost k) :
    H.HasRankWidthAtMost k

/-- **Rank-width is at most tree-width plus one.** A finite graph of tree-width at most `k` has
rank-width at most `k + 1` (Oum, *Rank-width: algorithmic and structural results*,
arXiv:1601.03800v2, Section 4.2, citing S. Oum, *Rank-width is less than or equal to
branch-width*, J. Graph Theory, 2008). The converse fails: complete graphs have rank-width at
most one (`SimpleGraph.cutRank_top_le_one`) but unbounded tree-width
(`SimpleGraph.hasTreewidthAtMost_top_iff`). -/
theorem_wanted HasTreewidthAtMost.hasRankWidthAtMost_succ {G : SimpleGraph V} {k : ℕ}
    (h : G.HasTreewidthAtMost k) : G.HasRankWidthAtMost (k + 1)

/-- **Excluded vertex-minors for bounded rank-width (Oum).** For `k ≥ 1`, a finite graph `G` has
rank-width at most `k` if and only if every vertex-minor of `G` with at most `(6 ^ (k + 1) - 1) / 5`
vertices has rank-width at most `k`. Equivalently, the class of graphs of rank-width at most `k`
is characterised by excluded vertex-minors with at most `(6 ^ (k + 1) - 1) / 5` vertices, so there
are finitely many excluded vertex-minors (Oum, *Rank-width and vertex-minors*, J. Combin. Theory
Ser. B 95 (2005), Theorem 5.4 and Corollary 5.5 in the author's revised preprint; Theorem 5.4
bounds the size of a graph of rank-width greater than `k` all of whose proper pivot-minors have
rank-width at most `k`). -/
theorem_wanted hasRankWidthAtMost_iff_forall_isVertexMinor (G : SimpleGraph V) {k : ℕ}
    (hk : 1 ≤ k) :
    G.HasRankWidthAtMost k ↔ ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      n ≤ (6 ^ (k + 1) - 1) / 5 → H.IsVertexMinor G → H.HasRankWidthAtMost k

end SimpleGraph
