/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CutRank
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Set.Card

/-!
# Rank-decompositions and rank-width

A rank-decomposition of a finite graph `G` is a tree whose internal nodes have degree three,
together with a bijection from the vertices of `G` to the leaves of the tree. Each tree edge
splits the leaves, hence the vertices of `G`, into two sides, and its width is the cut-rank of
either side. The rank-width of `G` is the least width of a rank-decomposition, and is `0` when
`G` has at most one vertex (Oum and Seymour 2006; Oum 2005).

We record "rank-width at most `k`" as the predicate `SimpleGraph.HasRankWidthAtMost`, which
avoids committing to a numerical convention, and prove that locally equivalent graphs satisfy it
for the same `k` (Oum 2005, Corollary 2.7, first statement).

## References

* S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100
  (author's revised preprint of 18 April 2005), Section 2.
* S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory
  Ser. B 96 (2006) 514–528 (author's preprint of 20 October 2004), Sections 2 and 6.
* S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017)
  15–24, arXiv:1601.03800v2, Section 2.1.
-/

@[expose] public section

namespace SimpleGraph

/-- **Rank-decomposition.** A rank-decomposition of a vertex type `V` is a finite tree `T` in which
every node is incident with exactly one or exactly three edges, together with a bijection `leaf`
from `V` onto the set of leaves (nodes of degree one) of `T` (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Section 2; Oum, arXiv:1601.03800v2,
Section 2.1). The decomposition does not depend on a graph; a graph enters only through the
width. -/
structure RankDecomposition (V : Type*) where
  /-- The nodes of the decomposition tree. -/
  ι : Type
  /-- The decomposition tree is finite. -/
  [fintype : Fintype ι]
  /-- The decomposition tree. -/
  T : SimpleGraph ι
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- Every node of `T` has degree one or three. -/
  degree_one_or_three : ∀ i, (T.neighborSet i).ncard = 1 ∨ (T.neighborSet i).ncard = 3
  /-- The leaf labelling vertices of `V`. -/
  leaf : V ↪ ι
  /-- The labelled nodes are exactly the leaves of `T`. -/
  range_leaf : Set.range leaf = {i | (T.neighborSet i).ncard = 1}

namespace RankDecomposition

variable {V : Type*} (D : RankDecomposition V)

/-- **Side of a tree edge.** For adjacent nodes `i, j` of the decomposition tree, the vertices of
`V` whose leaves lie in the component of `i` after deleting the edge `ij`; together with the side
of `j, i` this is the partition of `V` induced by the edge (Oum, arXiv:1601.03800v2,
Section 2.1). -/
def side (i j : D.ι) : Set V :=
  {x | (D.T.deleteEdges {s(i, j)}).Reachable i (D.leaf x)}

/-- **Width at most `k`.** A rank-decomposition has width at most `k` for a graph `G` if every
edge `ij` of the tree has width at most `k`, the width of `ij` being the cut-rank of the side of
`i` (Oum, arXiv:1601.03800v2, Section 2.1; by symmetry of cut-rank the choice of side does not
matter). -/
def HasWidthAtMost [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ i j, D.T.Adj i j → G.cutRank (D.side i j) ≤ k

/-- **Width bounds are monotone.** A decomposition of width at most `k` has width at most every
`l ≥ k`. -/
theorem HasWidthAtMost.mono [Fintype V] {G : SimpleGraph V} {k l : ℕ}
    (h : D.HasWidthAtMost G k) (hkl : k ≤ l) : D.HasWidthAtMost G l :=
  fun i j hij => (h i j hij).trans hkl

end RankDecomposition

variable {V : Type*} [Fintype V]

/-- **Rank-width at most `k`.** A finite graph `G` has rank-width at most `k` if it has at most one
vertex (the convention `rw(G) = 0` in that case) or it has a rank-decomposition of width at most
`k`. Thus `rw(G)` is the least `k` with `G.HasRankWidthAtMost k` (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Section 2; Oum and Seymour, J. Combin.
Theory Ser. B 96 (2006), Section 6; Oum, arXiv:1601.03800v2, Section 2.1). -/
def HasRankWidthAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  Fintype.card V ≤ 1 ∨ ∃ D : RankDecomposition V, D.HasWidthAtMost G k

/-- **Rank-width bounds are monotone.** -/
theorem HasRankWidthAtMost.mono {G : SimpleGraph V} {k l : ℕ} (h : G.HasRankWidthAtMost k)
    (hkl : k ≤ l) : G.HasRankWidthAtMost l :=
  h.imp id fun ⟨D, hD⟩ => ⟨D, RankDecomposition.HasWidthAtMost.mono D hD hkl⟩

/-- **Graphs with at most one vertex have rank-width zero.** -/
theorem hasRankWidthAtMost_of_card_le_one (G : SimpleGraph V) (hV : Fintype.card V ≤ 1)
    (k : ℕ) : G.HasRankWidthAtMost k :=
  Or.inl hV

/-- **Local complementation preserves rank-width.** For every finite graph `G`, vertex `v` and
`k`, `G * v` has rank-width at most `k` if and only if `G` does: every rank-decomposition has
the same width for both graphs, since their cut-rank functions agree (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Corollary 2.7, first statement, from
Proposition 2.6). -/
theorem hasRankWidthAtMost_localComplement_iff (G : SimpleGraph V) (v : V) (k : ℕ) :
    (G.localComplement v).HasRankWidthAtMost k ↔ G.HasRankWidthAtMost k := by
  simp only [HasRankWidthAtMost, RankDecomposition.HasWidthAtMost, cutRank_localComplement]

/-- **Locally equivalent graphs have the same rank-width.** If `H` is locally equivalent to `G`,
then `H` has rank-width at most `k` exactly when `G` does (Oum, *Rank-width and vertex-minors*,
J. Combin. Theory Ser. B 95 (2005), Corollary 2.7, first statement). -/
theorem LocallyEquivalent.hasRankWidthAtMost_iff {G H : SimpleGraph V}
    (h : G.LocallyEquivalent H) (k : ℕ) : H.HasRankWidthAtMost k ↔ G.HasRankWidthAtMost k := by
  simp only [HasRankWidthAtMost, RankDecomposition.HasWidthAtMost, h.cutRank_eq]

end SimpleGraph
