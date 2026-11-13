/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two vertices joined by many disjoint paths (Erdős Problem 915)

Erdős Problem 915: let `G` be a graph with `1 + n(m - 1)` vertices and `1 + n · C(m, 2)` edges. Must
`G` contain two points which are connected by `m` disjoint paths?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Connectivity

@[expose] public section

namespace MathlibExt.GraphTheory.DisjointPathsEdgeCountErdosProblem915Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #915, https://www.erdosproblems.com/915 (status
SOLVED). UnsolvedMath record UM-30007086 (`EP-915`), dataset ulamai/UnsolvedMath v1.8.0.

erdosproblems.com notes that it is unclear whether disjoint means edge-disjoint or internally
vertex-disjoint; both readings are settled, in opposite directions, and each has its own target. The
graph has vertex set `Fin (1 + n (m - 1))` and exactly `1 + n · C(m, 2)` edges, with `m ≥ 2` (the
page's `k_m` and `ℓ_m` are defined for `m ≥ 2`) and `n ≥ 1`. The two points are distinct (for `u =
v` trivial paths would be disjoint), and in the vertex-disjoint reading the `m` paths form an
injective family (otherwise the one-edge path `uv` repeated `m` times would be internally disjoint);
internal disjointness is MathlibExt's `SimpleGraph.InternallyDisjoint`. Compared with the
formal-conjectures statement `ErdosProblems/915.lean` (`erdos_915.variants.edge_disjoint` and
`erdos_915`, equivalent; no code imported).
-/

/-- Erdős Problem 915, edge-disjoint reading: for `m ≥ 2` and `n ≥ 1`, every graph with
`1 + n (m - 1)` vertices and `1 + n · C(m, 2)` edges has two distinct vertices joined by `m`
paths, no two of which share an edge. -/
def edgeDisjointPathsFromEdgeCount : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ∀ G : SimpleGraph (Fin (1 + n * (m - 1))),
    G.edgeSet.ncard = 1 + n * m.choose 2 →
      ∃ u v, u ≠ v ∧ ∃ P : Fin m → G.Walk u v, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j => List.Disjoint (P i).edges (P j).edges

/-- Erdős Problem 915, internally vertex-disjoint reading: for `m ≥ 2` and `n ≥ 1`, every graph
with `1 + n (m - 1)` vertices and `1 + n · C(m, 2)` edges has two distinct vertices joined by `m`
distinct paths, no two of which share a vertex other than their endpoints
(`SimpleGraph.InternallyDisjoint`, MathlibExt). -/
def internallyDisjointPathsFromEdgeCount : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ∀ G : SimpleGraph (Fin (1 + n * (m - 1))),
    G.edgeSet.ncard = 1 + n * m.choose 2 →
      ∃ u v, u ≠ v ∧ ∃ P : Fin m → G.Walk u v, (∀ i, (P i).IsPath) ∧ Function.Injective P ∧
        Pairwise fun i j => SimpleGraph.InternallyDisjoint (P i) (P j)

/--
Resolved true (edge-disjoint reading): Mader proved that a graph on `N` vertices with more than
`(m/2)(N - 1) - (e_0 + ⋯ + e_{m-2})/2` edges, `e_r` the number of vertices of degree at most `r`,
has two vertices joined by `m` edge-disjoint paths; erdosproblems.com/915 records that this confirms
the conjecture (`ℓ_m(N) = ⌊m(N - 1)/2⌋ + 1`). Source: T. F. Bloom, Erdős Problems, Problem #915,
https://www.erdosproblems.com/915 (status SOLVED); resolution: W. Mader, Ein Extremalproblem des
Zusammenhangs von Graphen, Math. Z. (1973), 223-231; J. L. Leonard, On a conjecture of Bollobás and
Erdős, Period. Math. Hungar. (1973), 281-284, erdosproblems.com/915: Mader proved that a graph on n
vertices with more than (m/2)(n - 1) - (e_0(G)+⋯+e_{m-2}(G))/2 edges has two vertices joined by m
edge-disjoint paths, 'this confirms (and is stronger than) the conjecture'; Leonard disproved the
vertex-disjoint conjecture for m = 5 with an explicit counterexample with 57 vertices and 141 edges,
and Mader disproved it for all m ≥ 6, https://www.erdosproblems.com/915.
-/
public theorem_wanted edgeDisjointPathsFromEdgeCount_holds : edgeDisjointPathsFromEdgeCount

/--
Resolved false (internally vertex-disjoint reading): Leonard gave a graph with `57 = 1 + 14 · 4`
vertices and `141 = 1 + 14 · C(5, 2)` edges in which no two vertices are joined by `5` internally
disjoint paths (`m = 5`, `n = 14`), and Mader disproved the conjecture for every `m ≥ 6`. Source: T.
F. Bloom, Erdős Problems, Problem #915, https://www.erdosproblems.com/915 (status SOLVED);
resolution: W. Mader, Ein Extremalproblem des Zusammenhangs von Graphen, Math. Z. (1973), 223-231;
J. L. Leonard, On a conjecture of Bollobás and Erdős, Period. Math. Hungar. (1973), 281-284,
erdosproblems.com/915: Mader proved that a graph on n vertices with more than (m/2)(n - 1) -
(e_0(G)+⋯+e_{m-2}(G))/2 edges has two vertices joined by m edge-disjoint paths, 'this confirms (and
is stronger than) the conjecture'; Leonard disproved the vertex-disjoint conjecture for m = 5 with
an explicit counterexample with 57 vertices and 141 edges, and Mader disproved it for all m ≥ 6,
https://www.erdosproblems.com/915.
-/
public theorem_wanted internallyDisjointPathsFromEdgeCount_refuted :
    ¬ internallyDisjointPathsFromEdgeCount

end MathlibExt.GraphTheory.DisjointPathsEdgeCountErdosProblem915Wanted
