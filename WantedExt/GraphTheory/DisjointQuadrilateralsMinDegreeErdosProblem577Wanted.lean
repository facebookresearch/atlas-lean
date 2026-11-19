/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vertex-disjoint quadrilaterals in dense graphs (Erdős Problem 577)

Erdős Problem 577 (Erdős and Faudree): if `G` is a graph with `4k` vertices and minimum degree at
least `2k` then `G` contains `k` vertex-disjoint `4`-cycles.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.GraphTheory.DisjointQuadrilateralsMinDegreeErdosProblem577Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #577, https://www.erdosproblems.com/577 (status
PROVED). UnsolvedMath record UM-30006936 (`EP-577`), dataset ulamai/UnsolvedMath v1.8.0.

The `k` cycles are an injective map `f : Fin k × Fin 4 → Fin (4k)` with `f (i, j)` adjacent to `f
(i, j + 1)` (indices mod `4`); injectivity makes each cycle a genuine `4`-cycle and the cycles
vertex-disjoint. The degree of `v` is `(G.neighborSet v).ncard`.
-/

/-- Erdős Problem 577 (Erdős and Faudree): every graph on `4k` vertices with minimum degree at
least `2k` contains `k` vertex-disjoint `4`-cycles. The `i`-th cycle is
`f (i, 0), f (i, 1), f (i, 2), f (i, 3)`, consecutive vertices (indices mod `4`) being adjacent;
injectivity of `f` makes the four vertices of each cycle distinct and the cycles disjoint. -/
def disjointQuadrilateralsMinDegree : Prop :=
  ∀ (k : ℕ) (G : SimpleGraph (Fin (4 * k))), (∀ v, 2 * k ≤ (G.neighborSet v).ncard) →
    ∃ f : Fin k × Fin 4 → Fin (4 * k), Function.Injective f ∧
      ∀ i : Fin k, ∀ j : Fin 4, G.Adj (f (i, j)) (f (i, j + 1))

/--
Resolved true: Wang proved the Erdős-Faudree conjecture that every graph on `4k` vertices with
minimum degree at least `2k` contains `k` vertex-disjoint quadrilaterals; erdosproblems.com/577
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #577,
https://www.erdosproblems.com/577 (status PROVED); resolution: H. Wang, Proof of the Erdős-Faudree
conjecture on quadrilaterals, Graphs Combin. (2010), 833-877, erdosproblems.com/577: a conjecture of
Erdős and Faudree, proved by Wang, https://www.erdosproblems.com/577.
-/
public theorem_wanted disjointQuadrilateralsMinDegree_holds : disjointQuadrilateralsMinDegree

end MathlibExt.GraphTheory.DisjointQuadrilateralsMinDegreeErdosProblem577Wanted
