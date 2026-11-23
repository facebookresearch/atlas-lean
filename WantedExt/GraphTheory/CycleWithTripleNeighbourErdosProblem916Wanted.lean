/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A cycle and a vertex adjacent to three of its vertices (Erdős Problem 916)

Erdős Problem 916: does every graph with `n` vertices and `2n - 2` edges contain a cycle and another
vertex adjacent to three vertices on the cycle?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MathlibExt.GraphTheory.CycleWithTripleNeighbourErdosProblem916Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #916, https://www.erdosproblems.com/916 (status
PROVED). UnsolvedMath record UM-30007087 (`EP-916`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs on `Fin n` with exactly `2n - 2` edges and `n ≥ 2`: for `n = 1` (and `n = 0`, where `2n - 2`
truncates to `0`) the edgeless graph has no cycle, so the question concerns `n ≥ 2` (it is vacuous
for `n = 2, 3`, where `2n - 2` edges do not fit). 'Another vertex adjacent to three vertices on the
cycle' is a vertex off the cycle adjacent to at least three distinct vertices of it.
formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 916: for `n ≥ 2`, every graph on `n` vertices with `2n - 2` edges contains a
cycle `C` and a vertex not on `C` that is adjacent to at least three vertices of `C`. -/
def cycleWithVertexAdjacentToThree : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = 2 * n - 2 →
    ∃ (u : Fin n) (C : G.Walk u u), C.IsCycle ∧ ∃ v ∉ C.support, ∃ S : Finset (Fin n),
      S.card = 3 ∧ ∀ w ∈ S, w ∈ C.support ∧ G.Adj v w

/--
Resolved true: Thomassen proved that every graph with `n` vertices and `2n - 2` edges contains a
cycle and a vertex off the cycle adjacent to three of its vertices, strengthening Dirac's theorem
that such graphs contain a subdivision of `K₄`; erdosproblems.com/916 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #916, https://www.erdosproblems.com/916 (status
PROVED); resolution: C. Thomassen, A minimal condition implying a special K₄-subdivision in a graph,
Arch. Math. (Basel) 25 (1974), 210-215, erdosproblems.com/916: a stronger form of Dirac's theorem
that such graphs contain a subdivision of K₄; 'the answer is yes, as proved by Thomassen',
https://www.erdosproblems.com/916.
-/
public theorem_wanted cycleWithVertexAdjacentToThree_holds : cycleWithVertexAdjacentToThree

end MathlibExt.GraphTheory.CycleWithTripleNeighbourErdosProblem916Wanted
