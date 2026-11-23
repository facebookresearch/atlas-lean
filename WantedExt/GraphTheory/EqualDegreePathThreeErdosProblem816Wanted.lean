/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal-degree endpoints of paths of length `3` (Erdős Problem 816)

Erdős Problem 816 (Erdős and Hajnal): let `G` be a graph with `2n + 1` vertices and `n² + n + 1`
edges. Must `G` contain two vertices of the same degree joined by a path of length `3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MathlibExt.GraphTheory.EqualDegreePathThreeErdosProblem816Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #816, https://www.erdosproblems.com/816 (status
PROVED). UnsolvedMath record UM-30007048 (`EP-816`), dataset ulamai/UnsolvedMath v1.8.0.

Stated in the range `n ≥ 600` proved by Chen and Ma, for at least `n² + n + 1` edges (their form).
The problem fixes no range: for `n = 1` the graph is a triangle with no path of length `3`, and `2 ≤
n < 600` is not covered by the resolution. A path of length `3` is a `Walk.IsPath` of length `3`.
The open-conjecture entry `EqualDegreeEndpointPathExtremal` concerns all odd path lengths. Compared
with the formal-conjectures statement `ErdosProblems/816.lean` (formal-conjectures states every `n ≥
2` with exactly `n² + n + 1` edges; no code imported).
-/

open Classical in
/-- `G` has two distinct vertices of equal degree joined by a path of length `3`. -/
def HasEqualDegreePathThree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3

/-- Erdős Problem 816 (Erdős and Hajnal), in the range `n ≥ 600` of the resolution: every graph on
`2n + 1` vertices with at least `n² + n + 1` edges has two vertices of equal degree joined by a path
of length `3`. -/
def equalDegreePathThree : Prop :=
  ∀ n : ℕ, 600 ≤ n → ∀ G : SimpleGraph (Fin (2 * n + 1)), n ^ 2 + n + 1 ≤ G.edgeSet.ncard →
    HasEqualDegreePathThree G

/--
Resolved true for `n ≥ 600`: Chen and Ma proved that every graph on `2n + 1` vertices with at least
`n² + n + 1` edges contains two vertices of equal degree joined by a path of length three (and with
`n² + n` edges every such graph except `K_{n, n+1}` does); erdosproblems.com/816 lists the problem
as proved. Source: T. F. Bloom, Erdős Problems, Problem #816, https://www.erdosproblems.com/816
(status PROVED); resolution: K. Chen and J. Ma, A problem of Erdős and Hajnal on paths with
equal-degree endpoints, arXiv:2503.19569 (2025), abstract: for all n ≥ 600, every (2n + 1)-vertex
graph with at least n² + n + 1 edges contains two vertices of equal degree connected by a path of
length three; K_{n,n+1} shows the edge bound is sharp, https://arxiv.org/abs/2503.19569.
-/
public theorem_wanted equalDegreePathThree_holds : equalDegreePathThree

end MathlibExt.GraphTheory.EqualDegreePathThreeErdosProblem816Wanted
