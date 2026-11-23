/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A vertex with a dense neighbourhood above the Turán number (Erdős Problem 1079)

Erdős Problem 1079: let `r ≥ 4`. If `G` is a graph on `n` vertices with at least `ex(n; K_r)` edges,
must `G` contain a vertex with degree `d ≫_r n` whose neighbourhood contains at least `ex(d;
K_{r-1})` edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.DenseNeighbourhoodTuranErdosProblem1079Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1079, https://www.erdosproblems.com/1079 (status
SOLVED). UnsolvedMath record UM-30007156 (`EP-1079`), dataset ulamai/UnsolvedMath v1.8.0.

`ex` is Mathlib's `SimpleGraph.extremalNumber`; the neighbourhood's edges are those of the induced
subgraph on `G.neighborSet v`. `n ≥ 2` excludes the one-vertex graph, whose only degree is `0`.
Compared with the formal-conjectures statement `ErdosProblems/1079.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 1079: for `r ≥ 4` there is `c_r > 0` such that every graph on `n ≥ 2` vertices
with at least `ex(n; K_r)` edges has a vertex `v` of degree `d ≥ c_r n` whose neighbourhood spans at
least `ex(d; K_{r-1})` edges. -/
def denseNeighbourhoodTuran : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
    SimpleGraph.extremalNumber n (SimpleGraph.completeGraph (Fin r)) ≤ G.edgeSet.ncard →
    ∃ v : Fin n, c * n ≤ (G.neighborSet v).ncard ∧
      SimpleGraph.extremalNumber (G.neighborSet v).ncard (SimpleGraph.completeGraph (Fin (r - 1)))
        ≤ (G.induce (G.neighborSet v)).edgeSet.ncard

/--
Resolved true: erdosproblems.com/1079 records the proof of Bollobás and Thomason. Bondy showed that
with more than `ex(n; K_r)` edges every vertex of maximum degree `m` has more than `ex(m; K_{r-1})`
edges in its neighbourhood; with exactly `ex(n; K_r)` edges the same vertex has at least that many,
since `ex(n; K_r) ≥ ex(m; K_{r-1}) + m (n - m)`. Here `m ≥ 2 ex(n; K_r) / n ≥ n / 3` for `r ≥ 4`.
erdosproblems.com/1079 lists the problem as solved. Source: T. F. Bloom, Erdős Problems, Problem
#1079, https://www.erdosproblems.com/1079 (status SOLVED); resolution: B. Bollobás and A. Thomason,
Dense neighbourhoods and Turán's theorem, J. Combin. Theory Ser. B (1981), 111-114; J. A. Bondy,
Large dense neighbourhoods and Turán's theorem, J. Combin. Theory Ser. B (1983), 109-111, true
(unless G is the Turán graph, for the strict form); Bondy: with more than ex(n; K_r) edges every
vertex of maximum degree m has more than ex(m; K_{r-1}) edges in its neighbourhood
(erdosproblems.com/1079), https://doi.org/10.1016/0095-8956(83)90012-6.
-/
public theorem_wanted denseNeighbourhoodTuran_holds : denseNeighbourhoodTuran

end MathlibExt.GraphTheory.DenseNeighbourhoodTuranErdosProblem1079Wanted
