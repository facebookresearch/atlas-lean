/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edges on pentagons in graphs above the Turán threshold (Erdős Problem 608)

Erdős Problem 608: let `G` be a graph with `n` vertices and more than `n²/4` edges. Are there at
least `(2/9) n²` edges of `G` which are contained in a `C₅`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.PentagonEdgesAboveTuranErdosProblem608Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #608, https://www.erdosproblems.com/608 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006950 (`EP-608`), dataset ulamai/UnsolvedMath v1.8.0.

An edge is contained in a `C₅` when it is an edge of a closed walk of length `5` that is a cycle
(`Walk.IsCycle`). Graphs are on `Fin n`; `n²/4` and `(2/9) n²` are real numbers. The claim is
required only for all large `n` (weaker than for every `n`, so its refutation is stronger): for
small `n` it fails for a trivial reason (for `n = 3` the triangle has `3 > 9/4` edges and no `C₅`).
-/

open Classical in
/-- The number of edges of `G` that lie on some cycle of length `5`. -/
noncomputable def pentagonEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (G.edgeFinset.filter fun e =>
    ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧ w.length = 5 ∧ e ∈ w.edges).card

/-- Erdős Problem 608, for all large `n`: every graph with `n` vertices and more than `n²/4` edges
has at least `(2/9) n²` edges lying on a `5`-cycle. -/
def pentagonEdgesAboveTuran : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ 2 / 4 < G.edgeSet.ncard →
    (2 / 9 : ℝ) * n ^ 2 ≤ pentagonEdgeCount G

/--
Resolved false: Füredi and Maleki (unpublished; described by Grzesik, Hu and Volec) constructed
graphs with `n` vertices and more than `n²/4` edges in which at most `c n² + O(n)` edges lie on a
`C₅`, where `c = (2 + √2)/16 ≈ 0.2134 < 2/9`, so the bound fails for infinitely many `n`; Grzesik,
Hu and Volec proved that `c` is optimal; erdosproblems.com/608 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #608, https://www.erdosproblems.com/608 (status
DISPROVED (LEAN)); resolution: A. Grzesik, P. Hu and J. Volec, Minimum number of edges that occur in
odd cycles, J. Combin. Theory Ser. B (2019), 65-103, erdosproblems.com/608: Füredi and Maleki
constructed graphs with n vertices and more than n²/4 edges in which at most c n² + O(n) edges lie
on a C₅, c = (2 + √2)/16 ≈ 0.2134; abstract: Füredi and Maleki constructed a counterexample for k =
2 and proved an asymptotically matching lower bound; Grzesik, Hu and Volec prove that every n-vertex
graph with at least ⌊n²/4⌋ + 1 edges has at least (2 + √2) n² / 16 - O(n^{15/8}) edges that occur in
C₅, https://www.sciencedirect.com/science/article/pii/S0095895618301230.
-/
public theorem_wanted pentagonEdgesAboveTuran_refuted : ¬ pentagonEdgesAboveTuran

end MathlibExt.GraphTheory.PentagonEdgesAboveTuranErdosProblem608Wanted
