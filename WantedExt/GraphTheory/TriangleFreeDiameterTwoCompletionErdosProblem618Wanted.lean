/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completing sparse triangle-free graphs to diameter two (Erdős Problem 618)

Erdős Problem 618 (Erdős, Gyárfás and Ruszinkó): for a triangle-free graph `G` let `h₂(G)` be the
smallest number of edges that need to be added to `G` so that it has diameter `2` and is still
triangle-free. Is it true that if `G` has maximum degree `o(n^{1/2})` then `h₂(G) = o(n²)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeDiameterTwoCompletionErdosProblem618Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #618, https://www.erdosproblems.com/618 (status PROVED
(LEAN)). UnsolvedMath record UM-30006954 (`EP-618`), dataset ulamai/UnsolvedMath v1.8.0.

Diameter `2` is read as diameter at most `2` (any two distinct vertices adjacent or with a common
neighbour). The `o(·)` statement is stated uniformly: for every `ε > 0` there is `δ > 0` such that
for all large `n` every triangle-free `G` on `n` vertices with maximum degree at most `δ √n` has
`h₂(G) ≤ ε n²`; this is equivalent to the statement for sequences of graphs with maximum degree
`o(√n)`, the form of the formal-conjectures statement `ErdosProblems/618.lean` (no code imported).
-/

/-- `h₂(G)`: the least number of edges whose addition to `G` gives a triangle-free graph of
diameter at most `2` (any two distinct vertices adjacent or with a common neighbour). For
triangle-free `G` a maximal triangle-free supergraph qualifies, so the set is nonempty. -/
noncomputable def diameterTwoCompletionCost {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧
    (∀ x y, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧ (H \ G).edgeSet.ncard = k}

open Classical in
/-- Erdős Problem 618 (Erdős, Gyárfás and Ruszinkó): if a triangle-free graph `G` on `n` vertices
has maximum degree `o(n^{1/2})` then `h₂(G) = o(n²)`; uniformly: for every `ε > 0` there is
`δ > 0` such that for all large `n`, maximum degree at most `δ √n` forces `h₂(G) ≤ ε n²`. -/
def diameterTwoCompletionSubquadratic : Prop :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree 3 → (G.maxDegree : ℝ) ≤ δ * Real.sqrt n →
      (diameterTwoCompletionCost G : ℝ) ≤ ε * n ^ 2

/--
Resolved true: Alon (Theorem 1.2) proved that a triangle-free graph on `n` vertices with maximum
degree at most `c √n` can be made triangle-free of diameter `2` by adding at most `2.5 c n²` edges,
for `n` large and `c` in a range containing every fixed `c ∈ (0, 1/2]`; take `c = min(ε / 2.5,
1/2)`. erdosproblems.com/618 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #618, https://www.erdosproblems.com/618 (status PROVED (LEAN)); resolution: N. Alon,
Triangle-free graphs of diameter 2, note (Princeton), Theorem 1.2: a triangle-free graph on n
vertices with maximum degree at most c √n becomes triangle-free of diameter 2 after adding at most
2.5 c n² edges, for n large and c = c(n) in a range containing every fixed c ∈ (0, 1/2];
erdosproblems.com/618: Alon's note solves the problem (essentially identical to Problem 134),
https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf.
-/
public theorem_wanted diameterTwoCompletionSubquadratic_holds : diameterTwoCompletionSubquadratic

end MathlibExt.GraphTheory.TriangleFreeDiameterTwoCompletionErdosProblem618Wanted
