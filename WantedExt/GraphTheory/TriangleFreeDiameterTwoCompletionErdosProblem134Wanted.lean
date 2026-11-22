/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completing sparse triangle-free graphs to diameter two (Erdős Problem 134)

Erdős Problem 134: let `ε, δ > 0` and `n` be large in terms of `ε` and `δ`. Can every triangle-free
graph on `n` vertices with maximum degree `< n^{1/2 - ε}` be made into a triangle-free graph of
diameter `2` by adding at most `δ n²` edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeDiameterTwoCompletionErdosProblem134Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #134, https://www.erdosproblems.com/134 (status PROVED
(LEAN)). UnsolvedMath record UM-30006735 (`EP-134`), dataset ulamai/UnsolvedMath v1.8.0.

Diameter `2` is written as: distinct vertices are adjacent or have a common neighbour (for
triangle-free graphs on `n ≥ 3` vertices this is diameter exactly `2`). Compared with the
formal-conjectures statement `ErdosProblems/134.lean` (equivalent; no code imported).
-/

open Filter

/-- Erdős Problem 134: for all `ε, δ > 0` and all large `n`, every triangle-free graph `G` on `n`
vertices with maximum degree `< n^{1/2 - ε}` extends, by adding at most `δ n²` edges, to a
triangle-free graph in which any two distinct vertices are adjacent or have a common neighbour
(diameter at most `2`). -/
def triangleFreeDiameterTwoCompletion : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    (∀ v, ((G.neighborSet v).ncard : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
      ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧
        (∀ x y, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        ((H.edgeSet \ G.edgeSet).ncard : ℝ) ≤ δ * (n : ℝ) ^ 2

/--
Resolved true: Alon proved (Theorem 1.2, abstract: any `0 < ε < 1/6`) that a triangle-free graph on
`n` vertices with maximum degree `< n^{1/2 - ε}` can be made triangle-free of diameter `2` by adding
fewer than `3 n^{2 - ε}` edges, which is at most `δ n²` for large `n`; for `ε ≥ 1/6` apply it with a
smaller exponent. erdosproblems.com/134 lists the problem as proved, and plby/lean-proofs has a
formal proof of formal-conjectures' `erdos_134`. Source: T. F. Bloom, Erdős Problems, Problem #134,
https://www.erdosproblems.com/134 (status PROVED (LEAN)); resolution: N. Alon, note on Erdős Problem
134, https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf, Theorem 1.2: a triangle-free graph
on n vertices with maximum degree at most c(n) √n, for c(n) in a range that contains n^{-ε} for
every 0 < ε < 1/6 and n large, becomes triangle-free of diameter 2 after adding at most 2.5 c(n) n²
edges (abstract: fewer than 3 n^{2-ε} edges); erdosproblems.com/134,
https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf.
-/
public theorem_wanted triangleFreeDiameterTwoCompletion_holds : triangleFreeDiameterTwoCompletion

end MathlibExt.GraphTheory.TriangleFreeDiameterTwoCompletionErdosProblem134Wanted
