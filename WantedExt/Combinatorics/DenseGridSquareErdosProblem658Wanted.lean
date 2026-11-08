/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Squares in dense subsets of the grid (Erdős Problem 658)

Erdős Problem 658: let `δ > 0` and `N` be sufficiently large depending on `δ`. Is it true that if `A
⊆ {1, …, N}²` has `|A| ≥ δ N²` then `A` must contain the vertices of a square?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.DenseGridSquareErdosProblem658Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #658, https://www.erdosproblems.com/658 (status PROVED
(LEAN)). UnsolvedMath record UM-30006972 (`EP-658`), dataset ulamai/UnsolvedMath v1.8.0.

The square is axis-parallel, `(a, b), (a + d, b), (a, b + d), (a + d, b + d)` with `d ≥ 1` (Graham's
version); this implies the version allowing squares in any orientation, so it is the stronger
statement. It follows from the density Hales-Jewett theorem, which MathlibExt proves
(`density_hales_jewett`); the derivation is not formalized. Compared with the formal-conjectures
statement `ErdosProblems/658.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 658 (Graham), with axis-parallel squares: for every `δ > 0` and all large `N`,
every `A ⊆ {1, …, N}²` with `|A| ≥ δ N²` contains the four vertices
`(a, b), (a + d, b), (a, b + d), (a + d, b + d)` of a square with `d ≥ 1`. -/
def denseGridContainsSquare : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset (ℕ × ℕ),
    A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N → δ * (N : ℝ) ^ 2 ≤ A.card →
      ∃ a b d : ℕ, 0 < d ∧ (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

/--
Resolved true: the statement with axis-parallel squares follows from the density Hales-Jewett
theorem of Furstenberg and Katznelson, and Solymosi gave a quantitative proof; erdosproblems.com/658
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #658,
https://www.erdosproblems.com/658 (status PROVED (LEAN)); resolution: H. Furstenberg and Y.
Katznelson, A density version of the Hales-Jewett theorem, J. Anal. Math. (1991), 64-119,
erdosproblems.com/658: the qualitative statement follows from the density Hales-Jewett theorem; a
quantitative proof was given by Solymosi (Combin. Probab. Comput. 2004),
https://www.erdosproblems.com/658.
-/
public theorem_wanted denseGridContainsSquare_holds : denseGridContainsSquare

end MathlibExt.Combinatorics.DenseGridSquareErdosProblem658Wanted
