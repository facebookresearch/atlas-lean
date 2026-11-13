/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lines determined by points with few on a line (Erdős Problem 211)

Erdős Problem 211: let `1 ≤ k < n`. Given `n` points in `ℝ²` with at most `n - k` on any line, are
there `≫ k n` lines containing at least two of the points?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.ConnectingLinesLowerBoundErdosProblem211Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #211, https://www.erdosproblems.com/211 (status
PROVED). UnsolvedMath record UM-30006768 (`EP-211`), dataset ulamai/UnsolvedMath v1.8.0.

Lines are affine subspaces with one-dimensional direction; the determined lines are `line[ℝ, p, q]`
for distinct points `p, q`. `≫ k n` is an absolute constant `c > 0`, uniform in `k` and `n`.
Compared with the formal-conjectures statement `ErdosProblems/211.lean` (`MainBound`, equivalent; no
code imported).
-/

/-- The lines through at least two points of `s`. -/
def connectingLines (s : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ L = line[ℝ, p, q]}

/-- Erdős Problem 211: there is `c > 0` such that for all `1 ≤ k < n`, every set of `n` points in
`ℝ²` with at most `n - k` on any line determines at least `c k n` lines. -/
def connectingLinesAtLeastLinearInKN : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n k : ℕ) (s : Finset (EuclideanSpace ℝ (Fin 2))), 1 ≤ k → k < n →
    s.card = n →
    (∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)), Module.finrank ℝ L.direction = 1 →
      ((s : Set (EuclideanSpace ℝ (Fin 2))) ∩ L).ncard ≤ n - k) →
    c * k * n ≤ (connectingLines s).ncard

/--
Resolved true: Beck, and independently Szemerédi and Trotter, proved that `n` points of `ℝ²` with at
most `n - k` on a line determine at least `c k n` lines for an absolute `c > 0`;
erdosproblems.com/211 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#211, https://www.erdosproblems.com/211 (status PROVED); resolution: J. Beck, On the lattice
property of the plane and some problems of Dirac, Motzkin and Erdős in combinatorial geometry,
Combinatorica 3 (1983), 281-297; E. Szemerédi and W. T. Trotter, Extremal problems in discrete
geometry, Combinatorica 3 (1983), 381-392, Beck's theorem: n points with at most n - k on a line
determine at least c k n lines; erdosproblems.com/211: solved by Beck and by Szemerédi-Trotter,
https://doi.org/10.1007/BF02579184.
-/
public theorem_wanted connectingLinesAtLeastLinearInKN_holds : connectingLinesAtLeastLinearInKN

end MathlibExt.Geometry.ConnectingLinesLowerBoundErdosProblem211Wanted
