/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Growth of the number of ordinary lines (Erdős Problem 210)

Erdős Problem 210 (Erdős and de Bruijn): let `f(n)` be the least number of ordinary lines (lines
through exactly two of the points) determined by `n` points of `ℝ²` not all on a line. Does `f(n) →
∞`? How fast?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

namespace MathlibExt.Geometry.OrdinaryLinesGrowthErdosProblem210Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #210, https://www.erdosproblems.com/210 (status
PROVED). UnsolvedMath record UM-30006767 (`EP-210`), dataset ulamai/UnsolvedMath v1.8.0.

Ordinary lines are the lines `line[ℝ, p, q]` through two distinct points containing no third point
of the set. Both targets avoid `f` itself: `f(n) → ∞` is "for every `M`, all large non-collinear
sets have at least `M` ordinary lines", and the answer to "how fast" is the Green-Tao bound `f(n) ≥
n / 2` for all large `n`, which is attained for even `n`. Compared with the formal-conjectures
statement `ErdosProblems/210.lean` (`parts.i` and `variants.green_tao`, equivalent; no code
imported).
-/

/-- The ordinary lines of `s`: lines through two distinct points of `s` containing no other point
of `s`. -/
def ordinaryLines (s : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ L = line[ℝ, p, q] ∧ ∀ r ∈ s, r ∈ L → r = p ∨ r = q}

/-- Erdős Problem 210, first question: `f(n) → ∞`, where `f(n)` is the least number of ordinary
lines of `n` points in `ℝ²` not all on a line. -/
def ordinaryLinesTendToInfinity : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ s : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ s.card →
    ¬ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) → M ≤ (ordinaryLines s).ncard

/-- Erdős Problem 210, "how fast": `f(n) ≥ n / 2` for all large `n`. -/
def ordinaryLinesAtLeastHalf : Prop :=
  ∃ N : ℕ, ∀ s : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ s.card →
    ¬ Collinear ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) → s.card ≤ 2 * (ordinaryLines s).ncard

/--
Resolved true: Motzkin proved `f(n) → ∞`, and Kelly and Moser proved `f(n) ≥ 3n/7`;
erdosproblems.com/210 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#210, https://www.erdosproblems.com/210 (status PROVED); resolution: T. S. Motzkin, The lines and
planes connecting the points of a finite set, Trans. Amer. Math. Soc. 70 (1951), 451-464; B. Green
and T. Tao, On sets defining few ordinary lines, Discrete Comput. Geom. 50 (2013), 409-468, Motzkin:
f(n) → ∞; Green-Tao (Dirac-Motzkin conjecture for large n): n ≥ n₀ points not all on a line span at
least n/2 ordinary lines (erdosproblems.com/210), https://doi.org/10.1007/s00454-013-9518-9.
-/
public theorem_wanted ordinaryLinesTendToInfinity_holds : ordinaryLinesTendToInfinity

/--
Resolved true: Green and Tao proved that `n` points of `ℝ²` not all on a line, with `n` larger than
an absolute constant, determine at least `n / 2` ordinary lines (at least `3 ⌊n / 4⌋` for odd `n`);
`n / 2` is attained for even `n`. Source: T. F. Bloom, Erdős Problems, Problem #210,
https://www.erdosproblems.com/210 (status PROVED); resolution: T. S. Motzkin, The lines and planes
connecting the points of a finite set, Trans. Amer. Math. Soc. 70 (1951), 451-464; B. Green and T.
Tao, On sets defining few ordinary lines, Discrete Comput. Geom. 50 (2013), 409-468, Motzkin: f(n) →
∞; Green-Tao (Dirac-Motzkin conjecture for large n): n ≥ n₀ points not all on a line span at least
n/2 ordinary lines (erdosproblems.com/210), https://doi.org/10.1007/s00454-013-9518-9.
-/
public theorem_wanted ordinaryLinesAtLeastHalf_holds : ordinaryLinesAtLeastHalf

end MathlibExt.Geometry.OrdinaryLinesGrowthErdosProblem210Wanted
