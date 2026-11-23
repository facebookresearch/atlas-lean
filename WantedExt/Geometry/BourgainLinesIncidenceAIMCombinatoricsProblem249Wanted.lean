/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bourgain's incidence problem for n² lines in R³ (AIM additive combinatorics, Problem 3.12)

AIM workshop Recent trends in additive combinatorics, Problem 3.12 (J. Bourgain): consider the
Szemerédi-Trotter theorem in `ℝ³` with `n²` lines, each containing `n` points from a given set `S`.
Assume no `n` lines are coplanar. Find a lower bound for `S` (e.g. `|S| ≥ n^{3 - ε}`).
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.LinesInEuclideanThreeSpaceShared

@[expose] public section

namespace MathlibExt.Geometry.BourgainLinesIncidenceAIMCombinatoricsProblem249Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.12 (J.
Bourgain). UnsolvedMath record UM-20001124 (`AIM-COMBINATORICS-0249`), dataset ulamai/UnsolvedMath
v1.8.0.

Lines and planes are affine subspaces of `ℝ³` with direction of dimension `1` and `2`; the `n²`
lines are distinct (a `Finset`) and `S` is finite. The hypothesis is Guth and Katz's 'no more than
`n` lines of `L` in any plane', weaker than the list's 'no `n` lines coplanar', so the statement
covers the list's setting.
-/

open MathlibExt.Geometry.LinesInEuclideanThreeSpaceShared

/-- An affine subspace of `ℝ³` is a plane when its direction has dimension `2`. -/
def IsPlane (P : AffineSubspace ℝ E3) : Prop :=
  Module.finrank ℝ P.direction = 2

/-- Bourgain's incidence question (AIM, Recent trends in additive combinatorics, Problem 3.12) with
the Guth-Katz answer: there is `c > 0` such that whenever `L` is a set of `n²` lines in `ℝ³`
(`IsLine` of the shared module) with at most `n` of them in any plane and `S` is a finite set of
points meeting every line of `L` in at least `n` points, `|S| ≥ c n³`. -/
def bourgainLinesIncidenceCubeBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (L : Finset (AffineSubspace ℝ E3)) (S : Finset E3),
    L.card = n ^ 2 → (∀ l ∈ L, IsLine l) →
    (∀ P : AffineSubspace ℝ E3, IsPlane P → {l | l ∈ L ∧ l ≤ P}.ncard ≤ n) →
    (∀ l ∈ L, n ≤ {x | x ∈ S ∧ x ∈ l}.ncard) →
    c * (n : ℝ) ^ 3 ≤ S.card

/--
Resolved true with the sharp bound `|S| ≫ n³`: Guth and Katz proved Bourgain's conjecture (their
Theorem 1.2, posed at AIM in 2004): if `L` is a set of `n²` lines in `ℝ³` with at most `n` lines of
`L` in any plane and every line of `L` contains at least `n` points of `S`, then `|S| = Ω(n³)`.
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.12 (J.
Bourgain); resolution: L. Guth and N. H. Katz, Algebraic methods in discrete analogs of the Kakeya
problem, Adv. Math. 225 (2010), 2828-2839, arXiv:0812.1043, Theorem 1.2 ('At AIM in 2004, Bourgain
conjectured the following'): L a set of N² lines in ℝ³, P a set of points, no more than N lines of L
in the same plane, each line of L containing at least N points of P; then |P| = Ω(N³),
https://doi.org/10.1016/j.aim.2010.05.015.
-/
public theorem_wanted bourgainLinesIncidenceCubeBound_holds : bourgainLinesIncidenceCubeBound

end MathlibExt.Geometry.BourgainLinesIncidenceAIMCombinatoricsProblem249Wanted
