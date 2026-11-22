/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unit squares in the complement of unit-distance-free sets (Erdős Problem 214)

Erdős Problem 214: let `S ⊆ ℝ²` have no two points at distance `1`. Must the complement of `S`
contain the four vertices of a unit square?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.UnitSquareInComplementErdosProblem214Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #214, https://www.erdosproblems.com/214 (status PROVED
(LEAN)). UnsolvedMath record UM-30006769 (`EP-214`), dataset ulamai/UnsolvedMath v1.8.0.

A unit square is given by vertices `a, b, c, d` with `b - a ⊥ d - a`, `|ab| = |ad| = 1` and `c = b +
(d - a)`, in any position and orientation. Compared with the formal-conjectures statement
`ErdosProblems/214.lean` (a congruent copy of the unit square, equivalent; no code imported).
-/

/-- Erdős Problem 214: if no two points of `S ⊆ ℝ²` are at distance `1`, then the complement of `S`
contains the four vertices `a, b, b + (d - a), d` of a unit square. -/
def unitDistanceAvoidingComplementHasUnitSquare : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin 2)), (∀ x ∈ S, ∀ y ∈ S, dist x y ≠ 1) →
    ∃ a b c d : EuclideanSpace ℝ (Fin 2), a ∉ S ∧ b ∉ S ∧ c ∉ S ∧ d ∉ S ∧
      inner ℝ (b - a) (d - a) = 0 ∧ dist a b = 1 ∧ dist a d = 1 ∧ c = b + (d - a)

/--
Resolved true: Juhász proved that the complement of a set with no two points at distance `1`
contains a congruent copy of every four-point configuration, in particular of the unit square;
erdosproblems.com/214 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#214, https://www.erdosproblems.com/214 (status PROVED (LEAN)); resolution: R. Juhász, Ramsey type
theorems in the plane, J. Combin. Theory Ser. A 27 (1979), 152-160, erdosproblems.com/214: proved by
Juhász, who showed that the complement contains a congruent copy of every four-point set,
https://doi.org/10.1016/0097-3165(79)90042-6.
-/
public theorem_wanted unitDistanceAvoidingComplementHasUnitSquare_holds :
    unitDistanceAvoidingComplementHasUnitSquare

end MathlibExt.Geometry.UnitSquareInComplementErdosProblem214Wanted
