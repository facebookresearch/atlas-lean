/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Obtuse angles among `2^d + 1` points (Erdős Problem 224)

Erdős Problem 224: if `A ⊆ ℝ^d` is any set of `2^d + 1` points, then some three points of `A`
determine an obtuse angle.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

@[expose] public section

namespace MathlibExt.Geometry.ObtuseAngleAmongPointsErdosProblem224Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #224, https://www.erdosproblems.com/224 (status PROVED
(LEAN)). UnsolvedMath record UM-30006776 (`EP-224`), dataset ulamai/UnsolvedMath v1.8.0.

An obtuse angle is `∠ y x z > π / 2` (`EuclideanGeometry.angle`) at a point `x` of `A` for two other
points `y, z` of `A`; collinear triples give the angle `π`. Compared with the formal-conjectures
statement `ErdosProblems/224.lean` (`⟪y - x, z - x⟫ < 0`, equivalent; no code imported).
-/

/-- Erdős Problem 224 (Danzer and Grünbaum): among any `2^d + 1` points of `ℝ^d` some three
distinct points `y, x, z` determine an obtuse angle `∠ y x z > π / 2`. -/
def obtuseAngleAmongTwoPowPlusOnePoints : Prop :=
  ∀ (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d))), A.card = 2 ^ d + 1 →
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Real.pi / 2 < EuclideanGeometry.angle y x z

/--
Resolved true: Danzer and Grünbaum proved that a set in `ℝ^d` in which all angles are at most `π /
2` has at most `2^d` points, so any `2^d + 1` points determine an obtuse angle;
erdosproblems.com/224 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#224, https://www.erdosproblems.com/224 (status PROVED (LEAN)); resolution: L. Danzer and B.
Grünbaum, Über zwei Probleme bezüglich konvexer Körper von P. Erdős und von V. L. Klee, Math. Z. 79
(1962), 95-99, a set in ℝ^d with no obtuse angle has at most 2^d points; erdosproblems.com/224:
proved by Danzer and Grünbaum, https://doi.org/10.1007/BF01193107.
-/
public theorem_wanted obtuseAngleAmongTwoPowPlusOnePoints_holds :
    obtuseAngleAmongTwoPowPlusOnePoints

end MathlibExt.Geometry.ObtuseAngleAmongPointsErdosProblem224Wanted
