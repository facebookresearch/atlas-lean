/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Near-integer distance configurations (Erdős Problems 465 and 466)

Shared definition for the `N(X, δ)` problems: the finite planar configurations in a closed disc of
radius `X` whose pairwise distances are all at distance at least `δ` from the nearest integer
(`MetaMathlibExt.distToNearestInt`). Erdős Problem 465 bounds their size from above, Erdős Problem
466 from below.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.NumberTheory.DiophantineApproximation.DistToNearestInt

@[expose] public section

namespace MathlibExt.NumberTheory.NearIntegerDistancePointsShared

open MetaMathlibExt (distToNearestInt)

/-- The finite set `P` of points of the plane lies in some closed disc of radius `X`, and the
distance between any two distinct points of `P` is at distance at least `δ` from the nearest
integer. -/
def IsNearIntegerAvoiding (X δ : ℝ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∃ c : EuclideanSpace ℝ (Fin 2), ∀ p ∈ P, dist p c ≤ X) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ distToNearestInt (dist p q)

end MathlibExt.NumberTheory.NearIntegerDistancePointsShared
