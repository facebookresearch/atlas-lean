/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Geodesic and CAT(0) metric spaces (Bestvina, Questions in Geometric Group Theory, Q 1.17, Q 2.18)

Shared definitions for the CAT(0) problems of Bestvina's list: a geodesic metric space, and a
CAT(0) space as a nonempty geodesic space satisfying the Berg–Nikolaev four-point condition
(`IsCAT0FourPoint`, MathlibExt), which characterizes CAT(0) among geodesic spaces. Both conditions
hold vacuously for the empty space, hence the nonemptiness requirement. Q 1.17 uses them for CAT(0)
groups, Q 2.18 for cocompact CAT(0) spaces.
-/

module

public import MathlibExt.Geometry.CAT0

@[expose] public section

namespace MathlibExt.Geometry.CATZeroSpaceShared

/-- `X` is a geodesic metric space: any two points are joined by an isometric copy of
`[0, dist x y]`. -/
def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ (dist x y) = y ∧
    ∀ s ∈ Set.Icc 0 (dist x y), ∀ t ∈ Set.Icc 0 (dist x y), dist (γ s) (γ t) = |s - t|

/-- `X` is a CAT(0) space: a nonempty geodesic space satisfying the Berg–Nikolaev four-point
condition (`IsCAT0FourPoint`), which characterizes CAT(0) among geodesic spaces. -/
def IsCATZero (X : Type*) [MetricSpace X] : Prop :=
  Nonempty X ∧ IsGeodesicSpace X ∧ IsCAT0FourPoint X

end MathlibExt.Geometry.CATZeroSpaceShared
