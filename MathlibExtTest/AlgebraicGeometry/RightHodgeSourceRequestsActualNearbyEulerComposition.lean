/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualNearbyEulerComposition

/-!
# Corollaries of the nearby Euler composition

Unpacking the nearby Euler composition gives the underlying sheaf-map identity:
`can ≫ var` equals the graded Euler map at index `0`.
-/

namespace MathlibExtTest.AlgebraicGeometry.RightHodgeSourceRequestsActualNearbyEulerComposition

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels

variable (k : Type) [CommRing k] [Algebra ℚ k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  (C : CoordinateDerivation k M O) (N : RightModule k M O)
  (V : RationalVFiltration k M O C N)

/-- The nearby Euler composition as an identity of underlying sheaf maps. -/
example (A : GradedVOperators k M O C N V) :
    (nearbyNilpotent k M O C N V A).asHom = (A.eulerMap 0).asHom := by
  rw [WantedExt.AlgebraicGeometry.RightHodgeSourceRequests.actual_nearby_euler_composition]

/-- `can` followed by `var` is the graded Euler map at index `0`. -/
example (A : GradedVOperators k M O C N V) :
    can k M O C N V A ≫ var k M O C N V A = (A.eulerMap 0).asHom := by
  have h := congrArg CategoryTheory.End.asHom
    (WantedExt.AlgebraicGeometry.RightHodgeSourceRequests.actual_nearby_euler_composition
      k M O C N V A)
  simpa [nearbyNilpotent] using h

end MathlibExtTest.AlgebraicGeometry.RightHodgeSourceRequestsActualNearbyEulerComposition
