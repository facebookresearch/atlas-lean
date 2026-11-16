/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealizationModels

/-!
The finite point dictionary is checked on the entire scheme morphism,
so nonreduced coefficient algebras are retained. The finite-to-formal
origin condition is inspected as a literal square-zero coefficient map,
and the original Tate module and O_C tests remain in the public signatures.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteCartierCharacterModels PDivisibleGroupSchemes
open PDivisibleCartierTowerModels
open scoped CategoryTheory.MonObj

noncomputable section

example (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (G : MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat (.of R))
    (x : AlgebraTest R A ⟶ G.obj.obj.X) :
    Spec.mapMulEquiv (R := R) (S := Coordinate R G) (T := A) (coordinatePointAt R G A x) =
      x ≫ (coordinateSchemeIso R G).inv.hom.hom := coordinate_point_recovers R G A x

#check @PDivisibleFormalCartierCotangentModels.CotangentBridge.finite_origin
#check @PDivisibleHodgeTateRealizationModels.IntegralProjection
#check @PDivisibleHodgeTateRealizationModels.HodgeTateMap.finite_normalization
#check @PDivisibleHodgeTateRealizationModels.HodgeTateMap.pure_normalization

#print axioms FiniteCartierCharacterModels.coordinate_point_recovers
#print axioms FiniteCartierCharacterModels.characterUnit
#print axioms FiniteCartierCharacterModels.finiteDlog
#print axioms PDivisibleCartierTowerModels.finite_point_power
#print axioms PDivisibleCartierTowerModels.geometricFiniteDlog
#print axioms PDivisibleCartierTowerModels.finiteCotangentTransition
#print axioms PDivisibleFiniteTangentModels.augmentation_square
#print axioms PDivisibleFiniteTangentModels.tangentInclusion
#print axioms PDivisibleFormalCartierCotangentModels.tangentCoordinates
#print axioms AlgebraicallyClosedPadicTests.padicIntegerScalars
