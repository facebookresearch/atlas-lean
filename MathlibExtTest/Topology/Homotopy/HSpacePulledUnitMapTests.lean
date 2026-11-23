/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpacePulledUnitMap

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology Opposite
open scoped Simplicial

universe u

#check SSet.KanWeakInterpolation.pathMap_section
#print axioms SSet.KanWeakInterpolation.pathMap_section
#check TopCat.HSpaceCommonUnitFibration.unitTotalMap_section
#print axioms TopCat.HSpaceCommonUnitFibration.unitTotalMap_section
#check SSet.KanComplex.nativeCoverPointTransport_projection
#print axioms SSet.KanComplex.nativeCoverPointTransport_projection
#check SSet.KanComplex.nativeCoverPulledPointTransport_fst
#print axioms SSet.KanComplex.nativeCoverPulledPointTransport_fst
#check SSet.KanComplex.nativeCoverPulledPointTransport_snd
#print axioms SSet.KanComplex.nativeCoverPulledPointTransport_snd
#check SSet.KanComplex.nativeCoverMap_congr
#print axioms SSet.KanComplex.nativeCoverMap_congr
#check SSet.KanComplex.nativeCoverMap_commutingSquare
#print axioms SSet.KanComplex.nativeCoverMap_commutingSquare
#check TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap
#check TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_fst
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_fst
#check TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_snd
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_snd
#check TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_factor
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_factor
#check TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_integralHomology_isIso

namespace HSpacePulledUnitMapTests

example {A B A' B' : SSet.{u}} {f : A ⟶ B} {g : A' ⟶ B'} (s : Arrow.mk f ⟶ Arrow.mk g) :
    SSet.mappingPathSection f ≫ SSet.KanWeakInterpolation.pathMap s =
      s.left ≫ SSet.mappingPathSection g := SSet.KanWeakInterpolation.pathMap_section s

example {A B : SSet.{u}} {f g : A ⟶ B} (h : f = g) (a : A _⦋0⦌) :
    SSet.KanComplex.nativeCoverMap f a ≫ eqToHom (congrArg (SSet.KanComplex.nativeCover B)
      (congrArg (fun k : A ⟶ B => k.app (op ⦋0⦌) a) h)) =
      SSet.KanComplex.nativeCoverMap g a := SSet.KanComplex.nativeCoverMap_congr h a

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.mappingPathSection (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.HSpaceCommonUnitFibration.unitTotalMap f =
      TopCat.toSSet.map f ≫
        SSet.mappingPathSection (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)) :=
  TopCat.HSpaceCommonUnitFibration.unitTotalMap_section f

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap (TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap f x)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) :=
  TopCat.HSpaceCommonUnitFibration.originalPulledUnitMap_integralHomology_isIso f hf x n

end HSpacePulledUnitMapTests
