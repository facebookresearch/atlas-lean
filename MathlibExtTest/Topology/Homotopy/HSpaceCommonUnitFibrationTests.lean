/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceCommonUnitFibration

open CategoryTheory
open scoped Simplicial

universe u

#check TopCat.HSpaceCommonUnitFibration.unitTotalMap
#print axioms TopCat.HSpaceCommonUnitFibration.unitTotalMap
#check TopCat.HSpaceCommonUnitFibration.unitTotalMap_projection
#print axioms TopCat.HSpaceCommonUnitFibration.unitTotalMap_projection
#check TopCat.HSpaceCommonUnitFibration.unitTotalMap_retract
#print axioms TopCat.HSpaceCommonUnitFibration.unitTotalMap_retract
#check TopCat.HSpaceCommonUnitFibration.commonTotalMap
#print axioms TopCat.HSpaceCommonUnitFibration.commonTotalMap
#check TopCat.HSpaceCommonUnitFibration.commonTotalMap_fst
#print axioms TopCat.HSpaceCommonUnitFibration.commonTotalMap_fst
#check TopCat.HSpaceCommonUnitFibration.commonTotalMap_snd
#print axioms TopCat.HSpaceCommonUnitFibration.commonTotalMap_snd
#check TopCat.HSpaceCommonUnitFibration.commonTotalMap_original
#print axioms TopCat.HSpaceCommonUnitFibration.commonTotalMap_original
#check TopCat.HSpaceCommonUnitFibration.commonTargetComparison_mem_realizationWeakEquivalences_of_integralH1
#print axioms TopCat.HSpaceCommonUnitFibration.commonTargetComparison_mem_realizationWeakEquivalences_of_integralH1
#check TopCat.HSpaceCommonUnitFibration.commonTotalMap_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.commonTotalMap_integralHomology_isIso

namespace HSpaceCommonUnitFibrationTests

open TopCat.HSpaceCommonUnitFibration

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫ CategoryTheory.Limits.pullback.fst (baseMap f) (unitProjection Y) =
      unitProjection X := commonTotalMap_fst f

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫
      (commonTargetComparison f ≫ SSet.mappingPathRetract
        (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f := commonTotalMap_original f

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    ∀ n : ℕ, IsIso (SSet.homologyMap (commonTotalMap f)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) :=
  fun n => commonTotalMap_integralHomology_isIso f (h 1) n (h n)

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    SSet.realizationWeakEquivalences (commonTargetComparison f) :=
  commonTargetComparison_mem_realizationWeakEquivalences_of_integralH1 f h1

end HSpaceCommonUnitFibrationTests
