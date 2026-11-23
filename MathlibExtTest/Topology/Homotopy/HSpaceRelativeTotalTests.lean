/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceRelativeTotal

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

#check TopCat.HSpaceCommonUnitFibration.unitProjection_isFibration
#print axioms TopCat.HSpaceCommonUnitFibration.unitProjection_isFibration
#check TopCat.HSpaceCommonUnitFibration.commonRelativeFactorization
#print axioms TopCat.HSpaceCommonUnitFibration.commonRelativeFactorization
#check TopCat.HSpaceCommonUnitFibration.relativeInclusion_comparison
#print axioms TopCat.HSpaceCommonUnitFibration.relativeInclusion_comparison
#check TopCat.HSpaceCommonUnitFibration.relativeInclusion_mono
#print axioms TopCat.HSpaceCommonUnitFibration.relativeInclusion_mono
#check TopCat.HSpaceCommonUnitFibration.relativeComparison_fibration
#print axioms TopCat.HSpaceCommonUnitFibration.relativeComparison_fibration
#check TopCat.HSpaceCommonUnitFibration.relativeComparison_mem_realizationWeakEquivalences
#print axioms TopCat.HSpaceCommonUnitFibration.relativeComparison_mem_realizationWeakEquivalences
#check TopCat.HSpaceCommonUnitFibration.relativeInclusion_projection
#print axioms TopCat.HSpaceCommonUnitFibration.relativeInclusion_projection
#check TopCat.HSpaceCommonUnitFibration.relativeProjection_fibration
#print axioms TopCat.HSpaceCommonUnitFibration.relativeProjection_fibration
#check TopCat.HSpaceCommonUnitFibration.relativeInclusion_original
#print axioms TopCat.HSpaceCommonUnitFibration.relativeInclusion_original
#check TopCat.HSpaceCommonUnitFibration.relativeInclusion_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.relativeInclusion_integralHomology_isIso
#check TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientTotal_acyclic_of_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalRelativeCoefficientTotal_acyclic_of_integralHomology_isIso

namespace HSpaceRelativeTotalTests

open TopCat.HSpaceCommonUnitFibration

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫ relativeComparison f = commonTotalMap f :=
  relativeInclusion_comparison f

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫ relativeProjection f = unitProjection X :=
  relativeInclusion_projection f

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫
      (relativeComparison f ≫ commonTargetComparison f ≫ SSet.mappingPathRetract
        (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f :=
  relativeInclusion_original f

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    (originalRelativeCoefficientTotal f).Acyclic :=
  originalRelativeCoefficientTotal_acyclic_of_integralHomology_isIso f h

end HSpaceRelativeTotalTests
