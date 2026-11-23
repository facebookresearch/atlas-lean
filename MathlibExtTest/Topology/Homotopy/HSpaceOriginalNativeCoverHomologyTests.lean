/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceOriginalNativeCoverHomology

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison
#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_fst
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_fst
#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_snd
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_snd
#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_mem_realizationWeakEquivalences
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_mem_realizationWeakEquivalences
#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitPoint_eq
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitPoint_eq
#check TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_square
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeUnitComparison_square
#check TopCat.HSpaceCommonUnitFibration.originalNativeCoverMap_integralHomology_isIso
#print axioms TopCat.HSpaceCommonUnitFibration.originalNativeCoverMap_integralHomology_isIso
#check TopCat.HSpaceCommonUnitFibration.originalRegularProjection_integralHomology_isIso_at_image
#print axioms TopCat.HSpaceCommonUnitFibration.originalRegularProjection_integralHomology_isIso_at_image

namespace HSpaceOriginalNativeCoverHomologyTests

open TopCat.HSpaceCommonUnitFibration

example (X : TopCat.{u}) (sx : (TopCat.toSSet.obj X) _⦋0⦌) :
    SSet.realizationWeakEquivalences (originalNativeUnitComparison X sx) :=
  originalNativeUnitComparison_mem_realizationWeakEquivalences X sx

example {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    originalNativeUnitComparison X (TopCat.toSSetObj₀Equiv.symm x) ≫ originalPulledUnitMap f x =
      (SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x) ≫
        originalNativeUnitComparison Y
          ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x))) ≫
        eqToHom (congrArg (fun b => pullback (unitProjection Y)
          (SSet.KanComplex.nativeCoverProjection
            (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))) b))
          (originalNativeUnitPoint_eq f x)) := originalNativeUnitComparison_square f x

variable {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
  (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
  (x : X) (n : ℕ)

example : IsIso (SSet.homologyMap
    (SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x))
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) :=
  originalNativeCoverMap_integralHomology_isIso f hf x n

example : IsIso (SSet.homologyMap
    (pullback.snd (TopCat.toSSet.map f)
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
        ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x))))
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) :=
  originalRegularProjection_integralHomology_isIso_at_image f hf x n

end HSpaceOriginalNativeCoverHomologyTests
