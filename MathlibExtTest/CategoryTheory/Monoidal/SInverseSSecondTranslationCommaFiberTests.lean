/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCommaFiber

/-! # Tests for the second-translation comma/fiber comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationCommaFiber

open CategoryTheory.SInverseS
open CategoryTheory.Functor.IsCofibered

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check secondTranslationCostructuredPushforwardMap
#check secondTranslationCostructuredPushforwardMap_isHomLift
#check secondTranslationCostructuredToFiberApp
#check pushforwardMap_comp_secondTranslationCostructuredToFiberApp
#check secondTranslationCostructuredToFiberApp_naturality
#check secondTranslationCostructuredToFiberNatTrans

example (A : C) (B : Translation C) :
    secondTranslationCostructuredMap A B ⋙ costructuredToFiber B ⟶
      costructuredToFiber B ⋙ secondTranslationFiberFunctor A B :=
  secondTranslationCostructuredToFiberNatTrans A B

#print axioms secondTranslationCostructuredToFiberApp_naturality
#print axioms secondTranslationCostructuredToFiberNatTrans

section Homology

variable (D : Type) [Category.{0} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

#check secondTranslationCostructured_homologyMap_comp_coreComparison

example (R : AddCommGrpCat.{0}) (A : D) (B : Translation D) (n : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R n ≫
        ((costructuredFiberHomologyIso
            (p := translationProjection (C := D))
            AddCommGrpCat B R n).hom ≫
          (coreTranslationFiberHomologyIso D B R n).inv) =
      ((costructuredFiberHomologyIso
          (p := translationProjection (C := D))
          AddCommGrpCat B R n).hom ≫
        (coreTranslationFiberHomologyIso D B R n).inv) ≫
          coreTranslationHomologyMap D R n (toSkeleton A) :=
  secondTranslationCostructured_homologyMap_comp_coreComparison
    D R A B n

#print axioms secondTranslationCostructured_homologyMap_comp_coreComparison

end Homology

end MathlibExtTest.SInverseSSecondTranslationCommaFiber

end
