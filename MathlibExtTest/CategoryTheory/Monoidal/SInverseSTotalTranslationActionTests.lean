/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTotalTranslationAction

/-! # Tests for the skeleton action on additive S⁻¹S homology -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

#check CategoryTheory.SInverseS.RawHom.ofCoordinateIsos
#check CategoryTheory.SInverseS.pairIsoOfCoordinateIsos
#check CategoryTheory.SInverseS.pairIsoOfCoordinateIsos_hom
#check CategoryTheory.SInverseS.pairIsoOfCoordinateIsos_inv
#check CategoryTheory.SInverseS.translateFirstIsoOfIso
#check CategoryTheory.SInverseS.translateFirstZeroIso
#check CategoryTheory.SInverseS.translateFirstBiprodIso
#check CategoryTheory.SInverseS.translateFirstSkeletonZeroIso
#check CategoryTheory.SInverseS.translateFirstSkeletonAddIso
#check CategoryTheory.SInverseS.pairTranslationHomologyMap
#check CategoryTheory.SInverseS.pairTranslationHomologyMap_toSkeleton
#check CategoryTheory.SInverseS.pairTranslationHomologyMap_zero
#check CategoryTheory.SInverseS.pairTranslationHomologyMap_add
#check CategoryTheory.SInverseS.pairTranslationHomologyAction
#check CategoryTheory.SInverseS.pairTranslationHomologyModule
#check CategoryTheory.SInverseS.pairTranslationHomologyModuleForgetIso
#check CategoryTheory.SInverseS.pairTranslationHomologyModuleForgetIso_monomial_smul
#check CategoryTheory.SInverseS.pairSecondTranslationHomologyMap
#check CategoryTheory.SInverseS.pairTranslationHomologyIsoOfObject
#check CategoryTheory.SInverseS.pairTranslationHomologyIsoToSkeleton
#check CategoryTheory.SInverseS.pairTranslationHomologyIso
#check CategoryTheory.SInverseS.pairTranslationHomologyIso_hom
#check CategoryTheory.SInverseS.pairTranslationHomologyIso_inv
#check CategoryTheory.SInverseS.pairTranslationHomologyMonomialIso
#check CategoryTheory.SInverseS.pairTranslationHomologyMonomialIso_hom_apply
#check CategoryTheory.SInverseS.pairTranslationHomologyModule_monomial_bijective

universe v u

namespace CategoryTheory.SInverseSTotalTranslationActionTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example {X Y : SInverseS.Pair C}
    (e₁ : X.fst ≅ Y.fst) (e₂ : X.snd ≅ Y.snd) : X ≅ Y :=
  SInverseS.pairIsoOfCoordinateIsos e₁ e₂

example (s t : C) :
    SInverseS.translateFirstFunctor (s ⊞ t) ≅
      SInverseS.translateFirstFunctor t ⋙
        SInverseS.translateFirstFunctor s :=
  SInverseS.translateFirstBiprodIso s t

end CategoryTheory.SInverseSTotalTranslationActionTests

#print axioms CategoryTheory.SInverseS.translateFirstIsoOfIso
#print axioms CategoryTheory.SInverseS.translateFirstZeroIso
#print axioms CategoryTheory.SInverseS.translateFirstBiprodIso
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyMap_zero
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyMap_add
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyAction
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyIsoOfObject
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyIsoToSkeleton
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyMonomialIso_hom_apply
#print axioms CategoryTheory.SInverseS.pairTranslationHomologyModule_monomial_bijective

end
