/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberPushforward

/-! # Tests for translation-fiber pushforward -/

@[expose] public section

#check CategoryTheory.SInverseS.coreLeftTranslationFunctor
#check CategoryTheory.SInverseS.coreLeftTranslationFunctor_obj_of
#check CategoryTheory.SInverseS.coreLeftTranslationFunctor_map_iso_hom
#check CategoryTheory.SInverseS.chosenCoreFiberPushforwardFunctor
#check CategoryTheory.SInverseS.chosenCoreFiberPushforwardFunctor_map_val
#check CategoryTheory.SInverseS.explicitCoreFiberPushforwardFunctor
#check CategoryTheory.SInverseS.explicitCoreFiberPushforwardFunctor_obj_val
#check CategoryTheory.SInverseS.coreFiberTranslationLift_naturality
#check CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIsoApp
#check CategoryTheory.SInverseS.pushforwardMap_comp_chosenExplicitCoreFiberPushforwardIsoApp_hom
#check CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIsoApp_naturality
#check CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIso

#print axioms CategoryTheory.SInverseS.coreFiberTranslationLift_naturality
#print axioms CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIsoApp
#print axioms
  CategoryTheory.SInverseS.pushforwardMap_comp_chosenExplicitCoreFiberPushforwardIsoApp_hom
#print axioms CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIsoApp_naturality
#print axioms CategoryTheory.SInverseS.chosenExplicitCoreFiberPushforwardIso

end
