/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison

/-! # Tests for the core-module/fiber-homology comparison -/

@[expose] public section

#check CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
#check CategoryTheory.SInverseS.coreTranslationCoefficientFunctor
#check CategoryTheory.SInverseS.coreTranslationHomologyModuleAddCommGrpIso
#check
  CategoryTheory.SInverseS.coreTranslationCoefficientFunctor_map_comp_moduleIso_hom
#check CategoryTheory.SInverseS.coreTranslationCoefficientFiberIsoApp
#check CategoryTheory.SInverseS.coreTranslationCoefficientFiberIsoApp_naturality
#check CategoryTheory.SInverseS.coreTranslationCoefficientFiberNatIso

#print axioms CategoryTheory.SInverseS.coreTranslationCoefficientFiberNatIso

end
