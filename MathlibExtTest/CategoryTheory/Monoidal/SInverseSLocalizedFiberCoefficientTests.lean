/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberCoefficient

/-! # Tests for localized translation coefficients -/

@[expose] public section

#check CategoryTheory.SInverseS.translationStabilizerClass
#check CategoryTheory.SInverseS.translationStabilizerClass_id
#check CategoryTheory.SInverseS.translationStabilizerClass_comp
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv_zero_toLinearMap
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv_add_toLinearMap
#check CategoryTheory.SInverseS.localizedCoreTranslationCoefficientFunctor
#check CategoryTheory.SInverseS.localizedCoreTranslationCoefficientFunctor_map_isIso

#print axioms CategoryTheory.SInverseS.translationStabilizerClass_comp
#print axioms
  CategoryTheory.SInverseS.localizedCoreTranslationCoefficientFunctor

end
