/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberHomologyComparison

/-! # Tests for localized strict-fiber homology coefficients -/

@[expose] public section

#check CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationLinearEquiv
#check CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationIsoApp
#check CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationLinearEquiv_comp_mk
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv_comp_mk
#check CategoryTheory.SInverseS.coreTranslationLocalizedMap_comp_mk
#check CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationIsoApp_naturality
#check CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationNatIso
#check CategoryTheory.SInverseS.localizedCoreTranslationActionCoefficientHomology
#check CategoryTheory.SInverseS.localizedCoreTranslationActionCoefficientHomologyIso
#check CategoryTheory.SInverseS.localizedCoreTranslationActionCoefficientHomologyZeroIso
#check CategoryTheory.SInverseS.isZero_localizedCoreTranslationActionCoefficientHomology

#print axioms
  CategoryTheory.SInverseS.coreTranslationCoefficientLocalizationNatIso
#print axioms
  CategoryTheory.SInverseS.localizedCoreTranslationActionCoefficientHomologyZeroIso
#print axioms
  CategoryTheory.SInverseS.isZero_localizedCoreTranslationActionCoefficientHomology

end
