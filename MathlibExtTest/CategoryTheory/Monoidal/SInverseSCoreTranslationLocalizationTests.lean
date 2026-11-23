/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationLocalization

/-! # Tests for localization of the skeleton action -/

@[expose] public section

#check CategoryTheory.SInverseS.coreTranslationRing
#check CategoryTheory.SInverseS.coreTranslationDenominators
#check CategoryTheory.SInverseS.localizedCoreTranslationHomology
#check CategoryTheory.SInverseS.coreTranslationDenominator
#check CategoryTheory.SInverseS.localizedCoreTranslationMonomialUnit
#check CategoryTheory.SInverseS.localizedCoreTranslationMonomialUnit_val
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv_apply
#check CategoryTheory.SInverseS.localizedCoreTranslationEquiv_mk

#print axioms CategoryTheory.SInverseS.localizedCoreTranslationEquiv
#print axioms CategoryTheory.SInverseS.localizedCoreTranslationEquiv_mk

end
