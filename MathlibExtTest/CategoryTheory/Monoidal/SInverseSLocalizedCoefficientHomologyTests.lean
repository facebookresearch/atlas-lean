/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoefficientHomology

/-! # Tests for localized translation coefficient homology -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.SInverseSLocalizedCoefficientHomologyTests

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check SInverseS.localizedCoreTranslationCoefficientHomology
#check SInverseS.localizedCoreTranslationCoefficientHomologyZeroIso
#check SInverseS.isZero_localizedCoreTranslationCoefficientHomology

example (R : AddCommGrpCat.{0}) (q : ℕ) :
    SInverseS.localizedCoreTranslationCoefficientHomology C R q 0 ≅
      SInverseS.localizedCoreTranslationHomologyModuleCat C R q :=
  SInverseS.localizedCoreTranslationCoefficientHomologyZeroIso C R q

example (R : AddCommGrpCat.{0}) (q p : ℕ) (hp : 1 ≤ p) :
    IsZero
      (SInverseS.localizedCoreTranslationCoefficientHomology C R q p) :=
  SInverseS.isZero_localizedCoreTranslationCoefficientHomology C R q p hp

#print axioms SInverseS.localizedCoreTranslationCoefficientHomologyZeroIso
#print axioms SInverseS.isZero_localizedCoreTranslationCoefficientHomology

end CategoryTheory.SInverseSLocalizedCoefficientHomologyTests

end
