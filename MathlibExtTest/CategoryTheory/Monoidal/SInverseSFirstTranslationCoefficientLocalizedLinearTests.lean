/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientLocalizedLinear

/-! # Tests for localized conjugated first-translation identity -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSFirstTranslationCoefficientLocalizedLinear

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check localizedConjugatedFirstTranslationCoefficientModuleMap
#check localizedConjugatedFirstTranslationCoefficientModuleMap_eq_id

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    localizedConjugatedFirstTranslationCoefficientModuleMap C R q A B =
      𝟙 _ := by
  simp

example (R : AddCommGrpCat.{0}) (q : ℕ) (B : Translation C) :
    localizedConjugatedFirstTranslationCoefficientModuleMap
        C R q (0 : C) B = 𝟙 _ := by
  simp

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    localizedConjugatedFirstTranslationCoefficientModuleMap C R q A
        (⟨(0 : C)⟩ : Translation C) = 𝟙 _ := by
  simp

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    localizedConjugatedFirstTranslationCoefficientModuleMap C R 0 A B =
      𝟙 _ := by
  simp

#print axioms localizedConjugatedFirstTranslationCoefficientModuleMap
#print axioms localizedConjugatedFirstTranslationCoefficientModuleMap_eq_id

end MathlibExtTest.SInverseSFirstTranslationCoefficientLocalizedLinear

end
