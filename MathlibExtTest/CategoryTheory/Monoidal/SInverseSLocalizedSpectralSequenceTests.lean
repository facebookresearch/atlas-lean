/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence

/-! # Tests for the localized core-action coefficient refinement -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.SInverseSLocalizedSpectralSequenceTests

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example (R : AddCommGrpCat.{0}) (p q : ℕ) :
    (forget₂
        (ModuleCat (SInverseS.coreTranslationRing C)) AddCommGrpCat).obj
        (SInverseS.coreTranslationActionCoefficientHomology C R q p) ≅
      ((SInverseS.translationBKHomologySpectralSequence C R).page 2).X
        (p, q) :=
  SInverseS.coreTranslationActionSecondPageIso C R p q

example (R : AddCommGrpCat.{0}) (p q : ℕ) :
    SInverseS.localizedCoreTranslationActionCoefficientRefinement C R p q ≅
      SInverseS.localizedCoreTranslationCoefficientHomology C R q p :=
  SInverseS.localizedCoreTranslationActionCoefficientRefinementIso C R p q

example (R : AddCommGrpCat.{0}) (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (SInverseS.localizedCoreTranslationActionCoefficientRefinement C R p q) :=
  SInverseS.isZero_localizedCoreTranslationActionCoefficientRefinement C R p q hp

example (R : AddCommGrpCat.{0}) (q : ℕ) :
    SInverseS.localizedCoreTranslationActionCoefficientRefinement C R 0 q ≅
      SInverseS.localizedCoreTranslationHomologyModuleCat C R q :=
  SInverseS.localizedCoreTranslationActionCoefficientRefinementZeroIso C R q

example (R : AddCommGrpCat.{0}) (q : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((SInverseS.translationBKHomologySpectralSequence C R).page 2).X
        (p, q))) :
    (forget₂
        (ModuleCat (SInverseS.coreTranslationRing C)) AddCommGrpCat).obj
        (SInverseS.coreTranslationActionCoefficientHomology C R q 0) ≅
      (SSet.bkAlternatingTotalComplex AddCommGrpCat R
        (SSet.rightCommaNerveDiagram
          (SInverseS.translationProjection (C := C)))).homology q :=
  SInverseS.coreTranslationActionSecondPageTotalHomologyIso C R q hpos

example (R : AddCommGrpCat.{0}) (q : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((SInverseS.translationBKHomologySpectralSequence C R).page 2).X
        (p, q))) :
    (forget₂
        (ModuleCat (SInverseS.coreTranslationRing C)) AddCommGrpCat).obj
        (SInverseS.coreTranslationActionCoefficientHomology C R q 0) ≅
      ((nerve (SInverseS.Pair C)).chainComplex R).homology q :=
  SInverseS.coreTranslationActionSecondPageAbutmentIso C R q hpos

#print axioms SInverseS.coreTranslationActionSecondPageIso
#print axioms SInverseS.localizedCoreTranslationActionCoefficientRefinementIso
#print axioms SInverseS.isZero_localizedCoreTranslationActionCoefficientRefinement
#print axioms SInverseS.localizedCoreTranslationActionCoefficientRefinementZeroIso
#print axioms SInverseS.coreTranslationActionSecondPageTotalHomologyIso
#print axioms SInverseS.coreTranslationActionSecondPageAbutmentIso

end CategoryTheory.SInverseSLocalizedSpectralSequenceTests

end
