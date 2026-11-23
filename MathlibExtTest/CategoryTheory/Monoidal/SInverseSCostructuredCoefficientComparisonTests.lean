/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCostructuredCoefficientComparison

/-! # Tests for the right-comma/core coefficient comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSCostructuredCoefficientComparison

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check costructuredCoreTranslationCoefficientNatIso
#check costructuredCoreTranslationCoefficientNatIso_hom_app

example (R : AddCommGrpCat.{0}) (q : ℕ) :
    Functor.IsCofibered.costructuredHomologyFunctor
        (p := translationProjection (C := C)) AddCommGrpCat.{0} R q ≅
      coreTranslationCoefficientFunctor C R q ⋙
        forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat :=
  costructuredCoreTranslationCoefficientNatIso C R q

-- Boundary check: degree zero and the zero base object use the same
-- canonical comma/fiber/core component formula.
example (R : AddCommGrpCat.{0}) :
    (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app
        (⟨(0 : C)⟩ : Translation C) =
      (Functor.IsCofibered.costructuredFiberHomologyIso
          (p := translationProjection (C := C)) AddCommGrpCat.{0}
          (⟨(0 : C)⟩ : Translation C) R 0).hom ≫
        (coreTranslationCoefficientFiberIsoApp C R 0
          (⟨(0 : C)⟩ : Translation C)).inv :=
  costructuredCoreTranslationCoefficientNatIso_hom_app C R 0 _

-- The packaged components satisfy the expected base-arrow naturality.
example (R : AddCommGrpCat.{0}) (q : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    (Functor.IsCofibered.costructuredHomologyFunctor
          (p := translationProjection (C := C)) AddCommGrpCat.{0} R q).map f ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app T =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (coreTranslationCoefficientFunctor C R q ⋙
          forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map f :=
  (costructuredCoreTranslationCoefficientNatIso C R q).hom.naturality f

#print axioms costructuredCoreTranslationCoefficientNatIso
#print axioms costructuredCoreTranslationCoefficientNatIso_hom_app

end MathlibExtTest.SInverseSCostructuredCoefficientComparison

end
