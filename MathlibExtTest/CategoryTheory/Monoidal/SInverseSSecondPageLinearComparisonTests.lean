/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondPageLinearComparison

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SInverseS

namespace SInverseSSecondPageLinearComparisonTests

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

local notation "Alg" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))
local notation "U" => forget₂ (ModuleCat Alg) AddCommGrpCat
local notation "P" => secondTranslationBKModuleSpectralSequence (C := C) R

theorem exact_forward (p q : ℕ) :
    (U).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom =
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p, q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv := by
  exact secondTranslationBKModuleSecondPageCoefficientIso_hom_forget (C := C) R p q

theorem exact_inverse (p q : ℕ) :
    (U).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv =
      (coreTranslationActionSecondPageIso C R p q).hom ≫
        (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).inv.f (p, q) := by
  exact secondTranslationBKModuleSecondPageCoefficientIso_inv_forget (C := C) R p q

theorem forward_scalar (p q : ℕ) (a : Alg)
    (x : (((P).page 2 (by omega)).X (p, q))) :
    (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom (a • x) =
      a • (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom x := by
  exact (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).hom.hom.map_smul a x

theorem inverse_scalar (p q : ℕ) (a : Alg)
    (y : coreTranslationActionCoefficientHomology C R q p) :
    (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv (a • y) =
      a • (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv y := by
  exact (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q).inv.hom.map_smul a y

theorem zero_column_exact (q : ℕ) :
    (U).map (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R 0 q).hom =
      (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (0, q) ≫
        (coreTranslationActionSecondPageIso C R 0 q).inv := by
  exact secondTranslationBKModuleSecondPageCoefficientIso_hom_forget (C := C) R 0 q

end SInverseSSecondPageLinearComparisonTests
