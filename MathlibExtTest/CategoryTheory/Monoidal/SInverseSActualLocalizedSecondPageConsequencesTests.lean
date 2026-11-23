/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPageConsequences

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SInverseS

namespace SInverseSActualLocalizedSecondPageConsequencesTests

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

local notation "T" => coreTranslationDenominators C
local notation "B" => Localization T
local notation "L" => ModuleCat.localizedModuleFunctor T
local notation "PB" => secondTranslationBKLocalizedModuleSpectralSequence (C := C) R
local notation "a" => secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R
local notation "Phi" => secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R
local notation "Gamma" => secondTranslationBKModuleSecondPageCoefficientIso (C := C) R
local notation "Z" => secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R
local notation "zeta" => localizedCoreTranslationActionCoefficientRefinementZeroIso C R

theorem all_positive_degrees (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (((PB).page 2 (by omega)).X (p,q)) := by
  exact isZero_secondTranslationBKLocalizedModuleSecondPage (C := C) R p q hp

theorem bottom_positive_degree :
    IsZero (((PB).page 2 (by omega)).X (1,0)) := by
  exact isZero_secondTranslationBKLocalizedModuleSecondPage (C := C) R 1 0 (by omega)

example (q : ℕ) :
    ((PB).page 2 (by omega)).X (0,q) ≅ localizedCoreTranslationHomologyModuleCat C R q :=
  Z q

example :
    ((PB).page 2 (by omega)).X (0,0) ≅ localizedCoreTranslationHomologyModuleCat C R 0 :=
  Z 0

theorem exact_zero_column_forward (q : ℕ) :
    (Z q).hom = (Phi 0 q).hom ≫ (zeta q).hom := by
  exact secondTranslationBKLocalizedModuleSecondPageZeroIso_hom (C := C) R q

theorem exact_zero_column_inverse (q : ℕ) :
    (Z q).inv = (zeta q).inv ≫ (Phi 0 q).inv := by
  exact secondTranslationBKLocalizedModuleSecondPageZeroIso_inv (C := C) R q

theorem zero_column_hom_inv (q : ℕ) :
    (Z q).hom ≫ (Z q).inv = 𝟙 _ := by
  exact (Z q).hom_inv_id

theorem zero_column_inv_hom (q : ℕ) :
    (Z q).inv ≫ (Z q).hom = 𝟙 _ := by
  exact (Z q).inv_hom_id

theorem zero_column_scalar (q : ℕ) (s : B)
    (x : ((PB).page 2 (by omega)).X (0,q)) :
    (Z q).hom (s • x) = s • (Z q).hom x := by
  exact (Z q).hom.hom.map_smul s x

theorem zero_column_inverse_scalar (q : ℕ) (s : B)
    (y : localizedCoreTranslationHomologyModuleCat C R q) :
    (Z q).inv (s • y) = s • (Z q).inv y := by
  exact (Z q).inv.hom.map_smul s y

theorem original_zero_column_forward (q : ℕ) :
    (Z q).hom =
      ((a).inv.hom 2 (by omega)).f (0,q) ≫
        (L).map (Gamma 0 q).hom ≫ (zeta q).hom := by
  calc
    (Z q).hom = (Phi 0 q).hom ≫ (zeta q).hom :=
      secondTranslationBKLocalizedModuleSecondPageZeroIso_hom (C := C) R q
    _ = (((a).inv.hom 2 (by omega)).f (0,q) ≫
        (L).map (Gamma 0 q).hom) ≫ (zeta q).hom :=
      congrArg (fun f => f ≫ (zeta q).hom)
        (secondTranslationBKLocalizedModuleSecondPageCoefficientIso_hom (C := C) R 0 q)
    _ = ((a).inv.hom 2 (by omega)).f (0,q) ≫
        (L).map (Gamma 0 q).hom ≫ (zeta q).hom :=
      Category.assoc _ _ _

theorem original_zero_column_inverse (q : ℕ) :
    (Z q).inv =
      (zeta q).inv ≫ (L).map (Gamma 0 q).inv ≫
        ((a).hom.hom 2 (by omega)).f (0,q) := by
  rw [secondTranslationBKLocalizedModuleSecondPageZeroIso_inv,
    secondTranslationBKLocalizedModuleSecondPageCoefficientIso_inv]

end SInverseSActualLocalizedSecondPageConsequencesTests
