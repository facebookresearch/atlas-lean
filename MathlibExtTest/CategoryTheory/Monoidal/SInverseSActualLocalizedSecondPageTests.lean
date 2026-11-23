/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPage

public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.SInverseS HomologicalComplex₂

namespace SInverseSActualLocalizedSecondPageTests

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

local notation "A" => coreTranslationRing C
local notation "T" => coreTranslationDenominators C
local notation "B" => Localization T
local notation "L" => ModuleCat.localizedModuleFunctor T
local notation "Res" => ModuleCat.restrictScalars (algebraMap A B)
local notation "Y" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "P" => secondTranslationBKModuleSpectralSequence (C := C) R
local notation "LY" => secondTranslationBKLocalizedModuleSpectralObject (C := C) R
local notation "PB" => secondTranslationBKLocalizedModuleSpectralSequence (C := C) R
local notation "a" => secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R
local notation "Phi" => secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R
local notation "Gamma" => secondTranslationBKModuleSecondPageCoefficientIso (C := C) R
local notation "data" => SpectralObject.coreE₁FirstQuadrantHomological

example : PreservesFiniteLimits (L) := inferInstance
example : PreservesFiniteColimits (L) := inferInstance
example : (LY).HasSpectralSequence data := inferInstance

theorem same_interval (n : ℤ) (I : ComposableArrows EInt 1) :
    ((LY).H n).obj I = (L).obj (((Y).H n).obj I) := by
  rfl

theorem actual_interval_unit (n : ℤ) (I : ComposableArrows EInt 1) :
    ((secondTranslationBKModuleLocalization (C := C) R).hom n).app I =
      (ModuleCat.localizedModuleFunctorUnit T).app (((Y).H n).obj I) := by
  exact secondTranslationBKModuleLocalization_hom_app (C := C) R n I

theorem connecting_square {i j k : EInt} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    (Y).δ f g n₀ n₁ hn ≫
        ((secondTranslationBKModuleLocalization (C := C) R).hom n₁).app
          (ComposableArrows.mk₁ f) =
      ((secondTranslationBKModuleLocalization (C := C) R).hom n₀).app
          (ComposableArrows.mk₁ g) ≫
        ((Res).mapSpectralObject LY).δ f g n₀ n₁ hn := by
  exact (secondTranslationBKModuleLocalization (C := C) R).comm n₀ n₁ hn f g

theorem all_page_differentials (r : ℤ) (hr : 1 ≤ r) (x y : ℕ × ℕ) :
    (L).map (((P).page r hr).d x y) ≫ ((a).hom.hom r hr).f y =
      ((a).hom.hom r hr).f x ≫ ((PB).page r hr).d x y := by
  exact (((a).hom.hom r hr).comm x y).symm

theorem native_successors (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    HomologicalComplex.homologyMap ((a).hom.hom r hr) x ≫
        ((PB).iso r r' x hrr' hr).hom =
      (((L).mapSpectralSequence P).iso r r' x hrr' hr).hom ≫
        ((a).hom.hom r' (by omega)).f x := by
  exact (a).hom.comm r r' x hrr' hr

theorem inverse_native_successors
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    HomologicalComplex.homologyMap ((a).inv.hom r hr) x ≫
        (((L).mapSpectralSequence P).iso r r' x hrr' hr).hom =
      ((PB).iso r r' x hrr' hr).hom ≫ ((a).inv.hom r' (by omega)).f x := by
  exact (a).inv.comm r r' x hrr' hr

theorem exact_phi_forward (p q : ℕ) :
    (Phi p q).hom = ((a).inv.hom 2 (by omega)).f (p,q) ≫ (L).map (Gamma p q).hom := by
  exact secondTranslationBKLocalizedModuleSecondPageCoefficientIso_hom (C := C) R p q

theorem exact_phi_inverse (p q : ℕ) :
    (Phi p q).inv = (L).map (Gamma p q).inv ≫ ((a).hom.hom 2 (by omega)).f (p,q) := by
  exact secondTranslationBKLocalizedModuleSecondPageCoefficientIso_inv (C := C) R p q

theorem phi_scalar (p q : ℕ) (s : B) (x : ((PB).page 2 (by omega)).X (p,q)) :
    (Phi p q).hom (s • x) = s • (Phi p q).hom x := by
  exact (Phi p q).hom.hom.map_smul s x

theorem same_zero_lower_cut (q : ℕ) :
    (data).i₁ (0,q) = ((-1 : ℤ) : EInt) := by
  rfl

theorem full_stage_to_total (d : ℕ) (i : EInt) :
    (secondTranslationBKLocalizedStageModuleIso (C := C) R d i).hom ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d i) =
      ((LY).H (-(d : ℤ))).map
          (secondTranslationBKStageIntervalMap (show i ≤ ⊤ from le_top)) ≫
        (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R d).hom := by
  exact secondTranslationBKLocalizedStageModuleIso_comp_toTotal (C := C) R d i

theorem all_cut_transitions (d : ℕ) {i j : EInt} (h : i ≤ j) :
    (L).map (secondTranslationBKStageHomologyModuleMap (C := C) R d h) ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d j) =
      (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d i) := by
  exact secondTranslationBKLocalizedStageModuleMap_comp_toTotal (C := C) R d h

theorem canonical_total_forward (p q : ℕ) :
    (secondTranslationBKLocalizedCanonicalToTotalModuleIso (C := C) R p q).hom =
      (L).map (secondTranslationBKCanonicalToTotalModuleIso (C := C) R p q).hom := by
  exact secondTranslationBKLocalizedCanonicalToTotalModuleIso_hom (C := C) R p q

theorem canonical_total_inverse (p q : ℕ) :
    (secondTranslationBKLocalizedCanonicalToTotalModuleIso (C := C) R p q).inv =
      (L).map (secondTranslationBKCanonicalToTotalModuleIso (C := C) R p q).inv := by
  exact secondTranslationBKLocalizedCanonicalToTotalModuleIso_inv (C := C) R p q

local notation "U" => forget₂ (ModuleCat A) AddCommGrpCat

theorem original_forward_square (p q : ℕ) :
    (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p,q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv ≫
        (U).map ((ModuleCat.localizedModuleFunctorUnit T).app
          (coreTranslationActionCoefficientHomology C R q p)) =
      (U).map
        ((ModuleCat.localizedModuleFunctorUnit T).app (((P).page 2 (by omega)).X (p,q)) ≫
          (Res).map (((a).hom.hom 2 (by omega)).f (p,q) ≫ (Phi p q).hom)) := by
  exact secondTranslationBKLocalizedModuleSecondPageLocalizationSquare_forget (C := C) R p q

end SInverseSActualLocalizedSecondPageTests
