/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnit
public import MathlibExt.Algebra.Homology.SpectralObject.Functor
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondPageLinearComparison
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModuleAbutment

/-!
# The actual localized BK spectral model and canonical maps

Apply exact module localization to the same accepted integral BK spectral
object. Its native sequence retains the complete intervals, signed degrees,
page-one recipe, differentials and successor maps. The canonical whole
sequence comparison identifies its second page with localization of the
actual integral coefficient comparison.

The interval localization morphism and page square use the canonical module
localization unit with scalar restriction. Complete-stage and total
comparisons are the mapped accepted comparisons on this same model. The
construction uses only the native category and coefficient group. It does
not assert localized concentration, an edge formula or the Q-plus theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex₂

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "A" => coreTranslationRing C
local notation "T" => coreTranslationDenominators C
local notation "B" => Localization T
local notation "L" => ModuleCat.localizedModuleFunctor T
local notation "Res" => ModuleCat.restrictScalars (algebraMap A B)
local notation "Y" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "P" => secondTranslationBKModuleSpectralSequence (C := C) R
local notation "data" => SpectralObject.coreE₁FirstQuadrantHomological

/-- Exact localization of every interval and connecting map of the same
actual integral BK module spectral object. -/
def secondTranslationBKLocalizedModuleSpectralObject :
    SpectralObject (ModuleCat.{u} B) EInt :=
  (L).mapSpectralObject Y

/-- The original native boundary support is transported by localization's
derived exactness and forward preservation of zero objects. -/
instance secondTranslationBKLocalizedModuleSpectralObject_hasSpectralSequence :
    (secondTranslationBKLocalizedModuleSpectralObject (C := C) R).HasSpectralSequence data :=
  inferInstanceAs (((L).mapSpectralObject Y).HasSpectralSequence data)

/-- The actual localized native sequence starts at page one with the
original increasing homological recipe and differential bidegree. -/
def secondTranslationBKLocalizedModuleSpectralSequence :
    SpectralSequence (ModuleCat.{u} B)
      (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 :=
  (secondTranslationBKLocalizedModuleSpectralObject (C := C) R).spectralSequence data

local notation "LY" => secondTranslationBKLocalizedModuleSpectralObject (C := C) R
local notation "PB" => secondTranslationBKLocalizedModuleSpectralSequence (C := C) R

/-- The canonical comparison of the whole mapped integral sequence with
the native sequence of the actual localized spectral object. -/
def secondTranslationBKLocalizedModuleSpectralSequenceIso :
    (L).mapSpectralSequence P ≅ PB :=
  (L).mapSpectralObjectSpectralSequenceIso Y data

local notation "a" => secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R

/-- Every forward page map is the canonical exact-transport comparison. -/
@[simp]
theorem secondTranslationBKLocalizedModuleSpectralSequenceIso_hom_hom
    (r : ℤ) (hr : 1 ≤ r) :
    (a).hom.hom r hr =
      ((L).mapSpectralObjectSpectralSequencePageIso Y data r hr).hom := rfl

/-- Every inverse page map is the inverse of that same comparison. -/
@[simp]
theorem secondTranslationBKLocalizedModuleSpectralSequenceIso_inv_hom
    (r : ℤ) (hr : 1 ≤ r) :
    (a).inv.hom r hr =
      ((L).mapSpectralObjectSpectralSequencePageIso Y data r hr).inv := rfl

/-- Canonical localization on the entire actual interval diagram, with
scalar restriction and all connecting-map commutation squares. -/
def secondTranslationBKModuleLocalization : Y ⟶ (Res).mapSpectralObject LY where
  hom n :=
    { app I := (ModuleCat.localizedModuleFunctorUnit T).app (((Y).H n).obj I)
      naturality := by
        intro I J f
        exact (ModuleCat.localizedModuleFunctorUnit T).naturality (((Y).H n).map f) }
  comm := by
    intro n₀ n₁ hn i j k f g
    exact (ModuleCat.localizedModuleFunctorUnit T).naturality ((Y).δ f g n₀ n₁ hn)

/-- Each component is exactly the canonical unit on the original interval. -/
@[simp]
theorem secondTranslationBKModuleLocalization_hom_app
    (n : ℤ) (I : ComposableArrows EInt 1) :
    ((secondTranslationBKModuleLocalization (C := C) R).hom n).app I =
      (ModuleCat.localizedModuleFunctorUnit T).app (((Y).H n).obj I) := rfl

/-- The actual localized second page is canonically isomorphic to the
accepted localized coefficient refinement in every natural bidegree. -/
def secondTranslationBKLocalizedModuleSecondPageCoefficientIso (p q : ℕ) :
    (((PB).page 2 (by omega)).X (p,q)) ≅
      localizedCoreTranslationActionCoefficientRefinement C R p q :=
  (HomologicalComplex.Hom.isoApp
      ((L).mapSpectralObjectSpectralSequencePageIso Y data 2 (by omega)) (p,q)).symm ≪≫
    (L).mapIso (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R p q)

local notation "Phi" => secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R
local notation "Gamma" => secondTranslationBKModuleSecondPageCoefficientIso (C := C) R

/-- Phi's forward map is the actual whole-comparison page inverse followed
by localization of the actual integral Gamma map. -/
theorem secondTranslationBKLocalizedModuleSecondPageCoefficientIso_hom (p q : ℕ) :
    (Phi p q).hom =
      ((a).inv.hom 2 (by omega)).f (p,q) ≫ (L).map (Gamma p q).hom := rfl

/-- Phi's inverse follows exactly the reverse canonical route. -/
theorem secondTranslationBKLocalizedModuleSecondPageCoefficientIso_inv (p q : ℕ) :
    (Phi p q).inv =
      (L).map (Gamma p q).inv ≫ ((a).hom.hom 2 (by omega)).f (p,q) := rfl

/-- The actual A-module page-localization square, with restriction of the
canonical whole-comparison component followed by Phi. -/
theorem secondTranslationBKLocalizedModuleSecondPageLocalizationSquare (p q : ℕ) :
    (Gamma p q).hom ≫
        (ModuleCat.localizedModuleFunctorUnit T).app
          (coreTranslationActionCoefficientHomology C R q p) =
      (ModuleCat.localizedModuleFunctorUnit T).app (((P).page 2 (by omega)).X (p,q)) ≫
        (Res).map (((a).hom.hom 2 (by omega)).f (p,q) ≫ (Phi p q).hom) := by
  let e := HomologicalComplex.Hom.isoApp
    ((L).mapSpectralObjectSpectralSequencePageIso Y data 2 (by omega)) (p,q)
  rw [secondTranslationBKLocalizedModuleSecondPageCoefficientIso_hom]
  change _ = (ModuleCat.localizedModuleFunctorUnit T).app _ ≫
    (Res).map (e.hom ≫ (e.inv ≫ (L).map (Gamma p q).hom))
  rw [Iso.hom_inv_id_assoc]
  exact (ModuleCat.localizedModuleFunctorUnit T).naturality (Gamma p q).hom


/-- After forgetting scalars, the left forward route is exactly the original
e2 comparison, kappa inverse and underlying localization map of Q. -/
theorem secondTranslationBKLocalizedModuleSecondPageLocalizationSquare_forget (p q : ℕ) :
    (secondTranslationBKModulePageForgetIso (C := C) R 2 (by omega)).hom.f (p,q) ≫
        (coreTranslationActionSecondPageIso C R p q).inv ≫
        ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map ((ModuleCat.localizedModuleFunctorUnit T).app
          (coreTranslationActionCoefficientHomology C R q p)) =
      ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map
        ((ModuleCat.localizedModuleFunctorUnit T).app (((P).page 2 (by omega)).X (p,q)) ≫
          (Res).map (((a).hom.hom 2 (by omega)).f (p,q) ≫ (Phi p q).hom)) := by
  calc
    _ = ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map ((Gamma p q).hom ≫
        (ModuleCat.localizedModuleFunctorUnit T).app
          (coreTranslationActionCoefficientHomology C R q p)) := by
      rw [Functor.map_comp, secondTranslationBKModuleSecondPageCoefficientIso_hom_forget,
        Category.assoc]
    _ = _ := congrArg (fun f => ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map f)
      (secondTranslationBKLocalizedModuleSecondPageLocalizationSquare (C := C) R p q)

/-- Apply localization to the accepted canonical stage comparison at every
complete filtration cut, using the actual LY interval as its source. -/
def secondTranslationBKLocalizedStageModuleIso (d : ℕ) (i : EInt) :
    ((LY).H (-(d : ℤ))).obj (secondTranslationBKStageInterval i) ≅
      (L).obj (secondTranslationBKStageHomologyModule (C := C) R d i) :=
  (L).mapIso (secondTranslationBKStageModuleIso (C := C) R d i)

/-- The forward stage map is exactly localization of the accepted map. -/
theorem secondTranslationBKLocalizedStageModuleIso_hom (d : ℕ) (i : EInt) :
    (secondTranslationBKLocalizedStageModuleIso (C := C) R d i).hom =
      (L).map (secondTranslationBKStageModuleIso (C := C) R d i).hom := rfl

/-- The inverse stage map is exactly localization of its accepted inverse. -/
theorem secondTranslationBKLocalizedStageModuleIso_inv (d : ℕ) (i : EInt) :
    (secondTranslationBKLocalizedStageModuleIso (C := C) R d i).inv =
      (L).map (secondTranslationBKStageModuleIso (C := C) R d i).inv := rfl

/-- The full bottom-to-top LY interval compares with the same literal total
homology module by localization of the accepted abutment comparison. -/
def secondTranslationBKLocalizedAbutmentModuleIso (d : ℕ) :
    ((LY).H (-(d : ℤ))).obj (secondTranslationBKStageInterval ⊤) ≅
      (L).obj (secondTranslationBKTotalHomologyModule (C := C) R d) :=
  (L).mapIso (secondTranslationBKAbutmentModuleIso (C := C) R d)

/-- The forward full abutment map is the mapped accepted map. -/
theorem secondTranslationBKLocalizedAbutmentModuleIso_hom (d : ℕ) :
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R d).hom =
      (L).map (secondTranslationBKAbutmentModuleIso (C := C) R d).hom := rfl

/-- Its inverse is the mapped accepted inverse. -/
theorem secondTranslationBKLocalizedAbutmentModuleIso_inv (d : ℕ) :
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R d).inv =
      (L).map (secondTranslationBKAbutmentModuleIso (C := C) R d).inv := rfl

/-- Every degree decomposition uses the accepted canonical interval and
the same total module in degree p+q, after localization. -/
def secondTranslationBKLocalizedCanonicalToTotalModuleIso (p q : ℕ) :
    ((LY).H (-((p + q : ℕ) : ℤ))).obj
        (ComposableArrows.mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≅
      (L).obj (secondTranslationBKTotalHomologyModule (C := C) R (p+q)) :=
  (L).mapIso (secondTranslationBKCanonicalToTotalModuleIso (C := C) R p q)

/-- The forward canonical total comparison is the mapped accepted map. -/
theorem secondTranslationBKLocalizedCanonicalToTotalModuleIso_hom (p q : ℕ) :
    (secondTranslationBKLocalizedCanonicalToTotalModuleIso (C := C) R p q).hom =
      (L).map (secondTranslationBKCanonicalToTotalModuleIso (C := C) R p q).hom := rfl

/-- The inverse canonical total comparison is its mapped accepted inverse. -/
theorem secondTranslationBKLocalizedCanonicalToTotalModuleIso_inv (p q : ℕ) :
    (secondTranslationBKLocalizedCanonicalToTotalModuleIso (C := C) R p q).inv =
      (L).map (secondTranslationBKCanonicalToTotalModuleIso (C := C) R p q).inv := rfl

/-- Actual LY interval maps correspond to localization of the accepted
linear transition maps between complete-stage homology modules. -/
theorem secondTranslationBKLocalizedStageModuleIso_naturality
    (d : ℕ) {i j : EInt} (h : i ≤ j) :
    ((LY).H (-(d : ℤ))).map (secondTranslationBKStageIntervalMap h) ≫
        (secondTranslationBKLocalizedStageModuleIso (C := C) R d j).hom =
      (secondTranslationBKLocalizedStageModuleIso (C := C) R d i).hom ≫
        (L).map (secondTranslationBKStageHomologyModuleMap (C := C) R d h) := by
  change (L).map (((Y).H (-(d : ℤ))).map (secondTranslationBKStageIntervalMap h)) ≫
      (L).map (secondTranslationBKStageModuleIso (C := C) R d j).hom =
    (L).map (secondTranslationBKStageModuleIso (C := C) R d i).hom ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [secondTranslationBKStageHomologyModuleMap, Iso.hom_inv_id_assoc]

/-- At every complete cut, the localized stage-to-total route is the actual
LY interval map to top followed by the mapped abutment comparison. -/
theorem secondTranslationBKLocalizedStageModuleIso_comp_toTotal (d : ℕ) (i : EInt) :
    (secondTranslationBKLocalizedStageModuleIso (C := C) R d i).hom ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d i) =
      ((LY).H (-(d : ℤ))).map
          (secondTranslationBKStageIntervalMap (show i ≤ ⊤ from le_top)) ≫
        (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R d).hom := by
  change (L).map (secondTranslationBKStageModuleIso (C := C) R d i).hom ≫
      (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d i) =
    (L).map (((Y).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap (show i ≤ ⊤ from le_top))) ≫
      (L).map (secondTranslationBKAbutmentModuleIso (C := C) R d).hom
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [secondTranslationBKStageToTotalModuleMap, Iso.hom_inv_id_assoc]

/-- Localization preserves the accepted compatibility of every complete
stage transition with its map to the one literal total module. -/
theorem secondTranslationBKLocalizedStageModuleMap_comp_toTotal
    (d : ℕ) {i j : EInt} (h : i ≤ j) :
    (L).map (secondTranslationBKStageHomologyModuleMap (C := C) R d h) ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d j) =
      (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R d i) := by
  rw [← Functor.map_comp, secondTranslationBKStageModuleMap_comp_toTotal]

end CategoryTheory.SInverseS

end
