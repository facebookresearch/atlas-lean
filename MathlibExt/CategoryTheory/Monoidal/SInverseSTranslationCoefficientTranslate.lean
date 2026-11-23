/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBaseAction

/-!
# Translation invariance of the core coefficient functor

Left translation of a base arrow preserves its stabilizer class.  Therefore
the core coefficient functor is canonically isomorphic to its precomposition
by base translation, with identity components.  The same comparison survives
objectwise localization, with the required functor reassociation.

This file does not construct the conjugated first-translation natural
transformation or pass to coefficient bars or Bousfield--Kan homology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Translating a base arrow preserves the skeleton class of its selected
stabilizer. -/
theorem translationStabilizerClass_translateFunctor_map
    (A : C) {B D : Translation C} (g : B ⟶ D) :
    translationStabilizerClass C
        ((Translation.translateFunctor A).map g) =
      translationStabilizerClass C g := by
  let T := Translation.translateFunctor A
  have hq : Translation.Hom.mk
        (Translation.representative (T.map g)) =
      Translation.Hom.mk ((Translation.representative g).translate A) := by
    calc
      _ = T.map g := Translation.mk_representative (T.map g)
      _ = T.map (Translation.Hom.mk
          (Translation.representative g)) := by
        rw [Translation.mk_representative]
      _ = _ := Translation.translateFunctor_map_mk A
        (Translation.representative g)
  obtain ⟨e, _⟩ := Quotient.exact hq
  simpa only [translationStabilizerClass_out, Translation.representative,
    Translation.RawHom.translate, T] using congr_toSkeleton_of_iso e

/-- The core coefficient functor is invariant under base translation, via
the identity isomorphism on its constant object value. -/
noncomputable def coreTranslationCoefficientTranslateNatIso
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    coreTranslationCoefficientFunctor C R q ≅
      Translation.translateFunctor A ⋙
        coreTranslationCoefficientFunctor C R q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro B D g
    change coreTranslationCoefficientMap C R q
          (translationStabilizerClass C g) =
        coreTranslationCoefficientMap C R q
          (translationStabilizerClass C
            ((Translation.translateFunctor A).map g))
    rw [translationStabilizerClass_translateFunctor_map])

@[simp]
theorem coreTranslationCoefficientTranslateNatIso_hom_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (coreTranslationCoefficientTranslateNatIso C R q A).hom.app B = 𝟙 _ :=
  rfl

@[simp]
theorem coreTranslationCoefficientTranslateNatIso_inv_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (coreTranslationCoefficientTranslateNatIso C R q A).inv.app B = 𝟙 _ :=
  rfl

/-- Translation invariance after objectwise localization, rebracketed so
the translated localized coefficient functor is the target. -/
noncomputable def localizedCoreTranslationCoefficientTranslateNatIso
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    coreTranslationCoefficientFunctor C R q ⋙
        ModuleCat.localizedModuleFunctor
          (coreTranslationDenominators C) ≅
      Translation.translateFunctor A ⋙
        (coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)) :=
  Functor.isoWhiskerRight
      (coreTranslationCoefficientTranslateNatIso C R q A)
      (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C)) ≪≫
    Functor.associator
      (Translation.translateFunctor A)
      (coreTranslationCoefficientFunctor C R q)
      (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C))

@[simp]
theorem localizedCoreTranslationCoefficientTranslateNatIso_hom_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedCoreTranslationCoefficientTranslateNatIso
      C R q A).hom.app B = 𝟙 _ := by
  change
    (ModuleCat.localizedModuleFunctor
      (coreTranslationDenominators C)).map (𝟙 _) = 𝟙 _
  exact (ModuleCat.localizedModuleFunctor
    (coreTranslationDenominators C)).map_id _

@[simp]
theorem localizedCoreTranslationCoefficientTranslateNatIso_inv_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedCoreTranslationCoefficientTranslateNatIso
      C R q A).inv.app B = 𝟙 _ := by
  change
    (ModuleCat.localizedModuleFunctor
      (coreTranslationDenominators C)).map (𝟙 _) = 𝟙 _
  exact (ModuleCat.localizedModuleFunctor
    (coreTranslationDenominators C)).map_id _

end SInverseS
end CategoryTheory

end
