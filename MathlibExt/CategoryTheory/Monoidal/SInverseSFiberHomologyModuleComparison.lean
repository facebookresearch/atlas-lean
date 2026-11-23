/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberCoefficient
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberHomology

/-!
# Module-valued core action versus strict-fiber homology

The skeleton monoid-algebra action on core homology defines a
constant-object module-valued functor on the translation category.  After
forgetting module structure, it is naturally isomorphic to the strict-fiber
homology coefficient functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Core homology with its skeleton monoid-algebra module structure, as a
module-category object. -/
noncomputable abbrev coreTranslationHomologyModuleCat
    (R : AddCommGrpCat.{u}) (n : ℕ) :=
  ModuleCat.of (coreTranslationRing C)
    (coreTranslationHomologyModule C R n)

/-- Scalar multiplication by a skeleton monomial as a morphism of the core
homology module. -/
noncomputable def coreTranslationCoefficientMap
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    coreTranslationHomologyModuleCat C R n ⟶
      coreTranslationHomologyModuleCat C R n :=
  ModuleCat.ofHom (LinearMap.lsmul
    (coreTranslationRing C) (coreTranslationHomologyModule C R n)
    (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
      (Multiplicative.ofAdd x)))

/-- Before localization, translation arrows act by their stabilizer
monomials on the constant core-homology module. -/
noncomputable def coreTranslationCoefficientFunctor
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) where
  obj _ := coreTranslationHomologyModuleCat C R n
  map f := coreTranslationCoefficientMap C R n
    (translationStabilizerClass C f)
  map_id B := by
    rw [translationStabilizerClass_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
      (Multiplicative.ofAdd 0)) • z = z
    rw [ofAdd_zero, map_one, one_smul]
  map_comp f g := by
    rw [translationStabilizerClass_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd
          (translationStabilizerClass C f +
            translationStabilizerClass C g))) • z =
      (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd (translationStabilizerClass C g))) •
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd (translationStabilizerClass C f))) • z
    rw [ofAdd_add, map_mul, ← mul_smul, mul_comm]

@[simp]
theorem coreTranslationCoefficientFunctor_obj
    (R : AddCommGrpCat.{u}) (n : ℕ) (B : Translation C) :
    (coreTranslationCoefficientFunctor C R n).obj B =
      coreTranslationHomologyModuleCat C R n :=
  rfl

@[simp]
theorem coreTranslationCoefficientFunctor_map
    (R : AddCommGrpCat.{u}) (n : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    (coreTranslationCoefficientFunctor C R n).map f =
      coreTranslationCoefficientMap C R n
        (translationStabilizerClass C f) :=
  rfl

/-- Forgetting the monoid-algebra module recovers the original core homology
group. -/
noncomputable def coreTranslationHomologyModuleAddCommGrpIso
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationHomologyModuleCat C R n) ≅
      (nerve (Core C)).homology R n :=
  by
    change AddCommGrpCat.of (coreTranslationHomologyModule C R n) ≅
      (nerve (Core C)).homology R n
    exact (coreTranslationHomologyModuleEquiv C R n).toAddEquiv.toAddCommGrpIso

/-- The module-action map followed by the underlying core-homology
identification is the core-translation homology map. -/
@[reassoc]
theorem coreTranslationCoefficientMap_comp_moduleIso_hom
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R n x) ≫
        (coreTranslationHomologyModuleAddCommGrpIso C R n).hom =
      (coreTranslationHomologyModuleAddCommGrpIso C R n).hom ≫
        coreTranslationHomologyMap C R n x := by
  apply ConcreteCategory.hom_ext
  intro z
  change coreTranslationHomologyModule C R n at z
  change coreTranslationHomologyModuleEquiv C R n
      (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x) • z) =
    (coreTranslationHomologyMap C R n x).hom
        (coreTranslationHomologyModuleEquiv C R n z)
  exact coreTranslationHomologyModuleEquiv_monomial_smul C R n _ z

/-- Functor-map form of the module-action/core-homology comparison. -/
theorem coreTranslationCoefficientFunctor_map_comp_moduleIso_hom
    (R : AddCommGrpCat.{u}) (n : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          ((coreTranslationCoefficientFunctor C R n).map f) ≫
        (coreTranslationHomologyModuleAddCommGrpIso C R n).hom =
      (coreTranslationHomologyModuleAddCommGrpIso C R n).hom ≫
        coreTranslationHomologyMap C R n
          (translationStabilizerClass C f) :=
  coreTranslationCoefficientMap_comp_moduleIso_hom C R n _

/-- Component comparing the underlying core-action module with strict-fiber
homology. -/
noncomputable def coreTranslationCoefficientFiberIsoApp
    (R : AddCommGrpCat.{u}) (n : ℕ) (B : Translation C) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        ((coreTranslationCoefficientFunctor C R n).obj B) ≅
      (Functor.IsCofibered.fiberHomologyFunctor
        (p := translationProjection (C := C))
        AddCommGrpCat.{u} R n).obj B :=
  by
    change (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationHomologyModuleCat C R n) ≅
      (nerve (TranslationFiber (⟨B.of⟩ : Core C))).homology R n
    exact (coreTranslationHomologyModuleAddCommGrpIso C R n).trans
      (coreTranslationFiberHomologyIso C B R n)

@[simp]
theorem coreTranslationCoefficientFiberIsoApp_hom
    (R : AddCommGrpCat.{u}) (n : ℕ) (B : Translation C) :
    (coreTranslationCoefficientFiberIsoApp C R n B).hom =
      (coreTranslationHomologyModuleAddCommGrpIso C R n).hom ≫
        (coreTranslationFiberHomologyIso C B R n).hom := by
  rcases B with ⟨B⟩
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the module/fiber homology comparison. -/
theorem coreTranslationCoefficientFiberIsoApp_naturality
    (R : AddCommGrpCat.{u}) (n : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          ((coreTranslationCoefficientFunctor C R n).map f) ≫
        (coreTranslationCoefficientFiberIsoApp C R n T).hom =
      (coreTranslationCoefficientFiberIsoApp C R n B).hom ≫
        (Functor.IsCofibered.fiberHomologyFunctor
          (p := translationProjection (C := C))
          AddCommGrpCat.{u} R n).map f := by
  rcases B with ⟨B⟩
  rcases T with ⟨T⟩
  dsimp only [coreTranslationCoefficientFunctor]
  have hConj :
      coreTranslationHomologyMap C R n
            (translationStabilizerClass C f) ≫
          (coreTranslationFiberHomologyIso C
            (⟨T⟩ : Translation C) R n).hom =
        (coreTranslationFiberHomologyIso C
          (⟨B⟩ : Translation C) R n).hom ≫
          (Functor.IsCofibered.fiberHomologyFunctor
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} R n).map f := by
    rw [translationStabilizerClass_out,
      coreTranslationHomologyMap_toSkeleton]
    exact (coreTranslationFiberHomologyIso_hom_naturality
      C f R n).symm
  rw [coreTranslationCoefficientFiberIsoApp_hom,
    coreTranslationCoefficientFiberIsoApp_hom]
  rw [coreTranslationCoefficientMap_comp_moduleIso_hom_assoc]
  rw [Category.assoc, hConj, ← Category.assoc]

/-- The module-valued skeleton action, after forgetting scalars, is the
strict-fiber homology coefficient system. -/
noncomputable def coreTranslationCoefficientFiberNatIso
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    coreTranslationCoefficientFunctor C R n ⋙
        forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u} ≅
      Functor.IsCofibered.fiberHomologyFunctor
        (p := translationProjection (C := C))
        AddCommGrpCat.{u} R n :=
  NatIso.ofComponents
    (coreTranslationCoefficientFiberIsoApp C R n)
    (fun f => coreTranslationCoefficientFiberIsoApp_naturality C R n f)

end SInverseS
end CategoryTheory

end
