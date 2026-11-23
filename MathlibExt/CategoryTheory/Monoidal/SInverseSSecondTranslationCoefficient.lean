/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCostructuredCoefficientComparison
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCommaFiber

/-!
# Second translation on right-comma homology coefficients

Under the natural comparison from right-comma homology to the underlying
additive group of the core translation coefficient module, fiberwise
second-coordinate translation is scalar multiplication by the skeleton
monomial of the added object.

Only the explicit comparison isomorphisms are cancelled.  In particular,
this file makes no cancellation, localization, or invertibility claim about
the coefficient monomial itself.
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

/-- Fiberwise second-coordinate translation on right-comma homology is
conjugate to the underlying core-coefficient monomial map for the added
object's skeleton class. -/
theorem secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) := by
  have hFiberInv :
      (coreTranslationCoefficientFiberIsoApp C R q B).inv ≫
          (coreTranslationHomologyModuleAddCommGrpIso C R q).hom =
        (coreTranslationFiberHomologyIso C B R q).inv := by
    apply (cancel_mono
      (coreTranslationFiberHomologyIso C B R q).hom).1
    simp only [Category.assoc,
      ← coreTranslationCoefficientFiberIsoApp_hom C R q B,
      Iso.inv_hom_id]
  have hAction :=
    coreTranslationCoefficientMap_comp_moduleIso_hom
      C R q (toSkeleton A)
  apply (cancel_mono
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom).1
  simp only [costructuredCoreTranslationCoefficientNatIso_hom_app]
  calc
    (SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R q ≫
        ((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationCoefficientFiberIsoApp C R q B).inv)) ≫
        (coreTranslationHomologyModuleAddCommGrpIso C R q).hom =
      SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R q ≫
        ((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationFiberHomologyIso C B R q).inv) := by
      let f := SSet.homologyMap
        (nerveMap (secondTranslationCostructuredMap A B)) R q
      let e := Functor.IsCofibered.costructuredFiberHomologyIso
        (p := translationProjection (C := C)) AddCommGrpCat.{u} B R q
      let i := coreTranslationCoefficientFiberIsoApp C R q B
      let c := coreTranslationHomologyModuleAddCommGrpIso C R q
      let j := coreTranslationFiberHomologyIso C B R q
      have h : i.inv ≫ c.hom = j.inv := hFiberInv
      change (f ≫ (e.hom ≫ i.inv)) ≫ c.hom = f ≫ (e.hom ≫ j.inv)
      exact (Category.assoc f (e.hom ≫ i.inv) c.hom).trans
        ((congrArg (fun t => f ≫ t) (Category.assoc e.hom i.inv c.hom)).trans
          (congrArg (fun t => f ≫ (e.hom ≫ t)) h))
    _ = ((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationFiberHomologyIso C B R q).inv) ≫
        coreTranslationHomologyMap C R q (toSkeleton A) :=
      secondTranslationCostructured_homologyMap_comp_coreComparison
        C R A B q
    _ = ((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationCoefficientFiberIsoApp C R q B).inv) ≫
        ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
          coreTranslationHomologyMap C R q (toSkeleton A)) := by
      rw [← hFiberInv]
      simp only [Category.assoc]
    _ = ((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationCoefficientFiberIsoApp C R q B).inv) ≫
        ((forget₂ (ModuleCat.{u} (coreTranslationRing C))
            AddCommGrpCat.{u}).map
              (coreTranslationCoefficientMap C R q (toSkeleton A)) ≫
          (coreTranslationHomologyModuleAddCommGrpIso C R q).hom) := by
      rw [hAction]
    _ = (((Functor.IsCofibered.costructuredFiberHomologyIso
            (p := translationProjection (C := C))
            AddCommGrpCat.{u} B R q).hom ≫
          (coreTranslationCoefficientFiberIsoApp C R q B).inv) ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C))
          AddCommGrpCat.{u}).map
            (coreTranslationCoefficientMap C R q (toSkeleton A))) ≫
        (coreTranslationHomologyModuleAddCommGrpIso C R q).hom :=
      (Category.assoc _ _ _).symm

end SInverseS
end CategoryTheory

end
