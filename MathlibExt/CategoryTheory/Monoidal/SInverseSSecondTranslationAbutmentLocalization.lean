/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnit
public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnitIso
public import MathlibExt.Algebra.Homology.QuasiIsoNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotalNaturality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSGroupCompletionSpectralSequence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationLocalization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModuleAbutment
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTotalTranslationAction

/-!
# Fixed-base second translation and literal BK total localization

The actual second translation of the fixed right-comma diagram commutes with
its original source augmentation. Across the inverse diagonal-total abutment
comparison, it is the inverse of first translation on pair homology. Thus all
skeleton monomials act bijectively on the existing literal signed-total module.
Its canonical localization has the same underlying group, with the actual
scalar-restricted localization unit followed by the comparison equal to identity.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

universe u

local instance secondTranslationAbutmentLocalizationHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

namespace CategoryTheory.SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Fixed-base second translation commutes with the original signed-total
source abutment comparison in every natural degree. -/
theorem secondTranslationBKAbutmentHomologySquare
    (R : AddCommGrpCat.{u}) (W : C) (n : ℕ) :
    HomologicalComplex.homologyMap
        (secondTranslationBKTotalComplexMap R W) n ≫
      (translationBKAbutmentHomologyIso C R n).hom =
    (translationBKAbutmentHomologyIso C R n).hom ≫
      pairSecondTranslationHomologyMap C R n W := by
  let F := translationProjection (C := C)
  let D := SSet.rightCommaNerveDiagram F
  let α := secondTranslationRightCommaNerveDiagramNatTrans W
  let τ := SSet.rightCommaProjection F
  let u := nerveMap (translateSecondFunctor W)
  have hτ (b : Translation C) : α.app b ≫ τ.app b = τ.app b ≫ u := by
    ext k x
    rfl
  have haug : SSet.bkHocolimMap α ≫ SSet.rightCommaTotalToSource F =
      SSet.rightCommaTotalToSource F ≫ u :=
    SSet.bkAugmentation_naturality α τ τ u hτ
  let c : (SSet.bkHocolim D).chainComplex R ⟶ (SSet.bkHocolim D).chainComplex R :=
    SSet.chainComplexMap (SSet.bkHocolimMap α) R
  let f : (SSet.bkHocolim D).chainComplex R ⟶ (nerve (Pair C)).chainComplex R :=
    SSet.chainComplexMap (SSet.rightCommaTotalToSource F) R
  let t : (nerve (Pair C)).chainComplex R ⟶ (nerve (Pair C)).chainComplex R :=
    SSet.chainComplexMap u R
  let v := secondTranslationBKTotalComplexMap R W
  have hcf : c ≫ f = f ≫ t := by
    change ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R).map
        (SSet.bkHocolimMap α) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R).map
        (SSet.rightCommaTotalToSource F) =
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R).map
        (SSet.rightCommaTotalToSource F) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R).map u
    rw [← Functor.map_comp, ← Functor.map_comp, haug]
  let _ : QuasiIso f :=
    SSet.rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp R F
  let d : ((SSet.bkHocolim D).chainComplex R).homology n ≅
      (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R D).homology n :=
    SSet.bkDiagonalTotalHomologyIso R D n
  let i : ((SSet.bkHocolim D).chainComplex R).homology n ≅
      ((nerve (Pair C)).chainComplex R).homology n := isoOfQuasiIsoAt f n
  have hQ := HomologicalComplex.isoOfQuasiIsoAt_naturality f f c t n hcf
  change HomologicalComplex.homologyMap c n ≫ i.hom =
    i.hom ≫ pairSecondTranslationHomologyMap C R n W at hQ
  have hD := SSet.bkDiagonalTotalHomologyIso_naturality R α n
  change HomologicalComplex.homologyMap c n ≫ d.hom =
    d.hom ≫ HomologicalComplex.homologyMap v n at hD
  have hDinv : HomologicalComplex.homologyMap v n ≫ d.inv =
      d.inv ≫ HomologicalComplex.homologyMap c n := by
    have h := congrArg (fun k => d.inv ≫ k ≫ d.inv) hD
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h.symm
  change HomologicalComplex.homologyMap v n ≫ (d.inv ≫ i.hom) =
    (d.inv ≫ i.hom) ≫ pairSecondTranslationHomologyMap C R n W
  calc
    HomologicalComplex.homologyMap v n ≫ (d.inv ≫ i.hom) =
        (d.inv ≫ HomologicalComplex.homologyMap c n) ≫ i.hom := by
      rw [← Category.assoc, hDinv]
    _ = (d.inv ≫ i.hom) ≫ pairSecondTranslationHomologyMap C R n W := by
      rw [Category.assoc, hQ, ← Category.assoc]

/-- Every denominator acts bijectively on the existing literal total module
with its original second-translation scalars. -/
theorem secondTranslationBKTotalHomologyModule_denominator_bijective
    (R : AddCommGrpCat.{u}) (n : ℕ) (s : coreTranslationDenominators C) :
    Function.Bijective
      (fun x : secondTranslationBKTotalHomologyModule (C := C) R n =>
        (s : coreTranslationRing C) • x) := by
  obtain ⟨m, hm⟩ := MonoidHom.mem_mrange.mp s.property
  let W := m.toAdd.out
  have hW : Multiplicative.ofAdd (toSkeleton W) = m :=
    congrArg Multiplicative.ofAdd (toSkeleton_fromSkeleton_obj m.toAdd)
  let β := translationBKAbutmentHomologyIso C R n
  let J : ((nerve (Pair C)).chainComplex R).homology n ≅
      ((nerve (Pair C)).chainComplex R).homology n :=
    pairTranslationHomologyIsoOfObject C R n W
  let e := β ≪≫ J.symm ≪≫ β.symm
  have hconj : HomologicalComplex.homologyMap
        (secondTranslationBKTotalComplexMap R W) n =
      (β.hom ≫ J.inv) ≫ β.inv := by
    have hsq : HomologicalComplex.homologyMap
        (secondTranslationBKTotalComplexMap R W) n ≫ β.hom = β.hom ≫ J.inv :=
      secondTranslationBKAbutmentHomologySquare C R W n
    have h := congrArg (fun k => k ≫ β.inv) hsq
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have he : HomologicalComplex.homologyMap
      (secondTranslationBKTotalComplexMap R W) n = e.hom := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hconj
  have hbij : Function.Bijective
      (fun x : secondTranslationBKTotalHomologyModule (C := C) R n =>
        HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) n x) := by
    rw [he]
    exact e.addCommGroupIsoToAddEquiv.bijective
  have hscalar (x : secondTranslationBKTotalHomologyModule (C := C) R n) :
      (s : coreTranslationRing C) • x =
        HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) n x := by
    rw [← hm, MonoidAlgebra.of_apply]
    have h := secondTranslationBKTotalHomologyModule_single_apply R n W 1 x
    rw [hW, one_zsmul] at h
    exact h
  have hfun :
      (fun x : secondTranslationBKTotalHomologyModule (C := C) R n =>
        (s : coreTranslationRing C) • x) =
      (fun x : secondTranslationBKTotalHomologyModule (C := C) R n =>
        HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) n x) :=
    funext hscalar
  rw [hfun]
  exact hbij

/-- The canonical localized literal total module has its original underlying
additive group when all denominator actions are already bijective. -/
def secondTranslationBKTotalHomologyLocalizationUnderlyingIso
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{u}).obj
      ((ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n)) ≅
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n) :=
  ModuleCat.localizedModuleAddCommGrpIsoOfBijectiveSmul (coreTranslationDenominators C)
    (secondTranslationBKTotalHomologyModule (C := C) R n)
    (secondTranslationBKTotalHomologyModule_denominator_bijective C R n)

/-- The actual scalar-restricted canonical localization unit followed by the
constructed underlying comparison is identity on the same literal group. -/
theorem secondTranslationBKTotalHomologyLocalizationUnderlyingIso_unit_hom
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
      ((ModuleCat.localizedModuleFunctorUnit (coreTranslationDenominators C)).app
        (secondTranslationBKTotalHomologyModule (C := C) R n)) ≫
      (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R n).hom =
    𝟙 ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n)) := by
  ext x
  change (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R n).hom
      (ModuleCat.Hom.hom
        (A := secondTranslationBKTotalHomologyModule (C := C) R n)
        (B := (ModuleCat.restrictScalars
          (algebraMap (coreTranslationRing C)
            (Localization (coreTranslationDenominators C)))).obj
              ((ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)).obj
                (secondTranslationBKTotalHomologyModule (C := C) R n)))
        ((ModuleCat.localizedModuleFunctorUnit (coreTranslationDenominators C)).app
          (secondTranslationBKTotalHomologyModule (C := C) R n)) x) = x
  rw [ModuleCat.localizedModuleFunctorUnit_app_apply]
  exact ModuleCat.localizedModuleAddCommGrpIsoOfBijectiveSmul_hom_mk (coreTranslationDenominators C)
    (secondTranslationBKTotalHomologyModule (C := C) R n)
    (secondTranslationBKTotalHomologyModule_denominator_bijective C R n) x

end CategoryTheory.SInverseS

end
