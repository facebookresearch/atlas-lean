/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowStableHomology
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoreZeroGradeHomology

/-!
# The actual finite-row comparison in intrinsic zero-grade coordinates

The already derived zero-grade isomorphism puts the actual stable homology
comparison into the independently defined subgroup of correctly graded
fractions. Each original finite-stage class is the original core numerator
divided by the same regular denominator power. Its whole comparison square
and its literal underlying fraction are both recorded in every degree.

No finite-stage image, stable-freeness, or homology-isomorphism premise is
supplied. Eventual representation and equality are still needed to prove
that the actual finite-stage colimit map is invertible.
-/

noncomputable section

open CategoryTheory Limits Algebra

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The actual finite-stage homology colimit comparison in the independently
defined intrinsic zero subgroup. The coordinate change is the already
derived generic zero-grade Iso, rather than a hypothesis about this map. -/
public def finiteFreeRowIntrinsicHomologyComparison (A : AddCommGrpCat.{u}) (q : ℕ) :
    colimit (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) ⟶
      AddCommGrpCat.of
        (SInverseS.zeroLocalizedCoreSubgroup (C := FGProjectiveCat.IdempotentModel R) A q) :=
  finiteFreeRowHomologyColimitComparison R A q ≫
    (SInverseS.zeroLocalizedCoreHomologyIso
      (C := FGProjectiveCat.IdempotentModel R) A q).inv

/-- The whole intrinsic comparison followed by the established zero-grade
Iso is the SAME actual finite-stage colimit map, in every degree. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_comp_homologyIso
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    finiteFreeRowIntrinsicHomologyComparison R A q ≫
        (SInverseS.zeroLocalizedCoreHomologyIso
          (C := FGProjectiveCat.IdempotentModel R) A q).hom =
      finiteFreeRowHomologyColimitComparison R A q := by
  let e := SInverseS.zeroLocalizedCoreHomologyIso
    (C := FGProjectiveCat.IdempotentModel R) A q
  change (finiteFreeRowHomologyColimitComparison R A q ≫ e.inv) ≫ e.hom = _
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Every original finite-stage injection retains the actual row zero map
followed by the same generic inverse coordinate change. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_ι
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
        finiteFreeRowIntrinsicHomologyComparison R A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q ≫
        (SInverseS.zeroLocalizedCoreHomologyIso
          (C := FGProjectiveCat.IdempotentModel R) A q).inv := by
  let e := SInverseS.zeroLocalizedCoreHomologyIso
    (C := FGProjectiveCat.IdempotentModel R) A q
  change colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
      (finiteFreeRowHomologyColimitComparison R A q ≫ e.inv) = _
  exact ((Category.assoc _ _ _).symm).trans
    (congrArg (fun f => f ≫ e.inv)
      (finiteFreeRowHomologyColimitComparison_ι R A q n))

/-- The value of every ORIGINAL finite-stage class is precisely its original
core numerator over the SAME regular denominator power. No imported data
definition is unfolded and the intrinsic subgroup is unchanged. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_ι_val
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    ((finiteFreeRowIntrinsicHomologyComparison R A q
      (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q) n x)).val :
      CategoryTheory.SInverseS.localizedCoreTranslationHomology
        (FGProjectiveCat.IdempotentModel R) A q) =
      LocalizedModule.mk
        (R := CategoryTheory.SInverseS.coreTranslationRing
          (FGProjectiveCat.IdempotentModel R))
        (S := CategoryTheory.SInverseS.coreTranslationDenominators
          (FGProjectiveCat.IdempotentModel R))
        (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
          (FGProjectiveCat.IdempotentModel R) A q)
        (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q)
        ((finiteFreeRowRegularDenominator R) ^ n) := by
  let C := FGProjectiveCat.IdempotentModel R
  let e := SInverseS.zeroLocalizedCoreHomologyIso (C := C) A q
  let E := SInverseS.secondTranslationBKLocalizedCoreHomologyIso (C := C) A q ≪≫
    SInverseS.swapHomologyIso (C := C) A q
  let J := SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (SInverseS.zeroComponentProperty (C := C)).ι) A q
  let y := SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q x
  let z : SInverseS.localizedWholeCoreHomologyGroup (C := C) A q :=
    LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q).inv
        (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x)) :
        CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
          (FGProjectiveCat.IdempotentModel R) A q)
      ((finiteFreeRowRegularDenominator R) ^ n)
  have hs : finiteFreeRowIntrinsicHomologyComparison R A q
      (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q) n x) =
        e.inv y :=
    ConcreteCategory.congr_hom (finiteFreeRowIntrinsicHomologyComparison_ι R A q n) x
  have he : (e.inv y).val = E.inv (J y) :=
    SInverseS.zeroLocalizedCoreHomologyIso_inv_val (C := C) A q y
  have hf : E.hom z = J y := by
    have h := finiteFreeRowStageHomology_fraction_characteristic R A q n x
    have hcomp := ConcreteCategory.congr_hom
      ((SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q).map_comp (finiteFreeRowStageZeroNerveMap R n)
        (nerveMap (SInverseS.zeroComponentProperty (C := C)).ι)) x
    exact h.trans hcomp
  change _ = z
  calc
    _ = (e.inv y).val := congrArg Subtype.val hs
    _ = E.inv (J y) := he
    _ = E.inv (E.hom z) := congrArg E.inv hf.symm
    _ = z := Iso.hom_inv_id_apply E z

/-- The original regular finite-stage fraction belongs to the intrinsic
zero subgroup, with membership derived from its actual comparison value. -/
public theorem finiteFreeRowStageFraction_mem_zeroLocalizedCoreSubgroup
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q)
        ((finiteFreeRowRegularDenominator R) ^ n) ∈
      SInverseS.zeroLocalizedCoreSubgroup (C := FGProjectiveCat.IdempotentModel R) A q := by
  let z := finiteFreeRowIntrinsicHomologyComparison R A q
    (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n x)
  have hz := finiteFreeRowIntrinsicHomologyComparison_ι_val R A q n x
  exact hz ▸ z.property

end AlgebraicKTheory.StableGL
