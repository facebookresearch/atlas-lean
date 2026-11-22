/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Levels
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Source

/-!
# Whole original standard RIGHT free level and full J source characteristics
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed
namespace PointedCGWH.OriginalStandardRightFreeLevelSource

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

open OriginalStandardRightFreeLevels

section EndpointTransport
universe uS vS uC vC uD vD uP vP
variable {S : Type uS} [Category.{vS} S] {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {P : Type uP} [Category.{vP} P]

private theorem mprValue_heq {α β : Sort uP} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private def rawCoefficientIso (E : C ≌ D) (L : S ⥤ D) (Ev : D ⥤ P) :
    (L ⋙ E.inverse) ⋙ (E.functor ⋙ Ev) ≅ L ⋙ Ev :=
  Functor.associator L E.inverse (E.functor ⋙ Ev) ≪≫
    Functor.isoWhiskerLeft L (Functor.associator E.inverse E.functor Ev).symm ≪≫
      Functor.isoWhiskerLeft L (Functor.isoWhiskerRight E.counitIso Ev) ≪≫
        Functor.isoWhiskerLeft L (Functor.leftUnitor Ev)

private theorem rawCoefficientIso_hom (E : C ≌ D) (L : S ⥤ D) (Ev : D ⥤ P) (X : S) :
    (rawCoefficientIso E L Ev).hom.app X = Ev.map (E.counitIso.hom.app (L.obj X)) := by
  unfold rawCoefficientIso
  change 𝟙 _ ≫ 𝟙 _ ≫ Ev.map (E.counitIso.hom.app (L.obj X)) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]

private theorem rawCoefficientIso_inv (E : C ≌ D) (L : S ⥤ D) (Ev : D ⥤ P) (X : S) :
    (rawCoefficientIso E L Ev).inv.app X = Ev.map (E.counitIso.inv.app (L.obj X)) := by
  unfold rawCoefficientIso
  change ((𝟙 _ ≫ Ev.map (E.counitIso.inv.app (L.obj X))) ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id]

private theorem natIsoHomApp_heq {F G H : S ⥤ P} (q : F ≅ H) (r : G ≅ H)
    (hFG : F = G) (h : HEq q r) (X : S) : HEq (q.hom.app X) (r.hom.app X) := by
  cases hFG
  cases (eq_of_heq h)
  rfl

private theorem natIsoInvApp_heq {F G H : S ⥤ P} (q : F ≅ H) (r : G ≅ H)
    (hFG : F = G) (h : HEq q r) (X : S) : HEq (q.inv.app X) (r.inv.app X) := by
  cases hFG
  cases (eq_of_heq h)
  rfl

private theorem map_heq (Ev : D ⥤ P) {X X' Y Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') (h : HEq f g) : HEq (Ev.map f) (Ev.map g) := by
  cases hX
  cases hY
  cases (eq_of_heq h)
  rfl

private theorem iso_heq_of_hom {X X' Y : P} (q : X ≅ Y) (r : X' ≅ Y)
    (hX : X = X') (h : HEq q.hom r.hom) : HEq q r := by
  cases hX
  apply heq_of_eq
  apply Iso.ext
  exact eq_of_heq h

private theorem iso_eq_of_heq {X X' Y : P} (q : X ≅ Y) (r : X' ≅ Y)
    (hX : X = X') (h : HEq q r) : q = eqToIso hX ≪≫ r := by
  cases hX
  cases (eq_of_heq h)
  exact (Iso.refl_trans _).symm

private theorem eqIsoApp_heq {F G : S ⥤ P} (h : F = G) (X : S) :
    HEq ((eqToIso h).app X) (Iso.refl (G.obj X)) := by
  cases h
  rfl

private theorem eqIsoApp_eq {F G : S ⥤ P} (h : F = G) (X : S) :
    (eqToIso h).app X = eqToIso (congrArg (fun F => F.obj X) h) := by
  cases h
  rfl

private theorem commonValue_hom {X Y Z : P} (q : X ≅ Z) (r : Y ≅ Z)
    (hX : X = Z) (hY : Y = Z) (hq : HEq q (Iso.refl Z)) (hr : HEq r (Iso.refl Z)) :
    HEq (q ≪≫ r.symm).hom (𝟙 Z) := by
  cases hX
  cases hY
  cases (eq_of_heq hq)
  cases (eq_of_heq hr)
  exact heq_of_eq (Category.id_comp _)

private theorem rebaseIso {X X' Y : P} (q : X ≅ Y) (r : X' ≅ Y) (v : X' ≅ X)
    (hX : X' = X) (hv : HEq v (Iso.refl X)) (h : HEq q r) : q = v.symm ≪≫ r := by
  cases hX
  cases (eq_of_heq hv)
  cases (eq_of_heq h)
  exact (Iso.refl_trans _).symm

private theorem natIso_square {F G : C ⥤ P} (i : F ≅ G) {X Y : C} (q : X ≅ Y) :
    G.mapIso q ≪≫ (i.app Y).symm = (i.app X).symm ≪≫ F.mapIso q := by
  apply Iso.ext
  exact i.inv.naturality q.hom

private theorem natIso_square_tail {F G : C ⥤ P} (i : F ≅ G) {X Y : C} (q : X ≅ Y)
    {Z : P} (r : F.obj Y ≅ Z) :
    G.mapIso q ≪≫ (i.app Y).symm ≪≫ r =
      (i.app X).symm ≪≫ F.mapIso q ≪≫ r := by
  simpa only [Iso.trans_assoc] using congrArg (fun j => j ≪≫ r) (natIso_square i q)

private theorem natIso_conjugate {F G : C ⥤ P} (i : F ≅ G) {X Y : C} (q : X ≅ Y) :
    (i.app X).symm ≪≫ F.mapIso q ≪≫ i.app Y = G.mapIso q := by
  have h : F.mapIso q ≪≫ i.app Y = i.app X ≪≫ G.mapIso q :=
    Iso.ext (i.hom.naturality q.hom)
  rw [h, Iso.symm_self_id_assoc]

private theorem natIso_conjugate_tail {F G : C ⥤ P} (i : F ≅ G) {X Y : C} (q : X ≅ Y)
    {Z : P} (r : G.obj Y ≅ Z) :
    (i.app X).symm ≪≫ F.mapIso q ≪≫ i.app Y ≪≫ r = G.mapIso q ≪≫ r := by
  simpa only [Iso.trans_assoc] using congrArg (fun j => j ≪≫ r) (natIso_conjugate i q)

private theorem natIsoApp_heq {F G H : S ⥤ P} (q : F ≅ H) (r : G ≅ H)
    (hFG : F = G) (h : HEq q r) (X : S) : HEq (q.app X) (r.app X) := by
  cases hFG
  cases (eq_of_heq h)
  rfl

end EndpointTransport

private theorem coefficientSource_eq (e n : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.nativeFreeFunctor.{u, v} e ⋙
      SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor.{u, v} n =
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e) ⋙
            SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse) ⋙
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor ⋙
            EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} n)) := by
  rw [SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq,
    SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq]
  rfl

private theorem coefficientInitializer_heq (e n : Operad.SmallFinBijGroupoid) :
    HEq (nativeCoefficientIso.{u, v} e n)
      (rawCoefficientIso
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e))
        (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} n))) := by
  unfold nativeCoefficientIso rawCoefficientIso
  exact (mprValue_heq _ _).trans (mprValue_heq _ _)

/-- The complete original native coefficient hom is evaluation of the same actual counit. -/
theorem nativeCoefficientIso_hom_value (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((nativeCoefficientIso e n).hom.app X)
      ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).map
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso.hom.app
            ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} e)).obj X))) :=
  (natIsoHomApp_heq _ _ (coefficientSource_eq e n) (coefficientInitializer_heq e n) X).trans
    (heq_of_eq (rawCoefficientIso_hom _ _ _ X))

/-- The complete original inverse coefficient map evaluates the original inverse counit. -/
theorem nativeCoefficientIso_inv_value (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((nativeCoefficientIso e n).inv.app X)
      ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).map
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso.inv.app
            ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} e)).obj X))) :=
  (natIsoInvApp_heq _ _ (coefficientSource_eq e n) (coefficientInitializer_heq e n) X).trans
    (heq_of_eq (rawCoefficientIso_inv _ _ _ X))

/-- Actual full J counit evaluation has the same complete original coefficient hom value. -/
theorem nativeOperatorFreeIso_evaluation_hom (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).map ((nativeOperatorFreeIso e).hom.app X))
      ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).map
          (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso.hom.app
            ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} e)).obj X))) :=
  map_heq _ _ _
    (congrArg (fun F => F.obj X) (nativeOperatorFreeIso_source_eq e)) rfl
      (nativeOperatorFreeIso_hom_heq e X)

/-- The complete original coefficient Iso is evaluation of the same full native free Iso. -/
theorem nativeCoefficientIso_evaluation_heq (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((nativeCoefficientIso e n).app X)
      ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).mapIso ((nativeOperatorFreeIso e).app X)) := by
  apply iso_heq_of_hom
  · change (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor n).obj
      ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X) = _
    rw [SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq]
    rfl
  · exact (nativeCoefficientIso_hom_value e n X).trans
      (nativeOperatorFreeIso_evaluation_hom e n X).symm

/-- The complete original source initializer is retained before any level evaluation. -/
theorem originalOperatorFreeIso_app (e : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    (originalOperatorFreeIso e).app X =
      SymmetricRightModulePresentation.rightModuleToOperator.mapIso
        ((SymmetricStandardRightFreeEvaluation.freeComparison e).app X) ≪≫
          (nativeOperatorFreeIso e).app X := by
  have h := congrArg (fun q => q.app X) (originalOperatorFreeIso_eq e)
  exact h.trans (by apply Iso.ext; rfl)

/-- The native value comparison is the actual original whole native evaluation equality. -/
def nativeValueIso (n : Operad.SmallFinBijGroupoid)
    (M : SymmetricStandardRightFreeEvaluation.Carrier.{u, v}) :
    (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor n).obj M ≅
      M.X.functor.obj n :=
  (eqToIso (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq n)).app M

/-- The original value comparison is the literal original whole evaluation equality. -/
def originalValueIso (n : Operad.SmallFinBijGroupoid)
    (M : SymmetricStandardRightFreeEvaluation.Carrier.{u, v}) :
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n).obj M ≅
      M.X.functor.obj n :=
  (eqToIso (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n)).app M

/-- The actual chosen evaluation comparison is the full identity value comparison. -/
theorem evaluationIso_value (n : Operad.SmallFinBijGroupoid)
    (M : SymmetricStandardRightFreeEvaluation.Carrier.{u, v}) :
    (SymmetricStandardRightFreeEvaluation.evaluationIso n).app M =
      nativeValueIso n M ≪≫ (originalValueIso n M).symm := by
  apply Iso.ext
  apply eq_of_heq
  exact (SymmetricStandardRightFreeEvaluation.evaluationIso_hom_app n M).trans
    (commonValue_hom (nativeValueIso n M) (originalValueIso n M)
      (congrArg (fun F => F.obj M)
        (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq n))
      (congrArg (fun F => F.obj M)
        (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n))
      (eqIsoApp_heq (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq n) M)
      (eqIsoApp_heq (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n) M)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original coefficient Iso is native evaluation followed by the complete free counit. -/
theorem nativeCoefficientIso_eval_eq (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    (nativeCoefficientIso e n).app X =
      nativeValueIso n ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X) ≪≫
        (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} n)).mapIso
            (X := (SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e ⋙
              SymmetricRightModulePresentation.rightModuleToOperator).obj X)
            (Y := (EnrichedFunctorCat.Free.functor
              (symmetricOperatorObj.{u, v} e)).obj X)
            ((nativeOperatorFreeIso e).app X) := by
  let freeIso :
      (SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e ⋙
        SymmetricRightModulePresentation.rightModuleToOperator).obj X ≅
      (EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} e)).obj X :=
    (nativeOperatorFreeIso e).app X
  let evaluatedIso := (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
    (symmetricOperatorObj.{u, v} n)).mapIso freeIso
  have h := iso_eq_of_heq ((nativeCoefficientIso e n).app X)
    evaluatedIso
    (congrArg (fun F => F.obj
      ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X))
      (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq n))
    (nativeCoefficientIso_evaluation_heq e n X)
  simpa only [nativeValueIso, eqIsoApp_eq] using h

private def levelBuilderFunctorIso (e n : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙
      SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n ≅
        tensorRight (coefficient.{u, v} e n) :=
  Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e)
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n) ≪≫
      Functor.isoWhiskerLeft (SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e)
        (SymmetricStandardRightFreeEvaluation.evaluationIso n).symm ≪≫
          nativeCoefficientIso e n ≪≫ EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
            (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)

private theorem levelBuilder_heq (e n : Operad.SmallFinBijGroupoid) :
    HEq (levelFunctorIso.{u, v} e n) (levelBuilderFunctorIso.{u, v} e n) := by
  unfold levelFunctorIso levelBuilderFunctorIso
  exact mprValue_heq _ _

private theorem levelSource_eq (e n : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙
      SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} n =
        SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙
          SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n :=
  congrArg (fun F => SymmetricStandardRightFreeEvaluation.originalFreeFunctor e ⋙ F)
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n).symm

/-- The existing original free level retains its entire initializer and every evaluation leg. -/
theorem levelIso_payload (e n : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    levelIso e X n =
      (originalValueIso n ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X)).symm
        ≪≫ (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n).mapIso
          ((SymmetricStandardRightFreeEvaluation.freeComparison e).app X) ≪≫
            ((SymmetricStandardRightFreeEvaluation.evaluationIso n).app
              ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X)).symm ≪≫
                (nativeCoefficientIso e n).app X ≪≫
                  (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
                    (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).app X := by
  have h := natIsoApp_heq (levelFunctorIso e n) (levelBuilderFunctorIso e n)
    (levelSource_eq e n) (levelBuilder_heq e n) X
  have hr := rebaseIso (levelIso e X n) ((levelBuilderFunctorIso e n).app X)
    (originalValueIso n ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X))
    (congrArg (fun F => F.obj
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X))
      (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n))
    (eqIsoApp_heq (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n)
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X)) h
  exact hr.trans (by apply Iso.ext; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The original free level is evaluation of the actual full original J comparison. -/
theorem levelIso_operator_evaluation (e n : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    levelIso e X n =
      (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} n)).mapIso ((originalOperatorFreeIso e).app X) ≪≫
          (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
            (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).app X := by
  rw [levelIso_payload]
  let q := (SymmetricStandardRightFreeEvaluation.freeComparison e).app X
  let originalNat := eqToIso
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n)
  have originalSquare := natIso_square_tail originalNat q
    (((SymmetricStandardRightFreeEvaluation.evaluationIso n).app
      ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X)).symm ≪≫
      (nativeCoefficientIso e n).app X ≪≫
      (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
        (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).app X)
  erw [← originalSquare]
  rw [evaluationIso_value]
  change (SymmetricStandardRightFreeEvaluation.literalEvaluation n).mapIso q ≪≫
    (originalNat.app ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X)).symm ≪≫
    (nativeValueIso n ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X) ≪≫
      (originalNat.app
        ((SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e).obj X)).symm).symm ≪≫
    (nativeCoefficientIso e n).app X ≪≫
    (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
      (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).app X = _
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [nativeCoefficientIso_eval_eq]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [originalOperatorFreeIso_app, Functor.mapIso_trans]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  change q.hom.hom.natTrans.app n ≫ _ =
    EnrichedFunctorCat.component
      (SymmetricRightModulePresentation.rightModuleToOperator.map q.hom)
      (symmetricOperatorObj.{u, v} n) ≫ _
  rw [SymmetricRightModulePresentation.rightModuleToOperator_component]

/-- The original level hom is the full J hom component followed by the actual free value. -/
theorem levelIso_operator_hom (e n : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    (levelIso e X n).hom =
      EnrichedFunctorCat.component ((originalOperatorFreeIso e).hom.app X)
        (symmetricOperatorObj.{u, v} n) ≫
          (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
            (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).hom.app X := by
  have h := congrArg Iso.hom (levelIso_operator_evaluation e n X)
  exact h

/-- The complete original inverse level map retains both original inverse source and free values. -/
theorem levelIso_operator_inv (e n : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    (levelIso e X n).inv =
      (EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
        (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)).inv.app X ≫
          EnrichedFunctorCat.component ((originalOperatorFreeIso e).inv.app X)
            (symmetricOperatorObj.{u, v} n) := by
  have h := congrArg Iso.inv (levelIso_operator_evaluation e n X)
  exact h

end PointedCGWH.OriginalStandardRightFreeLevelSource
