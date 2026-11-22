/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.FreeHom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Source
import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource
import MathlibExt.CategoryTheory.Enriched.AdjunctionComparisonHEq
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.LevelSource

/-!
# Free symmetric modules and enriched evaluation

Compares the standard free/evaluation adjunction with the enriched free functor through the
sphere-module presentation equivalence. Point formulas retain the original adjunct and both
evaluation comparison maps at every finite-set index.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricFreeAdjunctionPoint

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The original standard RIGHT carrier of the actual free adjunction. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}
/-- The original literal degree evaluation of the standard RIGHT carrier. -/
abbrev E := SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- The original evaluation isomorphism retains its entire actual native endpoint. -/
def evaluationIso (e : Operad.SmallFinBijGroupoid) :
    E.{u, v}.functor ⋙ EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} e) ≅
      SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} e := by
  change SymmetricRightModulePresentation.rightModuleToOperator ⋙
    EnrichedFunctorCat.evaluation (symmetricOperatorObj e) ≅
      SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e
  exact eqToIso (SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq e).symm ≪≫
    SymmetricStandardRightFreeEvaluation.evaluationIso e

/-- The complete normalized original free comparison uses the same chosen adjunction. -/
def normalizedOperatorIso (e : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙ E.{u, v}.functor ≅
      EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
        (symmetricOperatorObj.{u, v} e) :=
  EnrichedFunctorCat.FreeAdjunctionSource.operatorIso E (symmetricOperatorObj e)
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e)
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) (evaluationIso e)

section CounitComparison
universe uS vS uC vC uD vD
variable {S : Type uS} [Category.{vS} S] {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

private theorem nativeCounit_eq (E : C ≌ D) (L : S ⥤ D)
    (q : (L ⋙ E.inverse) ⋙ E.functor ≅ L)
    (hq : ∀ X : S, q.hom.app X = E.counitIso.hom.app (L.obj X)) :
    q = Functor.associator L E.inverse E.functor ≪≫
      Functor.isoWhiskerLeft L E.counitIso ≪≫ Functor.rightUnitor L := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rw [hq X]
  change E.counitIso.hom.app (L.obj X) = 𝟙 _ ≫ E.counitIso.hom.app (L.obj X) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

private theorem isoTrans_app {F G H : S ⥤ D} (q : F ≅ G) (r : G ≅ H) (X : S) :
    (q ≪≫ r).app X = q.app X ≪≫ r.app X := by apply Iso.ext; rfl

private theorem eqIso_symm_app {F G : S ⥤ D} (h : F = G) (X : S) :
    (eqToIso h.symm).app X = ((eqToIso h).app X).symm := by
  cases h
  rfl

private theorem rightAdjointEq_point {L : S ⥤ D} {R R' : D ⥤ S}
    (h : R = R') (adj : L ⊣ R) (X : S) (M : D) (f : L.obj X ⟶ M) :
    (Adjunction.ofRightEq h adj).homEquiv X M f =
      adj.homEquiv X M f ≫ eqToHom (Functor.congr_obj h M) := by
  cases h
  rw [eq_of_heq (Adjunction.ofRightEq_heq rfl adj), eqToHom_refl, Category.comp_id]

end CounitComparison

/-- The whole normalized original comparison is the same actual original free/counit comparison. -/
theorem normalizedOperatorIso_eq (e : Operad.SmallFinBijGroupoid) :
    normalizedOperatorIso.{u, v} e = OriginalStandardRightFreeLevels.originalOperatorFreeIso e := by
  let a := symmetricOperatorObj.{u, v} e
  let L := SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e
  let R := SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} e
  let adj := SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} e
  have hL : SymmetricStandardRightFreeEvaluation.nativeFreeFunctor.{u, v} e =
      EnrichedFunctorCat.Free.functor a ⋙ E.{u, v}.inverse :=
    SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq e
  have hR : SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor.{u, v} e =
      E.{u, v}.functor ⋙ EnrichedFunctorCat.evaluation a :=
    SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq e
  have hr : HEq (evaluationIso.{u, v} e)
      (SymmetricStandardRightFreeEvaluation.evaluationIso.{u, v} e) := by
    unfold evaluationIso
    exact AdjunctionComparisonHEq.eqToIso_symm_trans hR
      (SymmetricStandardRightFreeEvaluation.evaluationIso e)
  have ha := AdjunctionComparisonHEq.ofNatIsoRight hL hR
    (SymmetricStandardRightFreeEvaluation.transportedAdjunction e)
    ((EnrichedFunctorCat.Free.adjunction a).comp E.symm.toAdjunction)
    (SymmetricStandardRightFreeEvaluation.transportedAdjunction_heq e)
    (SymmetricStandardRightFreeEvaluation.evaluationIso e) (evaluationIso e) hr.symm
  rw [← SymmetricStandardRightFreeEvaluation.migratedAdjunction_eq] at ha
  rw [← EnrichedFunctorCat.FreeAdjunctionSource.transported_eq E a,
    ← EnrichedFunctorCat.FreeAdjunctionSource.migrated_eq E a R (evaluationIso e)] at ha
  have hq := AdjunctionComparisonHEq.leftAdjointUniq hL adj
    (SymmetricStandardRightFreeEvaluation.migratedAdjunction e)
    (EnrichedFunctorCat.FreeAdjunctionSource.migrated E a R (evaluationIso e)) ha
  rw [← SymmetricStandardRightFreeEvaluation.freeComparison_eq,
    ← EnrichedFunctorCat.FreeAdjunctionSource.comparison_eq E a L R adj (evaluationIso e)] at hq
  have hw := AdjunctionComparisonHEq.whiskerRight hL
    (SymmetricStandardRightFreeEvaluation.freeComparison e)
    (EnrichedFunctorCat.FreeAdjunctionSource.comparison E a L R adj (evaluationIso e)) hq E.functor
  have hn : HEq (OriginalStandardRightFreeLevels.nativeOperatorFreeIso.{u, v} e)
      (EnrichedFunctorCat.FreeAdjunctionSource.nativeIso E a) :=
    (OriginalStandardRightFreeLevels.nativeOperatorFreeIso_initializer_heq e).trans
      (heq_of_eq (nativeCounit_eq E (EnrichedFunctorCat.Free.functor a)
        (EnrichedFunctorCat.FreeAdjunctionSource.nativeIso E a)
        (EnrichedFunctorCat.FreeAdjunctionSource.nativeIso_hom_app E a)).symm)
  have hall := AdjunctionComparisonHEq.trans
    (OriginalStandardRightFreeLevels.nativeOperatorFreeIso_source_eq e)
    (Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e) E.functor)
    (Functor.isoWhiskerRight
      (EnrichedFunctorCat.FreeAdjunctionSource.comparison E a L R adj (evaluationIso e)) E.functor)
    hw (OriginalStandardRightFreeLevels.nativeOperatorFreeIso e)
    (EnrichedFunctorCat.FreeAdjunctionSource.nativeIso E a) hn
  exact (EnrichedFunctorCat.FreeAdjunctionSource.operatorIso_eq E a L R adj
    (evaluationIso e)).trans
      (hall.symm.trans (OriginalStandardRightFreeLevels.originalOperatorFreeIso_eq e).symm)

/-- Every actual original adjunct point is the full free evaluation after the original carrier. -/
theorem point (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶ M) :
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv X M f ≫
      (evaluationIso e).inv.app M =
        EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} e) X (E.functor.obj M)
          ((normalizedOperatorIso e).inv.app X ≫
            E.functor.map f) := by
  have h := EnrichedFunctorCat.FreeAdjunctionSource.point E (symmetricOperatorObj e)
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e)
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e) (evaluationIso e) f
  change _ = EnrichedFunctorCat.Free.evaluate _ _ _
    ((normalizedOperatorIso e).inv.app X ≫ E.functor.map f) at h
  exact h

/-- The complete original evaluation comparison is the actual identity level morphism. -/
theorem originalEvaluation_hom (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    HEq ((SymmetricStandardRightFreeEvaluation.evaluationIso.{u, v} e).hom.app M)
      (𝟙 (M.X.functor.obj e)) :=
  SymmetricStandardRightFreeEvaluation.evaluationIso_hom_app e M

/-- The complete original inverse comparison is the same actual identity level morphism. -/
theorem originalEvaluation_inv (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    HEq ((SymmetricStandardRightFreeEvaluation.evaluationIso.{u, v} e).inv.app M)
      (𝟙 (M.X.functor.obj e)) :=
  SymmetricStandardRightFreeEvaluation.evaluationIso_inv_app e M

/-- Every original chosen adjunct point uses the actual whole original full-J comparison. -/
theorem original_point (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X ⟶ M) :
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv X M f ≫
      (evaluationIso e).inv.app M =
        EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} e) X (E.functor.obj M)
          ((OriginalStandardRightFreeLevels.originalOperatorFreeIso e).inv.app X ≫
            E.functor.map f) := by
  have h := point e X M f
  rw [normalizedOperatorIso_eq] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The entire original native evaluation comparison is the same actual original value Iso. -/
theorem evaluation_value (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v}) :
    (evaluationIso.{u, v} e).app M =
      (OriginalStandardRightFreeLevelSource.originalValueIso e M).symm := by
  unfold evaluationIso
  dsimp only [id]
  rw [isoTrans_app, eqIso_symm_app,
    OriginalStandardRightFreeLevelSource.evaluationIso_value]
  change (OriginalStandardRightFreeLevelSource.nativeValueIso e M).symm ≪≫
    (OriginalStandardRightFreeLevelSource.nativeValueIso e M ≪≫
      (OriginalStandardRightFreeLevelSource.originalValueIso e M).symm) = _
  exact Iso.symm_self_id_assoc _ _

/-- Every original literal value point is the actual full original free evaluation. -/
theorem value_point (e : Operad.SmallFinBijGroupoid) (M : Carrier.{u, v})
    (f : (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj
      (𝟙_ PointedCGWH.{u, v}) ⟶ M) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (SymmetricActualRightFreeHom.valueIso e M).hom =
      EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} e)
        (𝟙_ PointedCGWH.{u, v}) (E.functor.obj M)
        ((OriginalStandardRightFreeLevels.originalOperatorFreeIso e).inv.app
          (𝟙_ PointedCGWH.{u, v}) ≫ E.functor.map f) := by
  rw [SymmetricActualRightFreeHom.valueIso_point]
  change (Adjunction.ofRightEq
    (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq e)
    (SymmetricStandardRightFreeEvaluation.originalAdjunction e)).homEquiv _ M f = _
  rw [rightAdjointEq_point]
  have h := original_point e (𝟙_ PointedCGWH.{u, v}) M f
  have hev := congrArg Iso.inv (evaluation_value e M)
  change (evaluationIso e).inv.app M =
    (OriginalStandardRightFreeLevelSource.originalValueIso e M).hom at hev
  rw [hev] at h
  unfold OriginalStandardRightFreeLevelSource.originalValueIso at h
  change (SymmetricStandardRightFreeEvaluation.originalAdjunction e).homEquiv _ M f ≫
    (eqToIso (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq e)).hom.app M = _
      at h
  rw [eqToIso.hom, eqToHom_app] at h
  exact h

end PointedCGWH.SymmetricFreeAdjunctionPoint
