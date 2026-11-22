/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFreeEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ScalarFunctorHom
import Mathlib.CategoryTheory.Whiskering

/-!
# Actual original standard RIGHT free levels and their whole source naturality
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.OriginalStandardRightFreeLevels
universe u v

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

/-- This is the actual original native J Hom coefficient, with both original degree labels. -/
def coefficient (e n : Operad.SmallFinBijGroupoid) : PointedCGWH.{u, v} :=
  symmetricOperatorObj.{u, v} e ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} n

set_option backward.isDefEq.respectTransparency false in
/-- The whole original inverse-carrier free value uses the actual original equivalence counit. -/
def nativeCoefficientIso (e n : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.nativeFreeFunctor.{u, v} e ⋙
      SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor.{u, v} n ≅
        EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) (symmetricOperatorObj.{u, v} e) ⋙
            EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} n) := by
  rw [SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq,
    SymmetricStandardRightFreeEvaluation.nativeEvaluationFunctor_eq]
  let E := SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
  let L := EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) (symmetricOperatorObj.{u, v} e)
  let Ev := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (symmetricOperatorObj.{u, v} n)
  change (L ⋙ E.inverse) ⋙ (E.functor ⋙ Ev) ≅ L ⋙ Ev
  exact Functor.associator L E.inverse (E.functor ⋙ Ev) ≪≫
    Functor.isoWhiskerLeft L (Functor.associator E.inverse E.functor Ev).symm ≪≫
      Functor.isoWhiskerLeft L (Functor.isoWhiskerRight E.counitIso Ev) ≪≫
        Functor.isoWhiskerLeft L (Functor.leftUnitor Ev)

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual original free-level functor is identified through its original comparison. -/
def levelFunctorIso (e n : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙
      SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} n ≅
        tensorRight (coefficient.{u, v} e n) := by
  rw [← SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq]
  exact Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e)
      (SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n) ≪≫
    Functor.isoWhiskerLeft (SymmetricStandardRightFreeEvaluation.nativeFreeFunctor e)
      (SymmetricStandardRightFreeEvaluation.evaluationIso n).symm ≪≫
        nativeCoefficientIso e n ≪≫
          EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
            (symmetricOperatorObj.{u, v} e) (symmetricOperatorObj.{u, v} n)

set_option backward.isDefEq.respectTransparency false in
/-- Each actual original free level has the complete original coefficient tensor isomorphism. -/
def levelIso (e : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v})
    (n : Operad.SmallFinBijGroupoid) :
    ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).obj X).X.functor.obj n ≅
      X ⊗ coefficient e n := (levelFunctorIso e n).app X

set_option backward.isDefEq.respectTransparency false in
/-- Every original free coefficient morphism preserves the whole chosen level map. -/
@[reassoc]
theorem levelIso_naturality (e : Operad.SmallFinBijGroupoid)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (n : Operad.SmallFinBijGroupoid) :
    (levelIso e X n).hom ≫ (f ▷ coefficient e n) =
      ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).map f).hom.natTrans.app n ≫
        (levelIso e Y n).hom := by
  have h := (levelFunctorIso e n).hom.naturality f
  change ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).map f).hom.natTrans.app n ≫
    (levelIso e Y n).hom = (levelIso e X n).hom ≫ (f ▷ coefficient e n) at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Every full inverse level map preserves the same original free morphism. -/
@[reassoc]
theorem levelIso_inv_naturality (e : Operad.SmallFinBijGroupoid)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (n : Operad.SmallFinBijGroupoid) :
    (f ▷ coefficient e n) ≫ (levelIso e Y n).inv =
      (levelIso e X n).inv ≫
        ((SymmetricStandardRightFreeEvaluation.originalFreeFunctor e).map f).hom.natTrans.app n :=
  (levelFunctorIso e n).inv.naturality f

/-- The actual standard RIGHT free functor supplies the derived scalar/free Hom primitive. -/
def data (e : Operad.SmallFinBijGroupoid) :
    SymmetricScalarFunctorHom.Data
      (SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e) where
  coefficient := coefficient e
  levelIso X n := levelIso e X n
  naturality f n := levelIso_naturality e f n

/-- The supplied coefficient remains the actual original native J Hom object. -/
theorem data_coefficient (e n : Operad.SmallFinBijGroupoid) :
    (data.{u, v} e).coefficient n =
      (symmetricOperatorObj.{u, v} e ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} n) := rfl

/-- The supplied whole level isomorphism is exactly the derived original map and inverse. -/
theorem data_levelIso (e n : Operad.SmallFinBijGroupoid) (X : PointedCGWH.{u, v}) :
    (data e).levelIso X n = levelIso e X n := rfl

end PointedCGWH.OriginalStandardRightFreeLevels
