/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Strict.Basic

/-!
# Full original RIGHT adjunction and cardinal comparisons on strict source diagrams

The chosen original standard RIGHT adjunction passes through the actual full
source and chosen-base equivalences. Its forward and inverse Hom maps, whole
units and counits, and complete free Arrow comparison retain those choices.
Both original cardinal middle comparisons remain natural on whole Arrow maps.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

section ActualAdjunctionData
universe uC vC
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

private theorem actual_strict_adjunction_point
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : EnrichedProjective.NativePresentation.transportedEvaluation e a ≅ R)
    (j : L ⋙ (EnrichedProjective.NativePresentation.strictSourceEquivalence e).functor ⊣
      EnrichedProjective.BasedNativePresentation.strictEvaluation a)
    (hj : j = EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction
      e a L R adj hR)
    (k : (EnrichedProjective.NativePresentation.strictSourceEquivalence e).functor ⊣
      (EnrichedProjective.NativePresentation.strictSourceEquivalence e).inverse)
    (hk : k = (EnrichedProjective.NativePresentation.strictSourceEquivalence e).toAdjunction)
    (i : (EnrichedProjective.NativePresentation.strictSourceEquivalence e).inverse ⋙ R ≅
      EnrichedProjective.BasedNativePresentation.strictEvaluation a)
    (hi : i = EnrichedProjective.NativePresentation.strictSourceInverseEvaluationIso e a R hR)
    {X : PointedCGWH.{u, v}} {Y : EnrichedProjective.BasedNativePresentation.StrictCarrier
      (A := A)}
    (f : (L ⋙ (EnrichedProjective.NativePresentation.strictSourceEquivalence e).functor).obj
      X ⟶ Y) :
    j.homEquiv X Y f = adj.homEquiv X
      ((EnrichedProjective.NativePresentation.strictSourceEquivalence e).inverse.obj Y)
        (k.homEquiv (L.obj X) Y f) ≫ i.hom.app Y := by
  rw [hj, hk, hi]
  exact EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction_homEquiv
    e a L R adj hR f
end ActualAdjunctionData

/-- Capture the exact original full strict carrier adjunction with explicit functor endpoints. -/
def strictCarrierAdjunction : strictPresentation.functor ⊣ strictPresentation.inverse :=
  strictPresentation.toAdjunction

/-- The captured carrier adjunction is the same entire chosen equivalence adjunction. -/
theorem strictCarrierAdjunction_eq : strictCarrierAdjunction.{u, v} =
    strictPresentation.toAdjunction := by rfl

/-- The entire original inverse evaluation uses the actual source counit and strict restriction. -/
def strictInverseEvaluationIso (n : I) :
    strictPresentation.inverse ⋙
      PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n ≅
        EnrichedProjective.BasedNativePresentation.strictEvaluation
          (PointedCGWH.SymmetricDRight.obj n) :=
  EnrichedProjective.NativePresentation.strictSourceInverseEvaluationIso presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n) (evaluationIso n)

/-- The exact original forward adjunct retains both chosen source-equivalence Hom maps. -/
private theorem original_adjunction_parameterized (n : I)
    (e : Carrier.{u, v} ≌ SourceCarrier.{u, v})
    (hR : EnrichedProjective.NativePresentation.transportedEvaluation e
      (PointedCGWH.SymmetricDRight.obj n) ≅
        PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n)
    {X : PointedCGWH.{u, v}} {Y : StrictSourceCarrier.{u, v}}
    (f : (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      (EnrichedProjective.NativePresentation.strictSourceEquivalence e).functor).obj X ⟶ Y) :
    (EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction e
      (PointedCGWH.SymmetricDRight.obj n)
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n)
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n)
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} n) hR).homEquiv
        X Y f =
          (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} n).homEquiv
            X ((EnrichedProjective.NativePresentation.strictSourceEquivalence e).inverse.obj Y)
              ((EnrichedProjective.NativePresentation.strictSourceEquivalence
                e).toAdjunction.homEquiv
                ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v}
                  n).obj X) Y f) ≫
                (EnrichedProjective.NativePresentation.strictSourceInverseEvaluationIso e
                  (PointedCGWH.SymmetricDRight.obj n)
                  (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v}
                    n) hR).hom.app Y :=
  EnrichedProjective.NativePresentation.strictSourceOriginalAdjunction_homEquiv e
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor.{u, v} n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} n) hR f

theorem strictOriginalAdjunction_homEquiv (n : I) {X : PointedCGWH.{u, v}}
    {Y : StrictSourceCarrier.{u, v}}
    (f : (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      strictPresentation.functor).obj X ⟶ Y) :
    (strictOriginalAdjunction n).homEquiv X Y f =
      (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction.{u, v} n).homEquiv X
        (strictPresentation.inverse.obj Y)
        (strictCarrierAdjunction.homEquiv
          ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v}
            n).obj X) Y f) ≫
            (strictInverseEvaluationIso n).hom.app Y :=
  original_adjunction_parameterized n presentation (evaluationIso n) f

/-- The actual inverse-evaluation comparison is the full original postcomposition equivalence. -/
def strictEvaluationHomEquiv (n : I) (X : PointedCGWH.{u, v})
    (Y : StrictSourceCarrier.{u, v}) :
    (X ⟶ (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n).obj
      (strictPresentation.inverse.obj Y)) ≃
        (X ⟶ (EnrichedProjective.BasedNativePresentation.strictEvaluation
          (PointedCGWH.SymmetricDRight.obj n)).obj Y) where
  toFun f := f ≫ (strictInverseEvaluationIso n).hom.app Y
  invFun f := f ≫ (strictInverseEvaluationIso n).inv.app Y
  left_inv f := by
    dsimp only
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id f
  right_inv f := by
    dsimp only
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id f

/-- Both entire original Hom maps are the actual three chosen equivalences in their source order. -/
def strictOriginalHomEquivStages (n : I) (X : PointedCGWH.{u, v})
    (Y : StrictSourceCarrier.{u, v}) :
    ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n ⋙
      strictPresentation.functor).obj X ⟶ Y) ≃
        (X ⟶ (EnrichedProjective.BasedNativePresentation.strictEvaluation
          (PointedCGWH.SymmetricDRight.obj n)).obj Y) :=
  (strictCarrierAdjunction.homEquiv
    ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n).obj X) Y).trans
    (((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n).homEquiv X
      (strictPresentation.inverse.obj Y)).trans (strictEvaluationHomEquiv n X Y))

/-- The whole actual chosen original adjunct is exactly the three full original Hom stages. -/
theorem strictOriginalHomEquivStages_eq (n : I) (X : PointedCGWH.{u, v})
    (Y : StrictSourceCarrier.{u, v}) :
    (strictOriginalAdjunction n).homEquiv X Y = strictOriginalHomEquivStages n X Y := by
  apply Equiv.ext
  intro f
  exact strictOriginalAdjunction_homEquiv n f

/-- Both complete original inverse maps and inverse evaluation are retained as a whole
  equivalence. -/
theorem strictOriginalAdjunction_homEquiv_symm (n : I) (X : PointedCGWH.{u, v})
    (Y : StrictSourceCarrier.{u, v}) :
    ((strictOriginalAdjunction n).homEquiv X Y).symm =
      (strictOriginalHomEquivStages n X Y).symm :=
  congrArg Equiv.symm (strictOriginalHomEquivStages_eq n X Y)

/-- The whole original forward adjunct compares to the actual strict native free adjunct. -/
theorem strictFreeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}}
    {Y : StrictSourceCarrier.{u, v}}
    (f : (EnrichedProjective.BasedNativePresentation.strictFreeAt
      (PointedCGWH.SymmetricDRight.obj n)).obj X ⟶ Y) :
    (strictOriginalAdjunction n).homEquiv X Y ((strictFreeComparison n).hom.app X ≫ f) =
      (EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
        (PointedCGWH.SymmetricDRight.obj n)).homEquiv X Y f :=
  EnrichedProjective.NativePresentation.strictSourceFreeIso_homEquiv presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n) f

/-- The whole original inverse adjunct compares to the same actual strict native inverse map. -/
theorem strictFreeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}}
    {Y : StrictSourceCarrier.{u, v}}
    (f : X ⟶ (EnrichedProjective.BasedNativePresentation.strictEvaluation
      (PointedCGWH.SymmetricDRight.obj n)).obj Y) :
    (strictFreeComparison n).hom.app X ≫
      ((EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
        (PointedCGWH.SymmetricDRight.obj n)).homEquiv X Y).symm f =
          ((strictOriginalAdjunction n).homEquiv X Y).symm f :=
  EnrichedProjective.NativePresentation.strictSourceFreeIso_homEquiv_symm presentation
    (PointedCGWH.SymmetricDRight.obj n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor n)
    (PointedCGWH.SymmetricStandardRightFreeEvaluation.originalAdjunction n) (evaluationIso n) f

/-- The whole actual composed original unit is preserved by the exact strict free comparison. -/
theorem strictFreeComparison_unit (n : I) :
    (strictOriginalAdjunction.{u, v} n).unit ≫
      Functor.whiskerRight (strictFreeComparison n).hom
        (EnrichedProjective.BasedNativePresentation.strictEvaluation
          (PointedCGWH.SymmetricDRight.obj n)) =
        (EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
          (PointedCGWH.SymmetricDRight.obj n)).unit :=
  Adjunction.unit_leftAdjointUniq_hom (strictOriginalAdjunction n)
    (EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
      (PointedCGWH.SymmetricDRight.obj n))

/-- The whole actual composed original counit is preserved by the exact strict free comparison. -/
theorem strictFreeComparison_counit (n : I) :
    Functor.whiskerLeft
      (EnrichedProjective.BasedNativePresentation.strictEvaluation
        (PointedCGWH.SymmetricDRight.obj n))
      (strictFreeComparison n).hom ≫
        (EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
          (PointedCGWH.SymmetricDRight.obj n)).counit =
            (strictOriginalAdjunction.{u, v} n).counit :=
  Adjunction.leftAdjointUniq_hom_counit (strictOriginalAdjunction n)
    (EnrichedProjective.BasedNativePresentation.strictFreeAdjunction
      (PointedCGWH.SymmetricDRight.obj n))

/-- Every whole original strict free arrow is isomorphic to the exact native strict free arrow. -/
def strictFreeGeneratorArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk (strictPresentation.functor.map
      ((PointedCGWH.SymmetricStandardRightFreeEvaluation.originalFreeFunctor n).map f)) ≅
        CategoryTheory.Arrow.mk ((EnrichedProjective.BasedNativePresentation.strictFreeAt
          (PointedCGWH.SymmetricDRight.obj n)).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (strictFreeComparison n) (CategoryTheory.Arrow.mk f)

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- Every complete strict Arrow square retains the natural original I middle comparison. -/
theorem strictOriginalCofibrantFactorizationData_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : CategoryTheory.Arrow StrictSourceCarrier.{u, v}} (φ : f ⟶ g) :
    EnrichedZeroCompletion.strictRestriction.map
      ((strictOriginalCofibrantFactorizationData.{u, v}).Z.map φ) ≫
      (strictOriginalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app g =
        (strictOriginalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
          (originalCofibrantFactorizationData.{u, v}).Z.map
            (EnrichedZeroCompletion.strictRestriction.mapArrow.map φ) :=
  (strictOriginalCofibrantFactorizationDataComparisonIso.{u, v}).hom.naturality φ

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- Every complete strict Arrow square retains the natural original J middle comparison. -/
theorem strictOriginalFibrantFactorizationData_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : CategoryTheory.Arrow StrictSourceCarrier.{u, v}} (φ : f ⟶ g) :
    EnrichedZeroCompletion.strictRestriction.map
      ((strictOriginalFibrantFactorizationData.{u, v}).Z.map φ) ≫
      (strictOriginalFibrantFactorizationDataComparisonIso.{u, v}).hom.app g =
        (strictOriginalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
          (originalFibrantFactorizationData.{u, v}).Z.map
            (EnrichedZeroCompletion.strictRestriction.mapArrow.map φ) :=
  (strictOriginalFibrantFactorizationDataComparisonIso.{u, v}).hom.naturality φ

end PointedCGWH.Spectra.Symmetric.DRightPresentation
