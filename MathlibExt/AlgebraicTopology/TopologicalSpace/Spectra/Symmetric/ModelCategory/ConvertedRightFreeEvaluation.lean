/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModule
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.FreeEvaluation
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Derived original right-sphere free/evaluation adjunction

Transport the actual original HSS-left Day free functor through the proved
sphere module conversion. Its right-module levels are literal original
levels. This derives right-module free APIs without identifying the separate
MMSS source category or its D_R Hom construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CGWH.limits MonoidalClosed

namespace PointedCGWH.SymmetricRightFreeEvaluation

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => Operad.SmallFinBijGroupoid

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallColimits

/-- The original left Day free functor followed by the actual right-module conversion. -/
@[no_expose]
def originalFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  SymmetricFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor

/-- Literal evaluation of the original underlying right-module sequence. -/
def literalEvaluation (n : I) : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} ⥤ PointedCGWH.{u,
  v} where
  obj M := M.X.functor.obj n
  map f := f.hom.natTrans.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Capture the exact original right evaluation with fixed typed endpoints. -/
@[no_expose]
def originalEvaluationFunctor (n : I) : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} ⥤
  PointedCGWH.{u, v} :=
  literalEvaluation n

/-- The captured evaluation is the whole literal original right evaluation. -/
theorem originalEvaluationFunctor_eq (n : I) :
    originalEvaluationFunctor.{u, v} n = literalEvaluation n := by rfl

/-- The complete actual native free functor through the actual right-module inverse. -/
@[no_expose]
def nativeFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v} :=
  EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
    SymmetricRightModulePresentation.operatorToRightModule.{u, v}

/-- Full native evaluation through the proved right-module forward functor. -/
@[no_expose]
def nativeEvaluationFunctor (n : I) : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} ⥤
  PointedCGWH.{u, v} :=
  SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ⋙
    EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n)

/-- The whole right free value is the literal original left free followed by conversion. -/
theorem originalFreeFunctor_eq (n : I) :
    originalFreeFunctor.{u, v} n = Mod.dayFreeAt sphereSequence.{u, v} n ⋙
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor := by
  unfold originalFreeFunctor
  rw [SymmetricFreeEvaluation.originalFreeFunctor_eq]

/-- Evaluation retains the exact complete original right-module level object. -/
theorem originalEvaluationFunctor_obj (n : I) (M : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v}) :
    (originalEvaluationFunctor n).obj M = M.X.functor.obj n := by rfl

/-- Evaluation retains the exact complete original module transformation component. -/
theorem originalEvaluationFunctor_map (n : I) {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v}} (f : M ⟶ N) :
    HEq ((originalEvaluationFunctor n).map f) (f.hom.natTrans.app n) := by rfl

/-- The typed native free functor is the complete actual constructed native value. -/
theorem nativeFreeFunctor_eq (n : I) :
    nativeFreeFunctor.{u, v} n =
      EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
        SymmetricRightModulePresentation.operatorToRightModule.{u, v} := by rfl

/-- The typed native evaluation retains the actual whole forward functor. -/
theorem nativeEvaluationFunctor_eq (n : I) :
    nativeEvaluationFunctor.{u, v} n =
      SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ⋙
        EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n) := by rfl

/-- Original left evaluation after the actual inverse conversion is literal right evaluation. -/
@[no_expose]
def inverseEvaluationIso (n : I) :
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
      SymmetricFreeEvaluation.originalEvaluationFunctor.{u, v} n ≅
        originalEvaluationFunctor.{u, v} n :=
  eqToIso (congrArg (fun R =>
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙ R)
      (SymmetricFreeEvaluation.originalEvaluationFunctor_eq n)) ≪≫
    NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
      intro M N f
      change (CommutativeModuleConversion.toLeftMap sphereSequence.{u, v} f).hom.natTrans.app n ≫
        𝟙 _ = 𝟙 _ ≫ f.hom.natTrans.app n
      rw [CommutativeModuleConversion.toLeftMap_hom]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Native evaluation is the identical original right-module level. -/
@[no_expose]
def evaluationIso (n : I) :
    nativeEvaluationFunctor.{u, v} n ≅ originalEvaluationFunctor.{u, v} n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
    intro M N f
    change EnrichedFunctorCat.component
        ((SymmetricRightModulePresentation.rightModuleToOperator.{u, v}).map f)
          (symmetricOperatorObj.{u, v} n) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.natTrans.app n
    rw [SymmetricRightModulePresentation.rightModuleToOperator_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual original left adjunction and proved conversion construct the right adjunction. -/
@[no_expose]
def originalAdjunction (n : I) :
    originalFreeFunctor.{u, v} n ⊣ originalEvaluationFunctor.{u, v} n := by
  let adj := (SymmetricFreeEvaluation.originalAdjunction n).comp
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction
  exact adj.ofNatIsoRight (inverseEvaluationIso n)

/-- The derived right adjunction retains the chosen original left and conversion values. -/
theorem originalAdjunction_eq (n : I) :
    HEq (originalAdjunction.{u, v} n)
      (let adj := (SymmetricFreeEvaluation.originalAdjunction n).comp
        SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction
       adj.ofNatIsoRight (inverseEvaluationIso n)) := by rfl

/-- The native adjunction is transported with the full actual right equivalence. -/
@[no_expose]
def transportedAdjunction (n : I) :
    nativeFreeFunctor.{u, v} n ⊣ nativeEvaluationFunctor.{u, v} n :=
  (EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)).comp
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.symm.toAdjunction

/-- The original right evaluation endpoint is kept by the complete native adjunction. -/
@[no_expose]
def migratedAdjunction (n : I) :
    nativeFreeFunctor.{u, v} n ⊣ originalEvaluationFunctor.{u, v} n :=
  (transportedAdjunction n).ofNatIsoRight (evaluationIso n)

/-- The derived original right free functor and the actual native free are naturally equal. -/
@[no_expose]
def freeComparison (n : I) : originalFreeFunctor.{u, v} n ≅ nativeFreeFunctor.{u, v} n :=
  Adjunction.leftAdjointUniq (originalAdjunction n) (migratedAdjunction n)

/-- The complete original right forward adjunct is preserved. -/
theorem freeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}}
    (f : (nativeFreeFunctor n).obj X ⟶ M) :
    (originalAdjunction n).homEquiv X M ((freeComparison n).hom.app X ≫ f) =
      (migratedAdjunction n).homEquiv X M f := by
  let adj := originalAdjunction.{u, v} n
  let newAdj := migratedAdjunction.{u, v} n
  let q := freeComparison.{u, v} n
  have hStart := adj.homEquiv_naturality_right (q.hom.app X) f
  have hUnit : adj.homEquiv X ((nativeFreeFunctor n).obj X) (q.hom.app X) =
      newAdj.unit.app X := Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact hStart.trans
    ((congrArg (fun z => z ≫ (originalEvaluationFunctor n).map f) hUnit).trans
      (newAdj.homEquiv_unit X M f).symm)

/-- The complete original right inverse adjunct is preserved. -/
theorem freeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}}
    (f : X ⟶ (originalEvaluationFunctor n).obj M) :
    (freeComparison n).hom.app X ≫ ((migratedAdjunction n).homEquiv X M).symm f =
      ((originalAdjunction n).homEquiv X M).symm f := by
  apply ((originalAdjunction n).homEquiv X M).injective
  exact (freeComparison_homEquiv n _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- The entire original right unit is retained by the free comparison. -/
theorem freeComparison_unit (n : I) (X : PointedCGWH.{u, v}) :
    (originalAdjunction n).unit.app X ≫
      (originalEvaluationFunctor n).map ((freeComparison n).hom.app X) =
        (migratedAdjunction n).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The entire original right counit is retained by the free comparison. -/
theorem freeComparison_counit (n : I) (M : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    (freeComparison n).hom.app ((originalEvaluationFunctor n).obj M) ≫
      (migratedAdjunction n).counit.app M = (originalAdjunction n).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit (originalAdjunction n) (migratedAdjunction n) M

end PointedCGWH.SymmetricRightFreeEvaluation
