/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Free evaluation in symmetric sphere-module presentations

Day free evaluation and native operator free evaluation are compared through the
sphere-module presentation equivalence. Transporting the evaluation isomorphism gives a
natural comparison of the free functors. The ordinary Hom equivalences, units and counits
agree under these comparisons, with both evaluation maps and comparison inverses retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace PointedCGWH.SymmetricFreeEvaluation

attribute [local instance] originalSymmetricSequenceMonoidal
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj

local notation "I" => Operad.SmallFinBijGroupoid

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallColimits

/-- The entire original HSS-left sphere Day-module carrier. -/
abbrev Carrier := Mod (SymmetricSequence.{u, v}) sphereSequence.{u, v}

/-- Capture the exact original HSS-left free functor as an explicitly typed value. -/
@[no_expose]
def originalFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  Mod.dayFreeAt sphereSequence.{u, v} n

/-- Capture the exact original whole Day-module evaluation functor. -/
@[no_expose]
def originalEvaluationFunctor (n : I) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  Mod.dayEvaluation sphereSequence.{u, v} n

/-- Capture the actual native free functor followed by the original full inverse. -/
@[no_expose]
def nativeFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
    SymmetricModulePresentation.operatorToModule.{u, v}

/-- Capture actual native evaluation through the original full forward functor. -/
@[no_expose]
def nativeEvaluationFunctor (n : I) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  SymmetricModulePresentation.moduleToOperator.{u, v} ⋙
    EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n)

/-- The captured original free functor is the entire actual source functor. -/
theorem originalFreeFunctor_eq (n : I) :
    originalFreeFunctor.{u, v} n = Mod.dayFreeAt sphereSequence.{u, v} n := by rfl

/-- The captured original evaluation is the entire actual source functor. -/
theorem originalEvaluationFunctor_eq (n : I) :
    originalEvaluationFunctor.{u, v} n = Mod.dayEvaluation sphereSequence.{u, v} n := by rfl

/-- The captured native free functor is the entire actual transported native free. -/
theorem nativeFreeFunctor_eq (n : I) :
    nativeFreeFunctor.{u, v} n =
      EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
        SymmetricModulePresentation.operatorToModule.{u, v} := by rfl

/-- The captured native evaluation retains the original full forward functor. -/
theorem nativeEvaluationFunctor_eq (n : I) :
    nativeEvaluationFunctor.{u, v} n = SymmetricModulePresentation.moduleToOperator.{u, v} ⋙
      EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n) := by rfl

/-- The forward comparison evaluates at the identical original module level. -/
@[no_expose]
def evaluationIso (n : I) :
    nativeEvaluationFunctor.{u, v} n ≅
        originalEvaluationFunctor.{u, v} n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
    intro M N f
    change EnrichedFunctorCat.component (SymmetricModulePresentation.toOperatorMorphism f)
        (symmetricOperatorObj.{u, v} n) ≫ 𝟙 (N.X.functor.obj n) =
      𝟙 (M.X.functor.obj n) ≫ f.hom.natTrans.app n
    rw [SymmetricModulePresentation.toOperatorMorphism_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual existing original free/evaluation adjunction, with explicit source endpoints. -/
@[no_expose]
def originalAdjunction (n : I) :
    originalFreeFunctor.{u, v} n ⊣ originalEvaluationFunctor.{u, v} n :=
  Mod.dayFreeAtEvaluationAdjunction sphereSequence.{u, v} n

/-- The actual native free adjunction followed by the proved original inverse carrier. -/
@[no_expose]
def transportedAdjunction (n : I) :
    (nativeFreeFunctor.{u, v} n) ⊣
      nativeEvaluationFunctor.{u, v} n :=
  (EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)).comp
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.symm.toAdjunction

/-- The complete original evaluation iso gives precisely the original evaluation endpoint. -/
@[no_expose]
def migratedAdjunction (n : I) :
    (nativeFreeFunctor.{u, v} n) ⊣
      originalEvaluationFunctor.{u, v} n :=
  (transportedAdjunction n).ofNatIsoRight (evaluationIso n)

/-- The original free modules and the genuine transported native free objects
are naturally isomorphic. -/
@[no_expose]
def freeComparison (n : I) :
    originalFreeFunctor.{u, v} n ≅
      nativeFreeFunctor.{u, v} n :=
  Adjunction.leftAdjointUniq (originalAdjunction n) (migratedAdjunction n)

/-- Every original evaluation component is the complete identity map. -/
theorem evaluationIso_hom_component (n : I) (M : Carrier.{u, v}) :
    HEq ((evaluationIso n).hom.app M) (𝟙 (M.X.functor.obj n)) := by rfl

theorem evaluationIso_inv_component (n : I) (M : Carrier.{u, v}) :
    HEq ((evaluationIso n).inv.app M) (𝟙 (M.X.functor.obj n)) := by rfl

/-- The sparse original adjunction is the actual original chosen value. -/
theorem originalAdjunction_eq (n : I) :
    HEq (originalAdjunction.{u, v} n)
      (Mod.dayFreeAtEvaluationAdjunction sphereSequence.{u, v} n) := by
  rfl

/-- The transported value is the actual original pair of composed adjunctions. -/
theorem transportedAdjunction_eq (n : I) :
    HEq (transportedAdjunction.{u, v} n)
      ((EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)).comp
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.symm.toAdjunction) := by
  rfl

/-- The migrated value retains the full original evaluation iso and actual native adjunction. -/
theorem migratedAdjunction_eq (n : I) :
    migratedAdjunction.{u, v} n =
      (transportedAdjunction n).ofNatIsoRight (evaluationIso n) := by
  rfl

/-- The free comparison is precisely uniqueness for those actual source adjunctions. -/
theorem freeComparison_eq (n : I) :
    freeComparison.{u, v} n =
      Adjunction.leftAdjointUniq (originalAdjunction n) (migratedAdjunction n) := by
  rfl

/-- The full original forward adjunct is retained by the complete free comparison. -/
theorem freeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : (nativeFreeFunctor.{u, v} n).obj X ⟶ M) :
    (originalAdjunction n).homEquiv X M ((freeComparison n).hom.app X ≫ f) =
      (migratedAdjunction n).homEquiv X M f := by
  let adj := originalAdjunction.{u, v} n
  let newAdj := migratedAdjunction.{u, v} n
  let q := freeComparison.{u, v} n
  have hStart := adj.homEquiv_naturality_right (q.hom.app X) f
  have hUnit : adj.homEquiv X
      ((nativeFreeFunctor.{u, v} n).obj X) (q.hom.app X) =
      newAdj.unit.app X :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact hStart.trans
    ((congrArg (fun z => z ≫ (originalEvaluationFunctor.{u, v} n).map f) hUnit).trans
      (newAdj.homEquiv_unit X M f).symm)

/-- Every complete inverse adjunct is the original inverse module adjunct. -/
theorem freeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : X ⟶ (originalEvaluationFunctor.{u, v} n).obj M) :
    (freeComparison n).hom.app X ≫ ((migratedAdjunction n).homEquiv X M).symm f =
      ((originalAdjunction n).homEquiv X M).symm f := by
  apply ((originalAdjunction n).homEquiv X M).injective
  exact (freeComparison_homEquiv n _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- The actual original unit is preserved by the whole free comparison. -/
theorem freeComparison_unit (n : I) (X : PointedCGWH.{u, v}) :
    (originalAdjunction n).unit.app X ≫
        (originalEvaluationFunctor.{u, v} n).map ((freeComparison n).hom.app X) =
      (migratedAdjunction n).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The actual original counit is preserved by the whole free comparison. -/
theorem freeComparison_counit (n : I) (M : Carrier.{u, v}) :
    (freeComparison n).hom.app ((originalEvaluationFunctor.{u, v} n).obj M) ≫
        (migratedAdjunction n).counit.app M = (originalAdjunction n).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (originalAdjunction n) (migratedAdjunction n) M

/-- The entire actual native forward Hom map keeps its evaluation comparison. -/
theorem migratedAdjunction_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : (nativeFreeFunctor.{u, v} n).obj X ⟶ M) :
    (migratedAdjunction n).homEquiv X M f =
      (transportedAdjunction n).homEquiv X M f ≫ (evaluationIso n).hom.app M :=
  Adjunction.homEquiv_ofNatIsoRight_apply _ _ f

/-- The entire actual native inverse Hom map keeps its inverse evaluation comparison. -/
theorem migratedAdjunction_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : X ⟶ (originalEvaluationFunctor.{u, v} n).obj M) :
    ((migratedAdjunction n).homEquiv X M).symm f =
      ((transportedAdjunction n).homEquiv X M).symm (f ≫ (evaluationIso n).inv.app M) :=
  Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ f

end PointedCGWH.SymmetricFreeEvaluation
