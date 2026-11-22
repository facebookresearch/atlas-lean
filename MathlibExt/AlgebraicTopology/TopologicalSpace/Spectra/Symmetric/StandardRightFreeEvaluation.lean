/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModule
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Free and evaluation adjunctions for right sphere modules

Constructs the standard right sphere-module free functor from a Day free diagram and identifies evaluation with the underlying module component. The module/operator equivalence compares this adjunction with the native enriched free-evaluation adjunction, retaining the Hom correspondences, unit, counit and triangle equations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open scoped CategoryTheory.MonObj MonoidalClosed

namespace PointedCGWH.SymmetricStandardRightFreeEvaluation

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => Operad.SmallFinBijGroupoid

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallColimits

universe uA vA uB vB

private theorem homEquivOfEndpointHEq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {adj : L ⊣ R} {adj' : L' ⊣ R'}
    (hL : L = L') (hR : R = R') (ha : HEq adj adj')
    (X : A) (M : B) (f : L.obj X ⟶ M) :
    HEq (adj.homEquiv X M f)
      (adj'.homEquiv X M (eqToHom (congrArg (fun F => F.obj X) hL).symm ≫ f)) := by
  cases hL
  cases hR
  cases ha
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem compEquivalenceHomEquiv
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type u} [Category.{v} C] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (E : C ≌ B) (X : A) (M : C) (f : E.inverse.obj (F.obj X) ⟶ M) :
    (adj.comp E.symm.toAdjunction).homEquiv X M f =
      adj.homEquiv X (E.functor.obj M)
        (E.counitIso.inv.app (F.obj X) ≫ E.functor.map f) := by
  rw [Adjunction.comp_homEquiv]
  change adj.homEquiv X (E.functor.obj M)
    (E.symm.toAdjunction.homEquiv (F.obj X) M f) = _
  rw [Adjunction.homEquiv_unit]
  rfl


/-- The actual standard right sphere-module carrier. -/
abbrev Carrier := SymmetricRightModulePresentation.RightSphereModule.{u, v}

/-- The unchanged actual original ordinary free diagram and Day wrapper. -/
@[no_expose]
def diagramFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ SymmetricSequence.{u, v} :=
  CategoryTheory.evaluationLeftAdjoint PointedCGWH.{u, v} n ⋙
    (DayFunctor.equiv I PointedCGWH.{u, v}).symm.functor

/-- Original standard right Day free is built from the actual right tensor free module. -/
@[no_expose]
def originalFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  diagramFreeFunctor n ⋙ RightModuleFree.functor sphereSequence.{u, v}

/-- Literal evaluation of the actual original right-module sequence. -/
def literalEvaluation (n : I) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} where
  obj M := M.X.functor.obj n
  map f := f.hom.natTrans.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Capture the exact literal original right evaluation with fixed endpoints. -/
@[no_expose]
def originalEvaluationFunctor (n : I) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  literalEvaluation n

/-- The actual original standard right-free value uses existing Mod.free in the opposite. -/
theorem originalFreeFunctor_eq (n : I) :
    originalFreeFunctor.{u, v} n =
      (CategoryTheory.evaluationLeftAdjoint PointedCGWH.{u, v} n ⋙
        (DayFunctor.equiv I PointedCGWH.{u, v}).symm.functor) ⋙
      (mopFunctor (SymmetricSequence.{u, v}) ⋙ Mod.free (mop sphereSequence.{u, v}) ⋙
        RightModuleFree.unmopModules sphereSequence.{u, v}) := by
  unfold originalFreeFunctor diagramFreeFunctor
  rw [RightModuleFree.functor_eq]

/-- The full standard free carrier retains the literal original right tensor order. -/
theorem originalFreeFunctor_obj (n : I) (X : PointedCGWH.{u, v}) :
    ((originalFreeFunctor n).obj X).X =
      (diagramFreeFunctor n).obj X ⊗ sphereSequence.{u, v} := by
  unfold originalFreeFunctor
  exact RightModuleFree.functor_obj sphereSequence.{u, v} ((diagramFreeFunctor n).obj X)

/-- The whole original free map is the unchanged original right tensor of the diagram map. -/
theorem originalFreeFunctor_map (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    eqToHom (originalFreeFunctor_obj n X).symm ≫
      ((originalFreeFunctor n).map f).hom ≫ eqToHom (originalFreeFunctor_obj n Y) =
        (diagramFreeFunctor n).map f ▷ sphereSequence.{u, v} := by
  unfold originalFreeFunctor
  exact RightModuleFree.functor_map sphereSequence.{u, v} ((diagramFreeFunctor n).map f)

/-- The entire original free action uses the original right Day tensor and multiplication. -/
theorem originalFreeFunctor_smul (n : I) (X : PointedCGWH.{u, v}) :
    (eqToHom (originalFreeFunctor_obj n X).symm ▷ sphereSequence.{u, v}) ≫
      ModObj.smul (M := mop sphereSequence.{u, v})
        (X := ((originalFreeFunctor n).obj X).X) ≫ eqToHom (originalFreeFunctor_obj n X) =
      (α_ ((diagramFreeFunctor n).obj X) sphereSequence.{u, v} sphereSequence.{u, v}).hom ≫
        ((diagramFreeFunctor n).obj X ◁
          (μ : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v})) := by
  unfold originalFreeFunctor
  exact RightModuleFree.functor_smul sphereSequence.{u, v} ((diagramFreeFunctor n).obj X)

/-- The actual diagram free keeps every original degree and ordinary free arrow. -/
theorem diagramFreeFunctor_eq (n : I) : diagramFreeFunctor.{u, v} n =
    CategoryTheory.evaluationLeftAdjoint PointedCGWH.{u, v} n ⋙
      (DayFunctor.equiv I PointedCGWH.{u, v}).symm.functor := by rfl

/-- Original evaluation is the whole literal sequence functor. -/
theorem originalEvaluationFunctor_eq (n : I) :
    originalEvaluationFunctor.{u, v} n = literalEvaluation n := by rfl

/-- Original right evaluation retains the complete underlying sequence object. -/
theorem originalEvaluationFunctor_obj (n : I) (M : Carrier.{u, v}) :
    (originalEvaluationFunctor n).obj M = M.X.functor.obj n := by rfl

/-- Original evaluation retains every complete right module morphism component. -/
theorem originalEvaluationFunctor_map (n : I) {M N : Carrier.{u, v}} (f : M ⟶ N) :
    HEq ((originalEvaluationFunctor n).map f) (f.hom.natTrans.app n) := by rfl

/-- The actual ordinary diagram adjunction and standard right free
construct the original source adjunction. -/
@[no_expose]
def originalAdjunction (n : I) :
    originalFreeFunctor.{u, v} n ⊣ originalEvaluationFunctor.{u, v} n := by
  let adj := ((CategoryTheory.evaluationAdjunctionRight PointedCGWH.{u, v} n).comp
    (DayFunctor.equiv I PointedCGWH.{u, v}).symm.toAdjunction).comp
      (RightModuleFree.adjunction sphereSequence.{u, v})
  exact adj.ofNatIsoRight (NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
    intro M N f
    change f.hom.natTrans.app n ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.natTrans.app n
    exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- Capture the actual existing native free functor through the genuine right-module inverse. -/
@[no_expose]
def nativeFreeFunctor (n : I) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
    SymmetricRightModulePresentation.operatorToRightModule.{u, v}

/-- Capture actual native evaluation through the full original module/J forward functor. -/
@[no_expose]
def nativeEvaluationFunctor (n : I) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ⋙
    EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n)

/-- The typed native free is exactly the original proved native free value. -/
theorem nativeFreeFunctor_eq (n : I) : nativeFreeFunctor.{u, v} n =
    EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n) ⋙
      SymmetricRightModulePresentation.operatorToRightModule.{u, v} := by rfl

/-- The typed native evaluation retains the full genuine module/J map. -/
theorem nativeEvaluationFunctor_eq (n : I) : nativeEvaluationFunctor.{u, v} n =
    SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ⋙
      EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n) := by rfl

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

/-- The actual native free/evaluation adjunction is transported
through the complete original right equivalence. -/
@[no_expose]
def transportedAdjunction (n : I) :
    nativeFreeFunctor.{u, v} n ⊣ nativeEvaluationFunctor.{u, v} n :=
  (EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)).comp
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.symm.toAdjunction

/-- The full actual native adjunction retains the original literal right evaluation endpoint. -/
@[no_expose]
def migratedAdjunction (n : I) :
    nativeFreeFunctor.{u, v} n ⊣ originalEvaluationFunctor.{u, v} n :=
  (transportedAdjunction n).ofNatIsoRight (evaluationIso n)

/-- The actual standard RIGHT Day free and native free compare with their genuine adjunctions. -/
@[no_expose]
def freeComparison (n : I) : originalFreeFunctor.{u, v} n ≅ nativeFreeFunctor.{u, v} n :=
  Adjunction.leftAdjointUniq (originalAdjunction n) (migratedAdjunction n)

/-- The entire original standard right free adjunct is retained. -/
theorem freeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
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

/-- Both inverse adjuncts preserve the same complete original right-module map. -/
theorem freeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : X ⟶ (originalEvaluationFunctor n).obj M) :
    (freeComparison n).hom.app X ≫ ((migratedAdjunction n).homEquiv X M).symm f =
      ((originalAdjunction n).homEquiv X M).symm f := by
  apply ((originalAdjunction n).homEquiv X M).injective
  exact (freeComparison_homEquiv n _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- The entire original standard right free unit is retained. -/
theorem freeComparison_unit (n : I) (X : PointedCGWH.{u, v}) :
    (originalAdjunction n).unit.app X ≫
      (originalEvaluationFunctor n).map ((freeComparison n).hom.app X) =
        (migratedAdjunction n).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The entire original standard right free counit is retained on every original right module. -/
theorem freeComparison_counit (n : I) (M : Carrier.{u, v}) :
    (freeComparison n).hom.app ((originalEvaluationFunctor n).obj M) ≫
      (migratedAdjunction n).counit.app M = (originalAdjunction n).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit (originalAdjunction n) (migratedAdjunction n) M

/-- The standard original right free/evaluation adjunction satisfies both complete triangles. -/
theorem originalAdjunction_free_triangle (n : I) (X : PointedCGWH.{u, v}) :
    (originalFreeFunctor n).map ((originalAdjunction n).unit.app X) ≫
      (originalAdjunction n).counit.app ((originalFreeFunctor n).obj X) = 𝟙 _ :=
  (originalAdjunction n).left_triangle_components X

theorem originalAdjunction_evaluation_triangle (n : I) (M : Carrier.{u, v}) :
    (originalAdjunction n).unit.app ((originalEvaluationFunctor n).obj M) ≫
      (originalEvaluationFunctor n).map ((originalAdjunction n).counit.app M) = 𝟙 _ :=
  (originalAdjunction n).right_triangle_components M

open SymmetricRightModulePresentation in
/-- The actual full transported adjunction retains the complete original composition. -/
theorem transportedAdjunction_heq (n : I) : HEq (transportedAdjunction.{u, v} n)
    ((EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)).comp
      rightModuleOperatorEquivalence.{u, v}.symm.toAdjunction) := by
  unfold transportedAdjunction
  rfl

/-- The actual full migrated adjunction retains the original evaluation comparison. -/
theorem migratedAdjunction_eq (n : I) : migratedAdjunction.{u, v} n =
    (transportedAdjunction n).ofNatIsoRight (evaluationIso n) := by rfl

/-- Every whole original evaluation comparison component is the actual identity value map. -/
theorem evaluationIso_hom_app (n : I) (M : Carrier.{u, v}) :
    HEq ((evaluationIso n).hom.app M) (𝟙 (M.X.functor.obj n)) := by rfl

/-- Every whole inverse evaluation comparison component is the actual identity value map. -/
theorem evaluationIso_inv_app (n : I) (M : Carrier.{u, v}) :
    HEq ((evaluationIso n).inv.app M) (𝟙 (M.X.functor.obj n)) := by rfl

/-- The whole original free comparison uses the actual two original chosen adjunctions. -/
theorem freeComparison_eq (n : I) : freeComparison.{u, v} n =
    Adjunction.leftAdjointUniq (originalAdjunction n) (migratedAdjunction n) := by rfl

/-- The full original transported adjunct uses the actual equivalence unit and free evaluation. -/
theorem transportedAdjunction_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : (nativeFreeFunctor n).obj X ⟶ M) :
    let E := SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
    let a := symmetricOperatorObj.{u, v} n
    HEq ((transportedAdjunction n).homEquiv X M f)
      ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (E.functor.obj M)
        (E.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) ≫
          E.functor.map (eqToHom (congrArg (fun F => F.obj X)
            (nativeFreeFunctor_eq n)).symm ≫ f))) := by
  dsimp only
  have h := homEquivOfEndpointHEq
    (nativeFreeFunctor_eq n) (nativeEvaluationFunctor_eq n)
    (transportedAdjunction_heq n) X M f
  exact h.trans (heq_of_eq (compEquivalenceHomEquiv
    (EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n))
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence X M
    (eqToHom (congrArg (fun F => F.obj X) (nativeFreeFunctor_eq n)).symm ≫ f)))

/-- The full original migrated adjunct retains the entire identity evaluation comparison. -/
theorem migratedAdjunction_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : Carrier.{u, v}}
    (f : (nativeFreeFunctor n).obj X ⟶ M) :
    (migratedAdjunction n).homEquiv X M f =
      (transportedAdjunction n).homEquiv X M f ≫ (evaluationIso n).hom.app M := by
  rw [migratedAdjunction_eq]
  exact Adjunction.homEquiv_ofNatIsoRight_apply _ _ f

end PointedCGWH.SymmetricStandardRightFreeEvaluation
