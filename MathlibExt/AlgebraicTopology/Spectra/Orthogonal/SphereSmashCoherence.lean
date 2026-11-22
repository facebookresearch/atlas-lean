/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmash
import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSelectedSource

/-!
# Coend coherence for the orthogonal sphere smash

With symmetric closed coefficients and the specified colimits, products and equalizers, a
selected enriched right-module presentation supplies unitor, associator and braiding formulas.
These compare primitive coequalizer structures with Day-convolution module structures and retain
free-module generator maps.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uI vI u v
open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule


namespace PointedCGWH.Spectra.Orthogonal.SphereSmash.Internal

namespace SourceTensorDictionaryTransport

universe uC vC uD vD

/-- The complete literal original two-free Iso family, independent of any proof. -/
private def IsoFamily {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] (obj : C → D) (tensor : MonoidalCategory D) :=
  letI := tensor
  ∀ (P Q : C), obj P ⊗ obj Q ≅ obj (P ⊗ Q)

/-- The entire original f/g word on the same object/map DATA, independent of its proof. -/
private def Natural {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] (obj : C → D)
    (map : ∀ {P P' : C}, (P ⟶ P') → (obj P ⟶ obj P'))
    (tensor : MonoidalCategory D) (μ : IsoFamily obj tensor) : Prop :=
  letI := tensor
  ∀ {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q'),
    (map f ⊗ₘ map g) ≫ (μ P' Q').hom =
      (μ P Q).hom ≫ map (f ⊗ₘ g)

/-- Change only the actual whole tensor dictionary, keeping the original entire Iso data. -/
private def moveFamily {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] (obj : C → D)
    (native primitive : MonoidalCategory D) (h : native = primitive)
    (μ : IsoFamily obj primitive) : IsoFamily obj native := by
  cases h
  exact μ

/-- The original full two-arrow proposition travels with the same original entire family. -/
private theorem moveNatural {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] (obj : C → D)
    (map : ∀ {P P' : C}, (P ⟶ P') → (obj P ⟶ obj P'))
    (native primitive : MonoidalCategory D) (h : native = primitive)
    (μ : IsoFamily obj primitive) (hn : Natural obj map primitive μ) :
    Natural obj map native (moveFamily obj native primitive h μ) := by
  cases h
  exact hn

end SourceTensorDictionaryTransport


open scoped MonoidalClosed CategoryTheory.MonObj

namespace RightModuleFree

open CategoryTheory.RightModuleFree

open CommutativeModuleConversion Limits MonoidalCategory MonoidalOpposite
open scoped MonoidalClosed CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The complete left projection type is written from original ambient/scalar data
and tensor data. -/
private def sourceLeftTripleProjectionType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  ∀ (X Y Z : RightModule M), (X.X ⊗ Y.X) ⊗ Z.X ⟶ ((X ⊗ Y) ⊗ Z).X

/-- The complete right projection type is written from those same original source arguments. -/
private def sourceRightTripleProjectionType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  ∀ (X Y Z : RightModule M), X.X ⊗ (Y.X ⊗ Z.X) ⟶ (X ⊗ (Y ⊗ Z)).X

/-- The original relative tensor instance used to type both complete source
triple-projection functions. -/
local instance sourceTripleProjectionMonoidal : MonoidalCategory (RightModule M) := tensorMonoidal M

/-- The original left-associated two-stage quotient projection, at all three modules. -/
private def sourceLeftTripleProjection :
    ∀ (X Y Z : RightModule M),
      (X.X ⊗ Y.X) ⊗ Z.X ⟶ ((X ⊗ Y) ⊗ Z).X :=
  fun X Y Z => (relativeTensorπ M X Y ▷ Z.X) ≫ relativeTensorπ M (X ⊗ Y) Z

/-- The original right-associated two-stage quotient projection, at all three modules. -/
private def sourceRightTripleProjection :
    ∀ (X Y Z : RightModule M),
      X.X ⊗ (Y.X ⊗ Z.X) ⟶ (X ⊗ (Y ⊗ Z)).X :=
  fun X Y Z => (X.X ◁ relativeTensorπ M Y Z) ≫ relativeTensorπ M X (Y ⊗ Z)

/-- The complete left source function has the explicitly written original family TYPE. -/
private def sourceLeftTripleProjectionTyped :
    sourceLeftTripleProjectionType M (tensorMonoidal M) := sourceLeftTripleProjection M

/-- The complete right source function has the explicitly written original family TYPE. -/
private def sourceRightTripleProjectionTyped :
    sourceRightTripleProjectionType M (tensorMonoidal M) := sourceRightTripleProjection M

/-- Transport the whole original left function by its unconditional entire dictionary equality. -/
private def sourceLeftTripleProjectionTransport
    (native primitive : MonoidalCategory (RightModule M)) (h : native = primitive)
    (f : sourceLeftTripleProjectionType M primitive) : sourceLeftTripleProjectionType M native := by
  cases h
  exact f

/-- Transport the whole original right function by the same entire dictionary equality. -/
private def sourceRightTripleProjectionTransport
    (native primitive : MonoidalCategory (RightModule M)) (h : native = primitive)
    (f : sourceRightTripleProjectionType M primitive) :
    sourceRightTripleProjectionType M native := by
  cases h
  exact f


/-- The entire ordinary free-unit Iso type, from the ambient and scalar data. -/
private def sourceFreeUnitType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  freeObject M (𝟙_ C) ≅ 𝟙_ (RightModule M)

/-- Both maps of the original ordinary free-unit constructor, checked before Day data. -/
private def sourceFreeUnit : sourceFreeUnitType M (tensorMonoidal M) :=
  freeTensorUnitIso M

/-- The whole forward carrier equation for an independently typed entire free-unit Iso. -/
private def sourceFreeUnitHomType
    (comparison : sourceFreeUnitType M (tensorMonoidal M)) : Prop :=
  comparison.hom.hom = (λ_ M).hom

/-- The whole inverse carrier equation for that same entire free-unit Iso. -/
private def sourceFreeUnitInvType
    (comparison : sourceFreeUnitType M (tensorMonoidal M)) : Prop :=
  comparison.inv.hom = (λ_ M).inv

/-- The complete original forward carrier law is checked before any selected source. -/
private theorem sourceFreeUnitHom : sourceFreeUnitHomType M (sourceFreeUnit M) :=
  freeTensorUnitIso_hom M

/-- The complete original inverse carrier law is checked before any selected source. -/
private theorem sourceFreeUnitInv : sourceFreeUnitInvType M (sourceFreeUnit M) :=
  freeTensorUnitIso_inv M

end RightModuleFree


namespace OrdinaryPrimitiveUnitor
universe uC vC
open CommutativeModuleConversion
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
/-- The original relative tensor types the complete generic left-unit characteristic. -/
local instance : MonoidalCategory (RightModule M) := RightModuleFree.tensorMonoidal M
/-- The complete original left-unit characteristic at arbitrary original ambient and scalar data. -/
private def LeftFullType : Prop := ∀ X : RightModule M,
  RightModuleFree.relativeTensorπ M (𝟙_ (RightModule M)) X ≫ (λ_ X).hom.hom =
    CommutativeModuleConversion.leftAction M X
/-- The original primitive source proof is checked at the complete independently written family. -/
private theorem leftCanonical : LeftFullType M := RightModuleFree.relativeTensorLeftUnitor_hom_π M

/-- The complete original right-unit characteristic at arbitrary ambient and scalar data. -/
private def RightFullType : Prop := ∀ X : RightModule M,
  RightModuleFree.relativeTensorπ M X (𝟙_ (RightModule M)) ≫ (ρ_ X).hom.hom =
    ModObj.smul (M := mop M) (X := X.X)

/-- The whole original right-unit law is checked before any Day or selected source data. -/
private theorem rightCanonical : RightFullType M := by
  intro X
  exact RightModuleFree.relativeTensorRightUnitor_hom_π M X

/-- The complete original projection braid law at arbitrary ambient and scalar data. -/
private def BraidingFullType : Prop :=
  letI := RightModuleFree.tensorSymmetric M
  ∀ (X Y : RightModule M),
    RightModuleFree.relativeTensorπ M X Y ≫ (β_ X Y).hom.hom =
      (β_ X.X Y.X).hom ≫ RightModuleFree.relativeTensorπ M Y X

/-- The complete two-module projection family for an actual whole right-module tensor. -/
private def UnitorProjectionType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  ∀ (X Y : RightModule M), X.X ⊗ Y.X ⟶ (X ⊗ Y).X

/-- The complete action family on the actual carrier of an entire tensor's unit. -/
private def UnitorActionType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  ∀ X : RightModule M, (𝟙_ (RightModule M)).X ⊗ X.X ⟶ X.X

/-- The whole original homogeneous left equation with its complete actual action family. -/
private def LeftWithProjectionType (tensor : MonoidalCategory (RightModule M))
    (projection : UnitorProjectionType M tensor) (action : UnitorActionType M tensor) : Prop :=
  letI := tensor
  ∀ X : RightModule M,
    projection (𝟙_ (RightModule M)) X ≫ (λ_ X).hom.hom = action X

/-- The original primitive quotient at its separately written complete family. -/
private def unitorCanonicalProjection : UnitorProjectionType M (RightModuleFree.tensorMonoidal M) :=
  RightModuleFree.relativeTensorπ M

/-- The original complete left action at the actual primitive unit carrier. -/
private def unitorCanonicalAction : UnitorActionType M (RightModuleFree.tensorMonoidal M) :=
  fun X => CommutativeModuleConversion.leftAction M X

/-- The original left supplier has the whole characteristic at the actual projection and action. -/
private theorem leftWithProjectionCanonical :
    LeftWithProjectionType M (RightModuleFree.tensorMonoidal M)
      (unitorCanonicalProjection M) (unitorCanonicalAction M) :=
  leftCanonical M

/-- Transport the entire actual quotient function through a whole tensor equality. -/
private def unitorProjectionTransport (native primitive : MonoidalCategory (RightModule M))
    (h : native = primitive) (projection : UnitorProjectionType M primitive) :
    UnitorProjectionType M native := by
  cases h
  exact projection

/-- Transport the entire actual left action through the same whole tensor equality. -/
private def unitorActionTransport (native primitive : MonoidalCategory (RightModule M))
    (h : native = primitive) (action : UnitorActionType M primitive) :
    UnitorActionType M native := by
  cases h
  exact action

omit [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Transport the entire homogeneous left equation with the same quotient and action families. -/
private theorem leftWithProjectionTransport (native primitive : MonoidalCategory (RightModule M))
    (h : native = primitive) (projection : UnitorProjectionType M primitive)
    (action : UnitorActionType M primitive)
    (hleft : LeftWithProjectionType M primitive projection action) :
    LeftWithProjectionType M native
      (unitorProjectionTransport M native primitive h projection)
      (unitorActionTransport M native primitive h action) := by
  cases h
  exact hleft

end OrdinaryPrimitiveUnitor

namespace OrdinaryPrimitiveTripleAssociator
universe uC vC
open CommutativeModuleConversion
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
/-- The original relative tensor types the complete generic associator characteristic. -/
local instance : MonoidalCategory (RightModule M) := RightModuleFree.tensorMonoidal M

/-- The complete original associator law at the original ambient and scalar data. -/
private def FullType : Prop :=
  ∀ (X Y Z : RightModule M),
    (RightModuleFree.relativeTensorπ M X Y ▷ Z.X) ≫
        RightModuleFree.relativeTensorπ M (X ⊗ Y) Z ≫ (α_ X Y Z).hom.hom =
      (α_ X.X Y.X Z.X).hom ≫ (X.X ◁ RightModuleFree.relativeTensorπ M Y Z) ≫
        RightModuleFree.relativeTensorπ M X (Y ⊗ Z)

/-- The original canonical proof is checked at the independently written complete family. -/
private theorem canonical : FullType M := RightModuleFree.relativeTensorAssociator_hom_π M

/-- The entire original two-module quotient function at an actual whole tensor dictionary. -/
private def ProjectionType (tensor : MonoidalCategory (RightModule M)) : Type _ :=
  letI := tensor
  ∀ (X Y : RightModule M), X.X ⊗ Y.X ⟶ (X ⊗ Y).X

/-- The full associator word uses the same whole projection at both inner and outer tensors. -/
private def WithProjectionType (tensor : MonoidalCategory (RightModule M))
    (projection : ProjectionType M tensor) : Prop :=
  letI := tensor
  ∀ (X Y Z : RightModule M),
    (projection X Y ▷ Z.X) ≫ projection (X ⊗ Y) Z ≫ (α_ X Y Z).hom.hom =
      (α_ X.X Y.X Z.X).hom ≫ (X.X ◁ projection Y Z) ≫ projection X (Y ⊗ Z)

/-- The canonical quotient is checked at its independently written complete projection type. -/
private def canonicalProjection : ProjectionType M (RightModuleFree.tensorMonoidal M) :=
  RightModuleFree.relativeTensorπ M

/-- The canonical complete law uses that same whole original quotient family. -/
private theorem withProjectionCanonical :
    WithProjectionType M (RightModuleFree.tensorMonoidal M) (canonicalProjection M) :=
  canonical M

/-- Move the entire original quotient function by the actual whole tensor equality. -/
private def projectionTransport (native primitive : MonoidalCategory (RightModule M))
    (h : native = primitive) (projection : ProjectionType M primitive) :
    ProjectionType M native := by
  cases h
  exact projection

omit [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Move the complete original associator law together with its whole quotient family. -/
private theorem withProjectionTransport (native primitive : MonoidalCategory (RightModule M))
    (h : native = primitive) (projection : ProjectionType M primitive)
    (hassoc : WithProjectionType M primitive projection) :
    WithProjectionType M native (projectionTransport M native primitive h projection) := by
  cases h
  exact hassoc

end OrdinaryPrimitiveTripleAssociator

end PointedCGWH.Spectra.Orthogonal.SphereSmash.Internal

open scoped MonoidalClosed CategoryTheory.MonObj

-- The complete original limit witnesses for all inner and outer Day diagrams.
namespace PointedCGWH.Spectra.Orthogonal.SphereSmash.TypedCoherence.NestedAssociatorFormula
open CategoryTheory.Enriched EnrichedDayKernel
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] ColimitMonoidal.smallestColimits
theorem innerRelationsColimit.{u_1, u_2, u_3, u_4}
    {V : Type u_3} [Category.{u_2} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_1} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_1, u_1} V] [HasProducts.{u_1} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y : q.Module) (m : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoproduct (relations q.monoidalData.tensorEnrichedFunctor
      X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance

theorem innerObjectsColimit.{u_1, u_2, u_3, u_4}
    {V : Type u_3} [Category.{u_2} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_1} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_1, u_1} V] [HasProducts.{u_1} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y : q.Module) (m : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoproduct (objects q.monoidalData.tensorEnrichedFunctor
      X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance

theorem innerCoendCoequalizer.{u_1, u_2, u_3, u_4}
    {V : Type u_2} [Category.{u_1} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_3} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_3, u_3} V] [HasProducts.{u_3} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y : q.Module) (m : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoequalizer (leftMap q.monoidalData.tensorEnrichedFunctor
      X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m)
    (rightMap q.monoidalData.tensorEnrichedFunctor
      X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance

theorem outerRelationsColimit.{u_1, u_2, u_3, u_4}
    {V : Type u_3} [Category.{u_2} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_1} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_1, u_1} V] [HasProducts.{u_1} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y Z : q.Module) (k : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoproduct (relations q.monoidalData.tensorEnrichedFunctor
      (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance

theorem outerObjectsColimit.{u_1, u_2, u_3, u_4}
    {V : Type u_3} [Category.{u_2} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_1} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_1, u_1} V] [HasProducts.{u_1} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y Z : q.Module) (k : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoproduct (objects q.monoidalData.tensorEnrichedFunctor
      (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance

theorem outerCoendCoequalizer.{u_1, u_2, u_3, u_4}
    {V : Type u_2} [Category.{u_1} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
    {I : Type u_3} [Category.{u_4} I] [MonoidalCategory I] [SymmetricCategory I]
    [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{u_3, u_3} V] [HasProducts.{u_3} V] [HasEqualizers V]
    (q : Enriched.ModuleMappingR.SelectedSource V I) (X Y Z : q.Module) (k : I) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  HasCoequalizer (leftMap q.monoidalData.tensorEnrichedFunctor
      (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k)
    (rightMap q.monoidalData.tensorEnrichedFunctor
      (X.X ⊗ Y.X).toEnrichedFunctor Z.X.toEnrichedFunctor k) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  infer_instance
end PointedCGWH.Spectra.Orthogonal.SphereSmash.TypedCoherence.NestedAssociatorFormula

namespace PointedCGWH.Spectra.Orthogonal.SphereSmash.TypedCoherence
open PointedCGWH.Spectra.Orthogonal.SphereSmash.Internal
open CategoryTheory.Enriched.ModuleMappingR
open CategoryTheory.Enriched EnrichedDayKernel
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
    [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (q : SelectedSource V I)



/-- The original whole projection braid law at the full Day and coefficient data. -/
def OriginalProjectionBraidingType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  letI := RightModuleFree.tensorSymmetric (⟨S⟩ : EnrichedFunctorCat V I)
  OrdinaryPrimitiveUnitor.BraidingFullType (⟨S⟩ : EnrichedFunctorCat V I)

/-- The canonical complete supplier is checked at its independently written original type. -/
theorem originalProjectionBraiding (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) :
    OriginalProjectionBraidingType d b S L B := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  let := RightModuleFree.tensorSymmetric (⟨S⟩ : EnrichedFunctorCat V I)
  exact RightModuleFree.relativeTensorBraiding_hom_π (⟨S⟩ : EnrichedFunctorCat V I)


/-- The complete original source OriginalLeftUnitorType at symbolic Day and coefficient data. -/
def OriginalLeftUnitorType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  letI : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  OrdinaryPrimitiveUnitor.LeftFullType (⟨S⟩ : EnrichedFunctorCat V I)

/-- The canonical supplier is independently typed with the full original statement. -/
theorem originalLeftUnitor (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : OriginalLeftUnitorType d b S L B := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  exact OrdinaryPrimitiveUnitor.leftCanonical (⟨S⟩ : EnrichedFunctorCat V I)

/-- The complete original source OriginalRightUnitorType at symbolic Day and coefficient data. -/
def OriginalRightUnitorType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  letI : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  letI := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  OrdinaryPrimitiveUnitor.RightFullType (⟨S⟩ : EnrichedFunctorCat V I)

/-- The canonical supplier is independently typed with the full original statement. -/
theorem originalRightUnitor (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : OriginalRightUnitorType d b S L B := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0,0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  let := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  exact OrdinaryPrimitiveUnitor.rightCanonical (⟨S⟩ : EnrichedFunctorCat V I)

/-- The full original primitive quotient type at actual selected coefficient and tensor data. -/
def PrimitiveUnitorProjectionType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  OrdinaryPrimitiveUnitor.UnitorProjectionType q.coefficient q.primitiveMonoidal

/-- The complete original primitive quotient at its independently written full type. -/
def primitiveUnitorProjection : PrimitiveUnitorProjectionType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  exact OrdinaryPrimitiveUnitor.unitorCanonicalProjection q.coefficient

/-- The transported entire projection is the original selected quotient function. -/
theorem projection_eq_unitorTransport :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.dayCoequalizers
    letI := q.dayTensorLeftPreserves
    letI := q.dayTensorRightPreserves
    q.projection =
      OrdinaryPrimitiveUnitor.unitorProjectionTransport q.coefficient q.moduleMonoidal
        q.primitiveMonoidal q.moduleMonoidal_eq_primitive (primitiveUnitorProjection q) := by
  rfl

/-- The complete primitive action-family type at the actual selected coefficient. -/
def PrimitiveUnitorActionType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  OrdinaryPrimitiveUnitor.UnitorActionType q.coefficient q.primitiveMonoidal

/-- The original full left-action family at the actual selected primitive tensor. -/
def primitiveUnitorAction : PrimitiveUnitorActionType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  exact OrdinaryPrimitiveUnitor.unitorCanonicalAction q.coefficient

/-- The complete action-family type at the actual selected whole source tensor. -/
def NativeUnitorActionType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  OrdinaryPrimitiveUnitor.UnitorActionType q.coefficient q.moduleMonoidal

/-- The original full left-action family at the actual selected source tensor. -/
def nativeUnitorAction : NativeUnitorActionType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  exact fun X => CommutativeModuleConversion.leftAction q.coefficient X

/-- The transported entire action is the original selected coefficient's left action. -/
theorem action_eq_unitorTransport :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.dayCoequalizers
    letI := q.dayTensorLeftPreserves
    letI := q.dayTensorRightPreserves
    nativeUnitorAction q =
      OrdinaryPrimitiveUnitor.unitorActionTransport q.coefficient q.moduleMonoidal
        q.primitiveMonoidal q.moduleMonoidal_eq_primitive (primitiveUnitorAction q) := by
  rfl

/-- The full primitive left characteristic at all actual selected source modules. -/
theorem primitiveUnitorLeft :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.dayCoequalizers
    letI := q.dayTensorLeftPreserves
    letI := q.dayTensorRightPreserves
    OrdinaryPrimitiveUnitor.LeftWithProjectionType q.coefficient q.primitiveMonoidal
      (primitiveUnitorProjection q) (primitiveUnitorAction q) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  exact OrdinaryPrimitiveUnitor.leftWithProjectionCanonical q.coefficient

/-- The entire original primitive quotient type retains all selected source data. -/
def PrimitiveTripleProjectionType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  OrdinaryPrimitiveTripleAssociator.ProjectionType q.coefficient q.primitiveMonoidal

/-- The original canonical whole quotient is checked at that complete selected type. -/
def primitiveTripleProjection : PrimitiveTripleProjectionType q := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  exact OrdinaryPrimitiveTripleAssociator.canonicalProjection q.coefficient

/-- The transported entire quotient is the original selected full projection function. -/
theorem projection_eq_tripleTransport :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.dayCoequalizers
    letI := q.dayTensorLeftPreserves
    letI := q.dayTensorRightPreserves
    q.projection =
      OrdinaryPrimitiveTripleAssociator.projectionTransport q.coefficient q.moduleMonoidal
        q.primitiveMonoidal q.moduleMonoidal_eq_primitive (primitiveTripleProjection q) := by
  rfl

/-- The complete primitive associator characteristic at all three actual selected modules. -/
theorem primitiveTripleAssociatorWithProjection :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.dayCoequalizers
    letI := q.dayTensorLeftPreserves
    letI := q.dayTensorRightPreserves
    OrdinaryPrimitiveTripleAssociator.WithProjectionType q.coefficient q.primitiveMonoidal
      (primitiveTripleProjection q) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  exact OrdinaryPrimitiveTripleAssociator.withProjectionCanonical q.coefficient

/-- The complete original left two-stage quotient type at selected source data. -/
def LeftTripleType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  Internal.RightModuleFree.sourceLeftTripleProjectionType q.coefficient q.moduleMonoidal

/-- Both original left quotient maps, without a caller tensor premise. -/
def leftTriple : LeftTripleType q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact Internal.RightModuleFree.sourceLeftTripleProjectionTransport q.coefficient
    q.moduleMonoidal q.primitiveMonoidal q.moduleMonoidal_eq_primitive
    (Internal.RightModuleFree.sourceLeftTripleProjectionTyped q.coefficient)


/-- The complete original right two-stage quotient type at selected source data. -/
def RightTripleType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  Internal.RightModuleFree.sourceRightTripleProjectionType q.coefficient q.moduleMonoidal

/-- Both original right quotient maps at their original tensor objects. -/
def rightTriple : RightTripleType q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact Internal.RightModuleFree.sourceRightTripleProjectionTransport q.coefficient
    q.moduleMonoidal q.primitiveMonoidal q.moduleMonoidal_eq_primitive
    (Internal.RightModuleFree.sourceRightTripleProjectionTyped q.coefficient)


/-- The whole original source associator characteristic on unquotiented tensors. -/
def TripleAssociatorFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  OrdinaryPrimitiveTripleAssociator.WithProjectionType q.coefficient q.moduleMonoidal q.projection

/-- The actual original relative tensor supplies the complete source associator law. -/
theorem tripleAssociator : TripleAssociatorFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  have h := OrdinaryPrimitiveTripleAssociator.withProjectionTransport q.coefficient
    q.moduleMonoidal q.primitiveMonoidal q.moduleMonoidal_eq_primitive
    (primitiveTripleProjection q) (primitiveTripleAssociatorWithProjection q)
  rw [← projection_eq_tripleTransport q] at h
  exact h

/-- The complete original nested family, independently written at all Day and scalar inputs. -/
def OriginalLeftNestedType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : Type _ :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  letI : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) :=
    RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  ∀ (X Y Z : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
    (k m n : I) (a : I × I),
    (d.tensorEnrichedFunctor.obj (m, n) ⟶[V] k) ⊗
      (objects d.tensorEnrichedFunctor X.X.toEnrichedFunctor Y.X.toEnrichedFunctor m a ⊗
        Z.X.toEnrichedFunctor.obj n) ⟶ ((X ⊗ Y) ⊗ Z).X.toEnrichedFunctor.obj k

/-- Both original quotient maps and all coefficients are checked at the full generic family. -/
def originalLeftNested (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d)
    (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) : OriginalLeftNestedType d b S L B := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  let : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) :=
    RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
  exact SphereSmashStructure.Internal.leftNestedCoendGenerator d b S L B

/-- Every inner and outer Day coefficient remains in the original nested integrand. -/
def LeftNestedType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  OriginalLeftNestedType q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided

/-- The original complete nested generator, using only named selected source data. -/
def leftNested : LeftNestedType q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact originalLeftNested q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided


/-- Associativity retains every original inner/outer coefficient and both quotient maps. -/
def NestedAssociatorFormula : Prop :=
  SphereSmashStructure.Internal.leftNestedCoendGeneratorAssociatorType
    q.monoidalData q.braidedData q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided

set_option maxHeartbeats 400000 in
/-- The full original source associator proof specializes the named record data. -/
theorem nestedAssociator : NestedAssociatorFormula q :=
  SphereSmashStructure.Internal.leftNestedCoendGenerator_associator
    q.monoidalData q.braidedData q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided

/-- The entire original left-unit projection equation on each actual source module. -/
def LeftUnitorFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  OrdinaryPrimitiveUnitor.LeftWithProjectionType q.coefficient q.moduleMonoidal
    q.projection (nativeUnitorAction q)

/-- The actual converted source action is the original left-unit characteristic. -/
theorem leftUnitor : LeftUnitorFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  have h := OrdinaryPrimitiveUnitor.leftWithProjectionTransport q.coefficient
    q.moduleMonoidal q.primitiveMonoidal q.moduleMonoidal_eq_primitive
    (primitiveUnitorProjection q) (primitiveUnitorAction q) (primitiveUnitorLeft q)
  rw [← projection_eq_unitorTransport q, ← action_eq_unitorTransport q] at h
  exact h

/-- The entire original right-unit projection equation on each actual source module. -/
def RightUnitorFormula : Prop :=
  OriginalRightUnitorType q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

set_option maxHeartbeats 400000 in
/-- The whole original right source action is the right-unit characteristic. -/
theorem rightUnitor : RightUnitorFormula q :=
  originalRightUnitor q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

/-- The original source regular-module identity, retaining the actual sphere coefficient. -/
def UnitRegularFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  (𝟙_ q.Module) = CommutativeModuleConversion.toRight q.coefficient (Mod.regular q.coefficient)

/-- The complete original source unit is the same converted regular module. -/
theorem unitRegular : UnitRegularFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact RightModuleFree.tensorUnit_eq q.coefficient

/-- The entire source tensor unit carrier remains the original coefficient object. -/
def UnitCarrierFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  (𝟙_ q.Module).X = q.coefficient

/-- The original whole tensor unit has the actual original coefficient carrier. -/
theorem unitCarrier : UnitCarrierFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact rfl

/-- The original full ambient braid descends through both source quotients. -/
def ProjectionBraidingFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  OrdinaryPrimitiveUnitor.BraidingFullType q.coefficient

/-- The canonical source braiding supplies that complete projection equation. -/
theorem projectionBraiding : ProjectionBraidingFormula q :=
  originalProjectionBraiding q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided


/-- Every original Day coefficient and both input values in the source generator. -/
def CoendType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  ∀ (X Y : q.Module) (k : I) (a : I × I),
  objects q.monoidalData.tensorEnrichedFunctor X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ⟶
    (X ⊗ Y).X.toEnrichedFunctor.obj k

/-- The original source coend generator at every selected tensor datum. -/
def coend : CoendType q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact q.coendGenerator

/-- The whole original inverse-index and value braid acts on every isometry integrand. -/
def GeneratorBraidingFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  ∀ (X Y : q.Module) (k : I) (a : I × I),
  coend q X Y k a ≫ EnrichedFunctorCat.component (β_ X Y).hom.hom k =
    (eHomWhiskerRight V (β_ a.1 a.2).inv k ⊗ₘ
      (β_ (X.X.toEnrichedFunctor.obj a.1) (Y.X.toEnrichedFunctor.obj a.2)).hom) ≫
      coend q Y X k (a.2,a.1)

/-- The complete original coend-braiding proof uses every named source record datum. -/
theorem generatorBraiding : GeneratorBraidingFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  have h : GeneratorBraidingFormula q :=
    SphereSmashStructure.Internal.coendGenerator_braiding q.monoidalData q.braidedData
      q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
  simpa only [GeneratorBraidingFormula, coend] using h

/-- The whole original two-free Iso family with the selected actual tensor. -/
def FreeIsoType (tensor : @MonoidalCategory q.Module q.moduleCategory) :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  letI := tensor
  ∀ (P Q : EnrichedFunctorCat V I), RightModuleFree.freeObject q.coefficient P ⊗
    RightModuleFree.freeObject q.coefficient Q ≅ RightModuleFree.freeObject q.coefficient (P ⊗ Q)

/-- The original complete two-free comparison in the original primitive context. -/
def primitiveFreeIso : FreeIsoType q q.primitiveMonoidal := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact RightModuleFree.freeTensorIso q.coefficient

/-- The original same entire comparison, at the selected source tensor. -/
def freeIso : FreeIsoType q q.moduleMonoidal :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  primitiveFreeIso q

/-- The original full free source unit comparison. -/
def FreeUnitType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  Internal.RightModuleFree.sourceFreeUnitType q.coefficient
    (RightModuleFree.tensorMonoidal q.coefficient)

/-- Both original source free-unit maps remain in this complete Iso. -/
def freeUnit : FreeUnitType q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact Internal.RightModuleFree.sourceFreeUnit q.coefficient


/-- The exact entire forward free-unit carrier map is the original Day left unitor. -/
def FreeUnitHomFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  Internal.RightModuleFree.sourceFreeUnitHomType q.coefficient (freeUnit q)

/-- The original whole forward-unit law. -/
theorem freeUnitHom : FreeUnitHomFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact Internal.RightModuleFree.sourceFreeUnitHom q.coefficient


/-- The exact entire inverse free-unit carrier map is the original inverse Day left unitor. -/
def FreeUnitInvFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  Internal.RightModuleFree.sourceFreeUnitInvType q.coefficient (freeUnit q)

/-- The original whole inverse-unit law. -/
theorem freeUnitInv : FreeUnitInvFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact Internal.RightModuleFree.sourceFreeUnitInv q.coefficient


/-- The complete original CoreMonoidal type of the actual original free source functor. -/
def FreeCoreType :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  (RightModuleFree.functor q.coefficient).CoreMonoidal

/-- Original complete unit/tensor/naturality/associativity data of the free source functor. -/
def freeCore : FreeCoreType q :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  RightModuleFree.freeTensorCoreMonoidal q.coefficient

/-- Both entire coefficient factors are multiplied by the original two-free forward map. -/
def FreeIsoHomFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  ∀ (P Q : EnrichedFunctorCat V I),
    RightModuleFree.FreeTensorHomFormula q.coefficient P Q

/-- The complete original two-free multiplication equation. -/
theorem freeIsoHom : FreeIsoHomFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact RightModuleFree.freeTensorIso_hom_π q.coefficient

/-- The whole original inverse comparison keeps its first source generator and quotient. -/
def FreeIsoInvFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  ∀ (P Q : EnrichedFunctorCat V I),
    RightModuleFree.FreeTensorInvFormula q.coefficient P Q

/-- The complete original inverse two-free equation. -/
theorem freeIsoInv : FreeIsoInvFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact RightModuleFree.freeTensorIso_inv q.coefficient

/-- The complete homogeneous two-arrow naturality word, with all four objects implicit. -/
def FreeNaturalFormula (tensor : @MonoidalCategory q.Module q.moduleCategory)
    (comparison : FreeIsoType q tensor) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  letI := tensor
  ∀ {P P' Q Q' : EnrichedFunctorCat V I} (f : P ⟶ P') (g : Q ⟶ Q'),
    (RightModuleFree.freeMap q.coefficient f ⊗ₘ RightModuleFree.freeMap q.coefficient g) ≫
      (comparison P' Q').hom = (comparison P Q).hom ≫ RightModuleFree.freeMap q.coefficient (f ⊗ₘ g)

/-- The complete original two-arrow family at the original primitive tensor. -/
def OriginalFreeNaturalityFormula : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  ∀ {P P' Q Q' : EnrichedFunctorCat V I} (f : P ⟶ P') (g : Q ⟶ Q'),
    RightModuleFree.FreeTensorNaturalityFormula q.coefficient f g

/-- Both full primitive source arrows retain the original entire Iso family. -/
theorem primitiveFreeNatural : OriginalFreeNaturalityFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  let := q.primitiveMonoidal
  intro P P' Q Q' f g
  exact CategoryTheory.RightModuleFree.freeTensorIso_naturality q.coefficient f g


/-- Both full actual source arrows retain the same entire Iso family. -/
theorem freeNatural : OriginalFreeNaturalityFormula q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  intro P P' Q Q' f g
  exact (@primitiveFreeNatural V _ _ _ _ I _ _ _ _ _ _ _ q) f g

/-- The whole ambient associator Iso is the original continuous coend comparison,
at the independent selected source before native specialization. -/
def AmbientAssociatorFormula (X Y Z : q.Module) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  (α_ X.X Y.X Z.X) = AssociatorConstruction.functorIso q.monoidalData
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor Z.X.toEnrichedFunctor

/-- The original Day supplier proves the full Iso-record equality at that source. -/
theorem ambientAssociator (X Y Z : q.Module) : AmbientAssociatorFormula q X Y Z := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact ColimitMonoidal.associator_eq q.monoidalData X.X Y.X Z.X

end PointedCGWH.Spectra.Orthogonal.SphereSmash.TypedCoherence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

namespace PointedCGWH.Spectra.Orthogonal.SphereSmash

/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := SphereSmashStructure.indexCategory.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex :=
  SphereSmashStructure.indexMonoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  SphereSmashStructure.indexEnrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex :=
  SphereSmashStructure.indexSymmetricCategory.{u, v}
attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The proved native pointed limits supply the original small mapping-end shapes. -/
local instance nativeSmallLimits : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- All original small products follow from that same actual native limit proof. -/
theorem nativeSmallProducts : HasProducts.{0} PointedCGWH.{u, v} := inferInstance

/-- The original equalizers follow from that same actual native limit proof. -/
theorem nativeSmallEqualizers : HasEqualizers PointedCGWH.{u, v} := inferInstance


private abbrev NativeCoefficient := PointedCGWH.{u, v}
private abbrev Modules := NativeSphereModule.Carrier.{u, v}

/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance instMonoidalCategoryISpace_1 :
    MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance instSymmetricCategoryISpace_1 :
    SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}

local instance instHasCoequalizersISpace_1 :
    HasCoequalizers (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.hasCoequalizers.{u, v}
/-- The canonical relative sphere tensor on the original source modules. -/
local instance : MonoidalCategory Modules.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}
/-- The canonical relative sphere symmetry on the same source modules. -/
local instance : SymmetricCategory Modules.{u, v} :=
  SphereSmashStructure.symmetricCategory.{u, v}


/-- The iterated projection in the left-associated source smash. -/
def leftTripleProjection : TypedCoherence.LeftTripleType sourceData.{u,v} :=
  TypedCoherence.leftTriple sourceData.{u,v}
/-- The iterated projection in the right-associated source smash. -/
def rightTripleProjection : TypedCoherence.RightTripleType sourceData.{u,v} :=
  TypedCoherence.rightTriple sourceData.{u,v}
/-- The actual source associator is characterized on the entire unquotiented tensor word. -/
abbrev tripleProjectionAssociator : TypedCoherence.TripleAssociatorFormula sourceData.{u,v} :=
  TypedCoherence.tripleAssociator sourceData.{u,v}
/-- The ambient associator is the complete original continuous coend comparison. -/
abbrev ambientAssociatorEqCoend (X Y Z : Modules.{u, v}) :
    TypedCoherence.AmbientAssociatorFormula sourceData.{u,v} X Y Z :=
  TypedCoherence.ambientAssociator sourceData.{u,v} X Y Z
/-- The two-stage continuous left integrand keeps its outer and inner isometry coefficients. -/
abbrev leftNestedIntegrand (X Y Z : Modules.{u, v}) (k m n : OrthogonalIndex)
    (a : OrthogonalIndex × OrthogonalIndex) : NativeCoefficient.{u,v} :=
  OrthogonalIndex.hom.{u,v} (m+n) k ⊗ (integrand X Y m a ⊗ Z.X.toEnrichedFunctor.obj n)
/-- Insert every inner Day generator into every outer Day generator, then project twice.
Its complete native type retains the entire original source generator family. -/
def leftNestedGenerator : TypedCoherence.LeftNestedType sourceData.{u,v} :=
  TypedCoherence.leftNested sourceData.{u,v}
/-- Associativity conserves each complete nested coend integrand through the original Day map. -/
abbrev leftNestedGeneratorAssociator : TypedCoherence.NestedAssociatorFormula sourceData.{u,v} :=
  TypedCoherence.nestedAssociator sourceData.{u,v}
/-- The actual source left unitor contracts the converted full left sphere action. -/
abbrev projectionLeftUnitor : TypedCoherence.LeftUnitorFormula sourceData.{u,v} :=
  TypedCoherence.leftUnitor sourceData.{u,v}
/-- The actual source right unitor contracts the original full right sphere action. -/
abbrev projectionRightUnitor : TypedCoherence.RightUnitorFormula sourceData.{u,v} :=
  TypedCoherence.rightUnitor sourceData.{u,v}
/-- The complete smash unit retains the original representation-sphere space. -/
theorem unitCarrier : TypedCoherence.UnitCarrierFormula sourceData.{u,v} := by
  rfl
/-- The source unit is the actual converted regular sphere module. -/
abbrev unitEqRegular : TypedCoherence.UnitRegularFormula sourceData.{u,v} :=
  TypedCoherence.unitRegular sourceData.{u,v}
/-- The complete original Day braid descends through the relative sphere projection. -/
abbrev projectionBraiding : TypedCoherence.ProjectionBraidingFormula sourceData.{u,v} :=
  TypedCoherence.projectionBraiding sourceData.{u,v}
/-- The whole source braid on each integrand retains the inverse native block isometry. -/
abbrev generatorBraiding : TypedCoherence.GeneratorBraidingFormula sourceData.{u,v} :=
  TypedCoherence.generatorBraiding sourceData.{u,v}
/-- The complete original primitive source Iso family used by the actual native comparison. -/
abbrev primitiveFreeTensorIso :
    TypedCoherence.FreeIsoType sourceData.{u,v} (sourceData.{u,v}).primitiveMonoidal :=
  TypedCoherence.primitiveFreeIso sourceData.{u,v}
/-- The same original entire Iso family, transported along the actual dictionary equality. -/
abbrev freeTensorIso :
    TypedCoherence.FreeIsoType sourceData.{u,v} (sourceData.{u,v}).moduleMonoidal :=
  TypedCoherence.freeIso sourceData.{u,v}
/-- The complete free sphere unit comparison uses the original Day unitor of the sphere. -/
abbrev freeUnitIso : TypedCoherence.FreeUnitType sourceData.{u,v} :=
  TypedCoherence.freeUnit sourceData.{u,v}
/-- Its forward carrier map is exactly the original sphere Day left unitor. -/
abbrev freeUnitIsoHom : TypedCoherence.FreeUnitHomFormula sourceData.{u,v} :=
  TypedCoherence.freeUnitHom sourceData.{u,v}
/-- Its inverse carrier map is exactly the inverse of that same sphere Day unitor. -/
abbrev freeUnitIsoInv : TypedCoherence.FreeUnitInvFormula sourceData.{u,v} :=
  TypedCoherence.freeUnitInv sourceData.{u,v}
/-- The full native free functor carries the original source tensor and unit coherence. -/
def freeCoreMonoidal : TypedCoherence.FreeCoreType sourceData.{u,v} :=
  TypedCoherence.freeCore sourceData.{u,v}
/-- Every actual two-free quotient map multiplies both entire sphere coefficients. -/
abbrev freeTensorIsoHomProjection : TypedCoherence.FreeIsoHomFormula sourceData.{u,v} :=
  TypedCoherence.freeIsoHom sourceData.{u,v}
/-- The complete inverse two-free comparison retains the original generator and quotient. -/
abbrev freeTensorIsoInv : TypedCoherence.FreeIsoInvFormula sourceData.{u,v} :=
  TypedCoherence.freeIsoInv sourceData.{u,v}
/-- The complete original two-arrow equation in its actual primitive source context. -/
theorem primitiveFreeTensorNaturality :
    TypedCoherence.OriginalFreeNaturalityFormula sourceData.{u,v} :=
  @TypedCoherence.primitiveFreeNatural _ _ _ _ _ _ _ _ _ _ _ _ _ sourceData.{u,v}
/-- The entire original P/P'/Q/Q'/f/g formula retains the same actual Iso and source arrows. -/
theorem freeTensorIsoNaturality :
    TypedCoherence.OriginalFreeNaturalityFormula sourceData.{u,v} :=
  @TypedCoherence.freeNatural _ _ _ _ _ _ _ _ _ _ _ _ _ sourceData.{u,v}
end PointedCGWH.Spectra.Orthogonal.SphereSmash
