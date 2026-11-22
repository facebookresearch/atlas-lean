/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.OrdinalCompactness
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedOrdinalSources
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StructuredSourceSmallness

/-!
# Original native free-R sources on closed ordinal diagrams

The compact separable realized source is transported through the actual
costar, native standard-right-free and R-module free adjunctions. Each given
closed diagram and each original cocone is retained. No stable R-model,
unrestricted filtered compactness, or homotopy-extension assertion is used.
-/

set_option autoImplicit false
noncomputable section

universe u v w
universe uC vC uD vD

open CategoryTheory Limits MorphismProperty Topology TopologicalSpace
open CategoryTheory.EnrichedFunctorCat
open CGWH
open scoped Simplicial MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.NativeRModuleOrdinalSources

private def endpointProperty {D : Type uD} [Category.{vD} D] (H : D → Prop) :
    MorphismProperty D := fun A B _ => H A ∧ H B

/-- Endpoint properties pull back through the actual object part of a
functor, without unfolding its concrete morphism implementation. -/
private theorem inverseImage_endpoints
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (H : D → Prop) :
    (endpointProperty H).inverseImage F = endpointProperty (fun A => H (F.obj A)) := rfl

section LiteralModules

/-- The original native sphere-module carrier. -/
abbrev NativeCarrier := PointedCGWH.StructuredSourceSmallness.NativeCarrier.{u, v}

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

variable (R : CommMon NativeCarrier.{u, v})

/-- Modules over the original commutative native coefficient R. -/
abbrev ModuleCarrier := Mod NativeCarrier.{u, v} R.X

/-- Closedness is tested by the original R-module forgetful functor on
the same actual native operator values. -/
def moduleClosedInclusions : MorphismProperty (ModuleCarrier R) :=
  NativeClosedCellHistory.closedInclusions.inverseImage (Mod.forget R.X)

/-- The literal costar/free-native/free-R source Hom preserves every
original bottomed linear diagram with closed double-forgotten maps. -/
theorem originalFreeModule_preservesClosedLinearColimit
    (n : Operad.SmallFinBijGroupoid) (A : CGWH.{u, v}) [CompactSpace A] [SeparableSpace A]
    {O : Type v} [LinearOrder O] [OrderBot O] (D : O ⥤ ModuleCarrier R)
    (hD : ∀ ⦃a b : O⦄ (f : a ⟶ b), moduleClosedInclusions R (D.map f)) :
    PreservesColimit D (coyoneda.obj (Opposite.op
      ((StructuredSourceSmallness.originalModuleFreeFunctor R.X n).obj
        ((Under.costar CGWH.point).obj A)))) := by
  let ev := StructuredSourceSmallness.originalModuleEvaluation R.X n
  let U := PointedCGWH.pointedToCGWH.{u, v}
  let _ : IsConnected O := IsFiltered.isConnected O
  let _ : PreservesColimitsOfSize.{v, v} ev :=
    StructuredSourceSmallness.originalModuleEvaluationPreservesColimits R.X n
  let _ : PreservesColimit D (ev ⋙ U) := inferInstance
  have hF : ∀ ⦃a b : O⦄ (f : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom ((D ⋙ ev ⋙ U).map f)) := by
    intro a b f
    exact hD f (PointedCGWH.symmetricOperatorObj n)
  let _ : PreservesColimit (D ⋙ ev ⋙ U) (coyoneda.obj (Opposite.op A)) :=
    compactSeparable_preservesClosedLinearColimit A (D ⋙ ev ⋙ U) hF
  exact ((Under.costarAdjForget CGWH.point).comp
    (StructuredSourceSmallness.originalModuleAdjunction R.X n)).preservesColimit_leftAdjointSource A D

/-- Both endpoints of the original free-R image of each realized generator
have their actual Hom-colimit comparisons on the same closed diagram. -/
theorem originalFreeModuleGeneratorEndpoints
    (n : Operad.SmallFinBijGroupoid) {A B : CGWH.{u, v}} (g : A ⟶ B)
    (hg : (CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) g)
    {O : Type v} [LinearOrder O] [OrderBot O] (D : O ⥤ ModuleCarrier R)
    (hD : ∀ ⦃a b : O⦄ (f : a ⟶ b), moduleClosedInclusions R (D.map f)) :
    PreservesColimit D (coyoneda.obj (Opposite.op
      ((StructuredSourceSmallness.originalModuleFreeFunctor R.X n).obj
        ((Under.costar CGWH.point).obj A)))) ∧
      PreservesColimit D (coyoneda.obj (Opposite.op
        ((StructuredSourceSmallness.originalModuleFreeFunctor R.X n).obj
          ((Under.costar CGWH.point).obj B)))) := by
  have h := realizedGeneratorEndpoints_compactSeparable g hg
  let _ : CompactSpace A := h.1.1
  let _ : SeparableSpace A := h.1.2
  let _ : CompactSpace B := h.2.1
  let _ : SeparableSpace B := h.2.2
  exact ⟨originalFreeModule_preservesClosedLinearColimit R n A D hD,
    originalFreeModule_preservesClosedLinearColimit R n B D hD⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every arrow of the actual free-R/free-native generator family retains
both original endpoint Hom-colimit comparisons on the given closed history. -/
theorem originalModuleGeneratorEndpoints_preserve
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {X Y : ModuleCarrier R} (i : X ⟶ Y)
    (hi : StructuredSourceSmallness.moduleGenerators R.X K i)
    {O : Type v} [LinearOrder O] [OrderBot O] (D : O ⥤ ModuleCarrier R)
    (hD : ∀ ⦃a b : O⦄ (f : a ⟶ b), moduleClosedInclusions R (D.map f)) :
    PreservesColimit D (coyoneda.obj (Opposite.op X)) ∧
      PreservesColimit D (coyoneda.obj (Opposite.op Y)) := by
  let H : ModuleCarrier R → Prop := fun A =>
    PreservesColimit D (coyoneda.obj (Opposite.op A))
  let E : MorphismProperty (ModuleCarrier R) := endpointProperty H
  have hFamily : StructuredSourceSmallness.moduleGenerators R.X K ≤ E := by
    rw [StructuredSourceSmallness.moduleGenerators,
      MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap]
    refine iSup_le fun n => ?_
    rw [MorphismProperty.strictMap_le_iff_le_inverseImage]
    rw [MorphismProperty.strictMap_le_iff_le_inverseImage]
    change K ≤ MorphismProperty.inverseImage
      (MorphismProperty.inverseImage (endpointProperty H)
        (StructuredSourceSmallness.originalModuleFreeFunctor R.X n)) (Under.costar CGWH.point)
    rw [inverseImage_endpoints, inverseImage_endpoints]
    intro A B g hg
    have hEndpoints := originalFreeModuleGeneratorEndpoints R n g (hK _ hg) D hD
    dsimp only [endpointProperty, H]
    with_reducible exact hEndpoints
  exact hFamily i hi

/-- The literal native free-R generating arrows supply the ordinal source
data required by the checked generic A6 closure producer. -/
theorem originalModuleSourceHomPreservation
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    CategoryTheory.MorphismProperty.SourceHomPreservation.{_, v, v}
      (StructuredSourceSmallness.moduleGenerators R.X K) (moduleClosedInclusions R) where
  domains i := by
    intro O _ _ _ D hD
    exact (originalModuleGeneratorEndpoints_preserve R K hK i.1.hom i.2 D
      (fun {_ _} f => hD _ _ f)).1
  codomains i := by
    intro O _ _ _ D hD
    exact (originalModuleGeneratorEndpoints_preserve R K hK i.1.hom i.2 D
      (fun {_ _} f => hD _ _ f)).2

/-- An actual chosen subfamily, including a later positive-degree source
family, retains the same original endpoints and ordinal source comparisons. -/
theorem originalModuleSubfamilySourceHomPreservation
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    (I : MorphismProperty (ModuleCarrier R))
    (hI : I ≤ StructuredSourceSmallness.moduleGenerators R.X K) :
    CategoryTheory.MorphismProperty.SourceHomPreservation.{_, v, v}
      I (moduleClosedInclusions R) where
  domains i := (originalModuleSourceHomPreservation R K hK).domains ⟨i.1, hI _ i.2⟩
  codomains i := (originalModuleSourceHomPreservation R K hK).codomains ⟨i.1, hI _ i.2⟩

end LiteralModules


end PointedCGWH.NativeRModuleOrdinalSources
