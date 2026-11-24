/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSelectedSource
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRTransport
public import MathlibExt.CategoryTheory.Monoidal.Transport

/-!
# Complete enriched module source contexts

Selected enriched module equivalences carry the original tensor, symmetry,
balanced quotient, generators and complete naturality families.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Monoidal.Transport
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

universe uV vV uI vI uD vD
open CategoryTheory.Enriched CategoryTheory.EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]

/-- The actual source record and complete equivalence into a typed target category. -/
structure SourceContext (q : ModuleMappingR.SelectedSource V I) (D : Type uD)
    [Category.{vD} D] where
  /-- Both original functors, their complete maps, unit, counit and triangles. -/
  equivalence : q.Module ≌ D

namespace SourceContext
variable {q : ModuleMappingR.SelectedSource V I} {D : Type uD} [Category.{vD} D]

/-- The entire target tensor is transported from the named original module tensor. -/
@[instance_reducible]
def monoidalCategory (c : SourceContext q D) : MonoidalCategory D :=
  letI := q.moduleMonoidal
  Monoidal.transport c.equivalence

/-- The full transported tensor record remains the original selected module tensor. -/
private theorem monoidalCategory_original_record (c : SourceContext q D) :
    c.monoidalCategory =
      (letI := q.moduleMonoidal; Monoidal.transport c.equivalence) := by
  rfl

/-- The full source symmetry is transported through the same original equivalence. -/
@[instance_reducible]
def symmetricCategory (c : SourceContext q D) :
    letI := c.monoidalCategory
    SymmetricCategory D :=
  ModuleMappingRTransport.Braiding.targetSymmetry q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The original source-unit comparison type, with every source and target tensor object. -/
def TensorIsoType (c : SourceContext q D) : Type _ :=
  letI := q.moduleMonoidal
  SourceTensorIso.IsoFamily c.equivalence c.monoidalCategory

/-- The complete comparison is the original equivalence unit on the entire source tensor. -/
def sourceTensorIso (c : SourceContext q D) : c.TensorIsoType := by
  letI := q.moduleMonoidal
  exact SourceTensorIso.isoOfEq c.equivalence c.monoidalCategory rfl

/-- The full original quotient function type for every pair of target objects. -/
def ProjectionType (c : SourceContext q D) : Type _ :=
  ModuleMappingRTransport.Quotient.ProjectionFamily q.monoidalData q.coefficientFunctor
    q.coefficientMonoidal c.equivalence c.monoidalCategory

/-- The actual quotient is followed by the same entire equivalence-unit comparison. -/
def projection (c : SourceContext q D) : c.ProjectionType :=
  ModuleMappingRTransport.Quotient.originalProjection q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso

/-- The full weighted generator type retains every target object and source integrand. -/
def GeneratorType (c : SourceContext q D) : Type _ :=
  ModuleMappingRTransport.Quotient.GeneratorFamily q.monoidalData q.coefficientFunctor
    q.coefficientMonoidal c.equivalence c.monoidalCategory

/-- The original continuous coend generator and complete source comparison are retained. -/
def generator (c : SourceContext q D) : c.GeneratorType :=
  ModuleMappingRTransport.Quotient.originalGenerator q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso

/-- The entire generator-followed-by-quotient equation is written before selecting native data. -/
def GeneratorProjectionFormula (c : SourceContext q D) (X Y : D) (k : I) (a : I × I) : Prop :=
  ModuleMappingRTransport.Quotient.GeneratorProjectionFormula q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso X Y k a

/-- The original complete source supplier proves the whole generator equation. -/
theorem generator_eq_projection (c : SourceContext q D) (X Y : D) (k : I) (a : I × I) :
    c.GeneratorProjectionFormula X Y k a :=
  ModuleMappingRTransport.Quotient.generatorProjection_original q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso X Y k a

/-- The full source tensorator naturality, including every input arrow. -/
def TensorIsoNaturality (c : SourceContext q D) : Prop :=
  letI := q.moduleMonoidal
  SourceTensorIso.Natural c.equivalence c.monoidalCategory c.sourceTensorIso

/-- The entire original tensorator naturality is supplied in the typed source context. -/
theorem sourceTensorIso_naturality (c : SourceContext q D) : c.TensorIsoNaturality := by
  let := q.moduleMonoidal
  intro X X' Y Y' f g
  exact SourceTensorIso.natural_of_eq c.equivalence c.monoidalCategory rfl f g

/-- The entire original tensorator naturality retains every module postcomposition. -/
def TensorIsoNaturalityAssoc (c : SourceContext q D) : Prop :=
  letI := q.moduleMonoidal
  letI := c.monoidalCategory
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') {Z : q.Module}
    (h : c.equivalence.inverse.obj (X' ⊗ Y') ⟶ Z),
    (c.equivalence.inverse.map f ⊗ₘ c.equivalence.inverse.map g) ≫
        (c.sourceTensorIso X' Y').hom ≫ h =
      (c.sourceTensorIso X Y).hom ≫ c.equivalence.inverse.map (f ⊗ₘ g) ≫ h

/-- The same whole source tensorator square is supplied with every original postcomposition. -/
theorem sourceTensorIso_naturality_assoc (c : SourceContext q D) : c.TensorIsoNaturalityAssoc := by
  let := q.moduleMonoidal
  let := c.monoidalCategory
  intro X X' Y Y' f g Z h
  simpa only [Category.assoc] using congrArg (fun t => t ≫ h) (c.sourceTensorIso_naturality f g)

/-- The complete quotient naturality family preserves every original input map. -/
def ProjectionNaturality (c : SourceContext q D) : Prop :=
  ModuleMappingRTransport.Quotient.ClosedProjectionNaturalFamily q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The original full source quotient square is proved before native specialization. -/
theorem projection_naturality (c : SourceContext q D) : c.ProjectionNaturality :=
  ModuleMappingRTransport.Quotient.closedProjectionNatural q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The complete weighted naturality family retains all coefficients and both original maps. -/
def GeneratorNaturality (c : SourceContext q D) : Prop :=
  ModuleMappingRTransport.Quotient.ClosedGeneratorNaturalFamily q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The entire original source generator square is supplied without a new premise. -/
theorem generator_naturality (c : SourceContext q D) : c.GeneratorNaturality :=
  ModuleMappingRTransport.Quotient.closedGeneratorNatural q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- Every full weighted-generator naturality equation survives arbitrary postcomposition. -/
def GeneratorNaturalityAssoc (c : SourceContext q D) : Prop :=
  letI := q.dayMonoidal
  letI := q.coefficientMonObj
  letI := q.moduleMonoidal
  letI := c.monoidalCategory
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') (k : I) (a : I × I)
    {Z : V} (h : (c.equivalence.inverse.obj (X' ⊗ Y')).X.toEnrichedFunctor.obj k ⟶ Z),
    c.generator X Y k a ≫ EnrichedFunctorCat.component
        (c.equivalence.inverse.map (f ⊗ₘ g)).hom k ≫ h =
      (𝟙 (q.monoidalData.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
        (EnrichedFunctorCat.component (c.equivalence.inverse.map f).hom a.1 ⊗ₘ
          EnrichedFunctorCat.component (c.equivalence.inverse.map g).hom a.2)) ≫
        c.generator X' Y' k a ≫ h

/-- The original full source naturality proof retains every complete postcomposition. -/
theorem generator_naturality_assoc (c : SourceContext q D) : c.GeneratorNaturalityAssoc := by
  let := q.dayMonoidal
  let := q.coefficientMonObj
  let := q.moduleMonoidal
  let := c.monoidalCategory
  intro X X' Y Y' f g k a Z h
  simpa only [generator, sourceTensorIso, Category.assoc] using
    congrArg (fun t => t ≫ h) (c.generator_naturality f g k a)

/-- The already-adopted original whole projection comparison is retained in its full type. -/
def ProjectionHEqFormula (c : SourceContext q D) : Prop :=
  ModuleMappingRTransport.Quotient.ProjectionHEqFormula q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso

/-- The existing complete original projection supplier remains unchanged. -/
theorem projection_heq (c : SourceContext q D) : c.ProjectionHEqFormula :=
  ModuleMappingRTransport.Quotient.projectionHEq_original q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso

/-- All original continuous Day balancing relations remain at every source index. -/
def BalancedFormula (c : SourceContext q D) (X Y : D) (k : I) : Prop :=
  ModuleMappingRTransport.Quotient.BalancedFormula q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso X Y k

/-- The same full original source balancing proof supplies the typed family. -/
theorem balanced (c : SourceContext q D) (X Y : D) (k : I) : c.BalancedFormula X Y k :=
  ModuleMappingRTransport.Quotient.balanced_original q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso X Y k

/-- The entire original generator hypothesis determines every full target tensor arrow. -/
def HomExtFamily (c : SourceContext q D) (gamma : c.GeneratorType) : Prop :=
  ModuleMappingRTransport.Quotient.HomExtFamily q.monoidalData q.coefficientFunctor
    q.coefficientMonoidal c.equivalence c.monoidalCategory gamma

/-- The complete source quotient and both original equivalence functors prove injectivity. -/
theorem homExt (c : SourceContext q D) (X Y Z : D)
    (f g : letI := c.monoidalCategory; X ⊗ Y ⟶ Z)
    (h : letI := q.dayMonoidal
      letI := q.coefficientMonObj
      letI := q.moduleMonoidal
      letI := c.monoidalCategory
      ∀ (k : I) (a : I × I),
        c.generator X Y k a ≫ EnrichedFunctorCat.component (c.equivalence.inverse.map f).hom k =
          c.generator X Y k a ≫
            EnrichedFunctorCat.component (c.equivalence.inverse.map g).hom k) : f = g :=
  ModuleMappingRTransport.Quotient.homExtOriginal q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory c.sourceTensorIso X Y Z f g h

/-- The complete source tensorator braid is expressed at the same typed source data. -/
def TensorIsoBraidingFormula (c : SourceContext q D) : Prop :=
  ModuleMappingRTransport.Braiding.TensorIsoFormula q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The original full source-unit braid proves the typed tensorator family. -/
theorem tensorIso_braiding (c : SourceContext q D) : c.TensorIsoBraidingFormula :=
  ModuleMappingRTransport.Braiding.tensorIso_source q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The entire source tensorator braid retains every original module postcomposition. -/
def TensorIsoBraidingAssoc (c : SourceContext q D) : Prop :=
  letI := q.moduleMonoidal
  letI := q.moduleSymmetric
  letI := c.monoidalCategory
  letI := c.symmetricCategory
  ∀ (X Y : D) {Z : q.Module} (h : c.equivalence.inverse.obj (Y ⊗ X) ⟶ Z),
    (c.sourceTensorIso X Y).hom ≫ c.equivalence.inverse.map (β_ X Y).hom ≫ h =
      (β_ (c.equivalence.inverse.obj X) (c.equivalence.inverse.obj Y)).hom ≫
        (c.sourceTensorIso Y X).hom ≫ h

/-- The selected full symmetry is the same original transported source dictionary. -/
theorem symmetricCategory_original (c : SourceContext q D) :
    letI := q.moduleMonoidal
    letI := q.moduleSymmetric
    c.symmetricCategory = Monoidal.Transport.moveSymmetric c.monoidalCategory
      (Monoidal.transport c.equivalence) rfl
      (Monoidal.Transport.sourceSymmetric c.equivalence) := rfl

/-- The selected complete source comparison is the same original whole unit-Iso family. -/
theorem sourceTensorIso_original (c : SourceContext q D) :
    letI := q.moduleMonoidal
    c.sourceTensorIso = SourceTensorIso.isoOfEq
      c.equivalence c.monoidalCategory rfl := rfl

/-- The full original tensorator braid is preserved under every postcomposition. -/
theorem tensorIso_braiding_assoc (c : SourceContext q D) : c.TensorIsoBraidingAssoc := by
  let := q.moduleMonoidal
  let := q.moduleSymmetric
  exact SourceTensorIso.braidingAssocFor_of_eq
    c.equivalence c.monoidalCategory rfl
    c.symmetricCategory c.symmetricCategory_original c.sourceTensorIso c.sourceTensorIso_original

/-- The whole original ambient Day quotient braid is retained at the typed source. -/
def ProjectionBraidingFormula (c : SourceContext q D) : Prop :=
  ModuleMappingRTransport.Braiding.ProjectionFormula q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- The original quotient braid and complete source-unit braid prove the entire ambient family. -/
theorem projection_braiding (c : SourceContext q D) : c.ProjectionBraidingFormula :=
  ModuleMappingRTransport.Braiding.projection_source q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

/-- Every original ambient Day braid equation retains arbitrary complete postcomposition. -/
def ProjectionBraidingAssoc (c : SourceContext q D) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.moduleMonoidal
  letI := c.monoidalCategory
  letI := c.symmetricCategory
  ∀ (X Y : D) {Z : EnrichedFunctorCat V I}
    (h : (c.equivalence.inverse.obj (Y ⊗ X)).X ⟶ Z),
    c.projection X Y ≫ (c.equivalence.inverse.map (β_ X Y).hom).hom ≫ h =
      (β_ (c.equivalence.inverse.obj X).X (c.equivalence.inverse.obj Y).X).hom ≫
        c.projection Y X ≫ h

/-- The same complete ambient quotient braid supplies every original postcomposition. -/
theorem projection_braiding_assoc (c : SourceContext q D) : c.ProjectionBraidingAssoc :=
  ModuleMappingRTransport.Braiding.projectionAssoc_source q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
    c.equivalence c.monoidalCategory rfl

end SourceContext
end CategoryTheory.Enriched.ModuleMappingR
