/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Tactic.Alias
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmash
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceContext

/-!
# Sphere smash on canonical continuous orthogonal spectra

The full source right sphere module equivalence transports the original
relative tensor to the canonical enriched orthogonal spectrum category.
Both original functors, their complete maps, and their unit and counit
are retained in the tensor, tensor maps, associator and unitors.

The source projection includes the original equivalence unit on the
relative tensor. Its continuous coend generators therefore land in the
restriction of the actual canonical smash, with every source transport
map displayed. Closedness uses the source module mapping end separately.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Monoidal.Transport
open CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

open CategoryTheory.Enriched

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash

universe w z

private theorem composeSquare {C : Type w} [Category.{z} C] {A A' B B' Q R : C}
    (p : A ⟶ B) (u : B ⟶ Q) (v : Q ⟶ R) (t : B ⟶ B')
    (s : A ⟶ A') (p' : A' ⟶ B') (u' : B' ⟶ R)
    (hu : t ≫ u' = u ≫ v) (hp : p ≫ t = s ≫ p') :
    (p ≫ u) ≫ v = s ≫ p' ≫ u' :=
  (Category.assoc p u v).trans
    ((congrArg (fun q => p ≫ q) hu.symm).trans
      ((Category.assoc p t u').symm.trans
        ((congrArg (fun q => q ≫ u') hp).trans (Category.assoc s p' u'))))

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

private abbrev V := PointedCGWH.{u, v}

/-- The canonical spectrum carrier, with the actual continuous operator index. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}

private abbrev Modules := NativeSphereModule.Carrier.{u, v}

/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory SphereSmash.ISpace.{u, v} :=
  SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance : SymmetricCategory SphereSmash.ISpace.{u, v} :=
  SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}

local instance : HasCoequalizers SphereSmash.ISpace.{u, v} :=
  SphereSmashStructure.spaceCoequalizers.{u, v}

/-- The actual original pointed-space small limits supply both source product and equalizer data. -/
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- The relative sphere tensor selected by the complete native factory. -/
local instance instMonoidalCategoryModules :
    MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  (SphereSmash.sourceData.{u, v}).moduleMonoidal
/-- The relative sphere symmetry selected by the same complete native factory. -/
local instance instSymmetricCategoryModules :
    SymmetricCategory NativeSphereModule.Carrier.{u, v} :=
  (SphereSmash.sourceData.{u, v}).moduleSymmetric

/-- The complete existing source equivalence, oriented from modules to canonical spectra. -/
abbrev sourceEquivalence : NativeSphereModule.Carrier.{u, v} ≌ Carrier.{u, v} :=
  CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.symm

/-- The actual source sphere module extracted from a canonical spectrum. -/
abbrev source (X : Carrier.{u, v}) : NativeSphereModule.Carrier.{u, v} :=
  sourceEquivalence.{u, v}.inverse.obj X

/-- Its original enriched right-module map on the entire continuous source diagram. -/
abbrev sourceMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) : source X ⟶ source Y :=
  sourceEquivalence.{u, v}.inverse.map f

/-- The full selected source and original equivalence into canonical continuous spectra. -/
def sourceContext : ModuleMappingR.SourceContext (SphereSmash.sourceData.{u, v}) Carrier.{u, v} where
  equivalence := sourceEquivalence.{u, v}

/--
Fix the same three original existence providers before the complete source module and transport
data.
-/
local instance sourceColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  @CategoryTheory.Under.instHasColimitsOfSizeOfHasWidePushouts
    CGWH.{u, v} CGWH.instCategory.{u, v} CGWH.point.{u, v} inferInstance

local instance sourceProducts : HasProducts.{0} PointedCGWH.{u, v} :=
  fun J : Type => @CategoryTheory.Limits.hasProductsOfShape_of_hasProducts
    PointedCGWH.{u, v}
    (@CategoryTheory.instCategoryUnder CGWH.{u, v} CGWH.instCategory.{u, v} CGWH.point.{u, v})
    (fun J' : Type => @CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize
      PointedCGWH.{u, v}
      (@CategoryTheory.instCategoryUnder CGWH.{u, v} CGWH.instCategory.{u, v} CGWH.point.{u, v})
      (Discrete J') (discreteCategory J') SphereSmash.instHasLimitsOfSize.{u, v}) J

local instance sourceEqualizers : HasEqualizers PointedCGWH.{u, v} :=
  @CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits
    PointedCGWH.{u, v}
    (@CategoryTheory.instCategoryUnder CGWH.{u, v} CGWH.instCategory.{u, v} CGWH.point.{u, v})
    (@CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize
      PointedCGWH.{u, v}
      (@CategoryTheory.instCategoryUnder CGWH.{u, v} CGWH.instCategory.{u, v} CGWH.point.{u, v})
      SphereSmash.instHasLimitsOfSize.{u, v})
    WalkingParallelPair inferInstance inferInstance

/-- The actual canonical monoidal structure transported from the relative sphere tensor. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory Carrier.{u, v} :=
  sourceContext.{u, v}.monoidalCategory

attribute [local instance] monoidalCategory

/-- The complete native tensor is its original transported source tensor, without a premise. -/
private theorem originalTransportedMonoidal :
    monoidalCategory.{u, v} = Monoidal.transport sourceEquivalence.{u, v} := rfl

/-- The native smash symmetry transported through the same complete source equivalence. -/
@[instance_reducible]
def symmetricCategory : SymmetricCategory Carrier.{u, v} :=
  sourceContext.{u, v}.symmetricCategory

attribute [local instance] symmetricCategory

/-- Every canonical tensor is the actual source sphere smash,
reconstructed by the source functor. -/
theorem tensorObject_eq_source (X Y : Carrier.{u, v}) :
    letI := monoidalCategory.{u, v}
    X ⊗ Y = sourceEquivalence.{u, v}.functor.obj
      (sourceEquivalence.{u, v}.inverse.obj X ⊗ sourceEquivalence.{u, v}.inverse.obj Y) :=
  TensorLaws.object_of_eq sourceEquivalence.{u, v}
    monoidalCategory.{u, v} originalTransportedMonoidal X Y

/-- The whole tensor-map function keeps both actual source module maps. -/
theorem tensorMap_eq_source {X X' Y Y' : Carrier.{u, v}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI : MonoidalCategory Carrier.{u, v} := Monoidal.transport sourceEquivalence.{u, v}
    f ⊗ₘ g = sourceEquivalence.{u, v}.functor.map
      (sourceEquivalence.{u, v}.inverse.map f ⊗ₘ sourceEquivalence.{u, v}.inverse.map g) :=
  TensorLaws.map_original sourceEquivalence.{u, v} f g

/-- Left tensor retains the complete restriction, source tensor and reconstruction functors. -/
theorem tensorLeft_eq_source (X : Carrier.{u, v}) :
    letI := monoidalCategory.{u, v}
    tensorLeft X = sourceEquivalence.{u, v}.inverse ⋙
      tensorLeft (sourceEquivalence.{u, v}.inverse.obj X) ⋙ sourceEquivalence.{u, v}.functor :=
  TensorLaws.left_of_eq sourceEquivalence.{u, v}
    monoidalCategory.{u, v} originalTransportedMonoidal X

/-- Right tensor retains those same original functors in the other tensor orientation. -/
theorem tensorRight_eq_source (X : Carrier.{u, v}) :
    letI := monoidalCategory.{u, v}
    tensorRight X = sourceEquivalence.{u, v}.inverse ⋙
      tensorRight (sourceEquivalence.{u, v}.inverse.obj X) ⋙ sourceEquivalence.{u, v}.functor :=
  TensorLaws.right_of_eq sourceEquivalence.{u, v}
    monoidalCategory.{u, v} originalTransportedMonoidal X

/-- The actual canonical sphere unit is reconstructed from the source regular sphere module. -/
theorem tensorUnit_eq_source :
    letI := monoidalCategory.{u, v}
    (𝟙_ Carrier.{u, v}) =
      sourceEquivalence.{u, v}.functor.obj (𝟙_ NativeSphereModule.Carrier.{u, v}) :=
  TensorLaws.unit_of_eq sourceEquivalence.{u, v}
    monoidalCategory.{u, v} originalTransportedMonoidal

/-- The original source equivalence unit identifies the source of the native smash. -/
def sourceTensorIso : sourceContext.{u, v}.TensorIsoType :=
  sourceContext.{u, v}.sourceTensorIso

/-- The source projection retains the original relative quotient followed by its original unit. -/
def sourceProjection : sourceContext.{u, v}.ProjectionType :=
  sourceContext.{u, v}.projection

/-- Each native smash generator retains the full source-unit carrier map. -/
def generator : sourceContext.{u, v}.GeneratorType :=
  sourceContext.{u, v}.generator

/-- The native source projection is the original entire projection on every isometry generator. -/
theorem generator_eq_projection (X Y : Carrier.{u, v}) (k : OrthogonalIndex)
    (a : OrthogonalIndex × OrthogonalIndex) :
    sourceContext.{u, v}.GeneratorProjectionFormula X Y k a :=
  sourceContext.{u, v}.generator_eq_projection X Y k a

/-- Both actual source functors and their full original unit remain in the tensorator equation. -/
@[reassoc]
theorem sourceTensorIso_naturality : sourceContext.{u, v}.TensorIsoNaturality :=
  sourceContext.{u, v}.sourceTensorIso_naturality

/-- The native source quotient is natural in both full source module maps. -/
theorem sourceProjectionNaturalityProof : sourceContext.{u, v}.ProjectionNaturality :=
  sourceContext.{u, v}.projection_naturality

/-- The full original two-input source projection property on the actual canonical carrier. -/
def sourceProjectionNaturality : Prop :=
  sourceContext.{u, v}.ProjectionNaturality

/-- The actual canonical source quotient obeys its whole original input-map property. -/
theorem sourceProjectionNaturality_spec : sourceProjectionNaturality.{u, v} :=
  @sourceProjectionNaturalityProof.{u, v}

/-- The complete source projection is the actual canonical quotient and equivalence-unit family. -/
theorem sourceProjection_heq_original : sourceContext.{u, v}.ProjectionHEqFormula :=
  sourceContext.{u, v}.projection_heq

/-- All native tensor generators are natural with both full coefficient input arrows. -/
theorem generator_naturality : sourceContext.{u, v}.GeneratorNaturality :=
  sourceContext.{u, v}.generator_naturality

/-- Every complete postcomposition retains the original generator naturality equation. -/
theorem generator_naturality_assoc : sourceContext.{u, v}.GeneratorNaturalityAssoc :=
  sourceContext.{u, v}.generator_naturality_assoc

/-- Every full continuous Day relation survives the original canonical source-unit transport. -/
theorem generators_balanced (X Y : Carrier.{u, v}) (k : OrthogonalIndex) :
    sourceContext.{u, v}.BalancedFormula X Y k :=
  sourceContext.{u, v}.balanced X Y k

/-- Entire arrows out of the canonical smash are determined by all continuous source integrands. -/
theorem hom_ext : sourceContext.{u, v}.HomExtFamily generator.{u, v} :=
  sourceContext.{u, v}.homExt

/-- Native left whiskering is the original source left whisker
under the same full reconstruction. -/
theorem whiskerLeft_eq_source (X : Carrier.{u, v}) {Y Z : Carrier.{u, v}} (f : Y ⟶ Z) :
    SourceCoherence.WhiskerLeftFormula sourceEquivalence.{u, v} X f :=
  SourceCoherence.whiskerLeft_original sourceEquivalence.{u, v} X f

/-- Native right whiskering retains the original source map and reconstructed target. -/
theorem whiskerRight_eq_source {X Y : Carrier.{u, v}} (f : X ⟶ Y) (Z : Carrier.{u, v}) :
    letI : MonoidalCategory Carrier.{u, v} := Monoidal.transport sourceEquivalence.{u, v}
    f ▷ Z = sourceEquivalence.{u, v}.functor.map
      (sourceEquivalence.{u, v}.inverse.map f ▷ sourceEquivalence.{u, v}.inverse.obj Z) :=
  SourceCoherence.whiskerRight_original sourceEquivalence.{u, v} f Z

/-- The whole native associator retains both original intermediate tensor-unit comparisons. -/
theorem associator_eq_source (X Y Z : Carrier.{u, v}) :
    SourceCoherence.AssociatorFormula sourceEquivalence.{u, v} X Y Z :=
  SourceCoherence.associator_original sourceEquivalence.{u, v} X Y Z

/-- The left unitor retains the original unit comparison and actual source counit. -/
theorem leftUnitor_eq_source (X : Carrier.{u, v}) :
    SourceCoherence.LeftUnitorFormula sourceEquivalence.{u, v} X :=
  SourceCoherence.leftUnitor_original sourceEquivalence.{u, v} X

/-- The right unitor retains the original inverse unit and that same source counit. -/
theorem rightUnitor_eq_source (X : Carrier.{u, v}) :
    SourceCoherence.RightUnitorFormula sourceEquivalence.{u, v} X :=
  SourceCoherence.rightUnitor_original sourceEquivalence.{u, v} X

/-- The whole canonical braiding is the original continuous relative sphere braiding. -/
theorem braiding_eq_source (X Y : Carrier.{u, v}) :
    SourceCoherence.BraidingFormula sourceEquivalence.{u, v} X Y :=
  SourceCoherence.braiding_original sourceEquivalence.{u, v} X Y

/-- The original equivalence unit conserves the complete source braiding map. -/
theorem sourceTensorIso_braiding : sourceContext.{u, v}.TensorIsoBraidingFormula :=
  sourceContext.{u, v}.tensorIso_braiding

/-- The native source projection preserves the whole ambient Day braid. -/
theorem sourceProjection_braiding : sourceContext.{u, v}.ProjectionBraidingFormula :=
  sourceContext.{u, v}.projection_braiding

/-- The original source-unit braiding equation after every complete postcomposition. -/
theorem sourceTensorIso_braiding_assoc : sourceContext.{u, v}.TensorIsoBraidingAssoc :=
  sourceContext.{u, v}.tensorIso_braiding_assoc

/-- The original ambient projection braiding equation after every complete postcomposition. -/
theorem sourceProjection_braiding_assoc : sourceContext.{u, v}.ProjectionBraidingAssoc :=
  sourceContext.{u, v}.projection_braiding_assoc

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash

/-!
Compatibility for the original public orthogonal source APIs.
-/

noncomputable section

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext (since := "2026-11-12")]
abbrev SourceContext := @CategoryTheory.Enriched.ModuleMappingR.SourceContext

section SourceContextMethodCompatibility

universe uV vV uI vI uD vD

open CategoryTheory.EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  {q : ModuleMappingR.SelectedSource V I} {D : Type uD} [Category.{vD} D]

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.monoidalCategory
    (since := "2026-11-12"), instance_reducible]
def SourceContext.monoidalCategory (c : SourceContext q D) : MonoidalCategory D :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.monoidalCategory V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.symmetricCategory
    (since := "2026-11-12"), instance_reducible]
def SourceContext.symmetricCategory (c : SourceContext q D) :
    letI := c.monoidalCategory
    SymmetricCategory D :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.symmetricCategory V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoType
    (since := "2026-11-12")]
def SourceContext.TensorIsoType (c : SourceContext q D) : Type _ :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoType V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso
    (since := "2026-11-12")]
def SourceContext.sourceTensorIso (c : SourceContext q D) : c.TensorIsoType :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionType
    (since := "2026-11-12")]
def SourceContext.ProjectionType (c : SourceContext q D) : Type _ :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionType V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection
    (since := "2026-11-12")]
def SourceContext.projection (c : SourceContext q D) : c.ProjectionType :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorType
    (since := "2026-11-12")]
def SourceContext.GeneratorType (c : SourceContext q D) : Type _ :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorType V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator
    (since := "2026-11-12")]
def SourceContext.generator (c : SourceContext q D) : c.GeneratorType :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorProjectionFormula
    (since := "2026-11-12")]
def SourceContext.GeneratorProjectionFormula (c : SourceContext q D) (X Y : D) (k : I) (a : I × I) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorProjectionFormula
    V _ _ _ _ I _ _ _ _ _ _ _ q D _ c X Y k a

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_eq_projection
    (since := "2026-11-12")]
theorem SourceContext.generator_eq_projection (c : SourceContext q D) (X Y : D) (k : I) (a : I × I) :
    c.GeneratorProjectionFormula X Y k a :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_eq_projection
    V _ _ _ _ I _ _ _ _ _ _ _ q D _ c X Y k a

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoNaturality
    (since := "2026-11-12")]
def SourceContext.TensorIsoNaturality (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoNaturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_naturality
    (since := "2026-11-12")]
theorem SourceContext.sourceTensorIso_naturality (c : SourceContext q D) : c.TensorIsoNaturality :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_naturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoNaturalityAssoc
    (since := "2026-11-12")]
def SourceContext.TensorIsoNaturalityAssoc (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoNaturalityAssoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_naturality_assoc
    (since := "2026-11-12")]
theorem SourceContext.sourceTensorIso_naturality_assoc (c : SourceContext q D) : c.TensorIsoNaturalityAssoc :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_naturality_assoc
    V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionNaturality
    (since := "2026-11-12")]
def SourceContext.ProjectionNaturality (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionNaturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_naturality
    (since := "2026-11-12")]
theorem SourceContext.projection_naturality (c : SourceContext q D) : c.ProjectionNaturality :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_naturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorNaturality
    (since := "2026-11-12")]
def SourceContext.GeneratorNaturality (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorNaturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_naturality
    (since := "2026-11-12")]
theorem SourceContext.generator_naturality (c : SourceContext q D) : c.GeneratorNaturality :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_naturality V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorNaturalityAssoc
    (since := "2026-11-12")]
def SourceContext.GeneratorNaturalityAssoc (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.GeneratorNaturalityAssoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_naturality_assoc
    (since := "2026-11-12")]
theorem SourceContext.generator_naturality_assoc (c : SourceContext q D) : c.GeneratorNaturalityAssoc :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.generator_naturality_assoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionHEqFormula
    (since := "2026-11-12")]
def SourceContext.ProjectionHEqFormula (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionHEqFormula V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_heq
    (since := "2026-11-12")]
theorem SourceContext.projection_heq (c : SourceContext q D) : c.ProjectionHEqFormula :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_heq V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.BalancedFormula
    (since := "2026-11-12")]
def SourceContext.BalancedFormula (c : SourceContext q D) (X Y : D) (k : I) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.BalancedFormula V _ _ _ _ I _ _ _ _ _ _ _ q D _ c X Y k

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.balanced
    (since := "2026-11-12")]
theorem SourceContext.balanced (c : SourceContext q D) (X Y : D) (k : I) : c.BalancedFormula X Y k :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.balanced V _ _ _ _ I _ _ _ _ _ _ _ q D _ c X Y k

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.HomExtFamily
    (since := "2026-11-12")]
def SourceContext.HomExtFamily (c : SourceContext q D) (gamma : c.GeneratorType) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.HomExtFamily V _ _ _ _ I _ _ _ _ _ _ _ q D _ c gamma

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.homExt
    (since := "2026-11-12")]
theorem SourceContext.homExt (c : SourceContext q D) (X Y Z : D)
    (f g : letI := c.monoidalCategory; X ⊗ Y ⟶ Z)
    (h : letI := q.dayMonoidal
      letI := q.coefficientMonObj
      letI := q.moduleMonoidal
      letI := c.monoidalCategory
      ∀ (k : I) (a : I × I),
        c.generator X Y k a ≫ EnrichedFunctorCat.component (c.equivalence.inverse.map f).hom k =
          c.generator X Y k a ≫
            EnrichedFunctorCat.component (c.equivalence.inverse.map g).hom k) : f = g :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.homExt V _ _ _ _ I _ _ _ _ _ _ _ q D _ c X Y Z f g h

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoBraidingFormula
    (since := "2026-11-12")]
def SourceContext.TensorIsoBraidingFormula (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoBraidingFormula V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.tensorIso_braiding
    (since := "2026-11-12")]
theorem SourceContext.tensorIso_braiding (c : SourceContext q D) : c.TensorIsoBraidingFormula :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.tensorIso_braiding V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoBraidingAssoc
    (since := "2026-11-12")]
def SourceContext.TensorIsoBraidingAssoc (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.TensorIsoBraidingAssoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.symmetricCategory_original
    (since := "2026-11-12")]
theorem SourceContext.symmetricCategory_original (c : SourceContext q D) :
    letI := q.moduleMonoidal
    letI := q.moduleSymmetric
    c.symmetricCategory = Monoidal.Transport.moveSymmetric c.monoidalCategory
      (Monoidal.transport c.equivalence) rfl
      (Monoidal.Transport.sourceSymmetric c.equivalence) :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.symmetricCategory_original V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_original
    (since := "2026-11-12")]
theorem SourceContext.sourceTensorIso_original (c : SourceContext q D) :
    letI := q.moduleMonoidal
    c.sourceTensorIso = SourceTensorIso.isoOfEq
      c.equivalence c.monoidalCategory rfl :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.sourceTensorIso_original V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.tensorIso_braiding_assoc
    (since := "2026-11-12")]
theorem SourceContext.tensorIso_braiding_assoc (c : SourceContext q D) : c.TensorIsoBraidingAssoc :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.tensorIso_braiding_assoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionBraidingFormula
    (since := "2026-11-12")]
def SourceContext.ProjectionBraidingFormula (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionBraidingFormula V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_braiding
    (since := "2026-11-12")]
theorem SourceContext.projection_braiding (c : SourceContext q D) : c.ProjectionBraidingFormula :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_braiding V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionBraidingAssoc
    (since := "2026-11-12")]
def SourceContext.ProjectionBraidingAssoc (c : SourceContext q D) : Prop :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.ProjectionBraidingAssoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

set_option linter.deprecated false in
/-- Deprecated forwarding API preserving the original source context member type and notation. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_braiding_assoc
    (since := "2026-11-12")]
theorem SourceContext.projection_braiding_assoc (c : SourceContext q D) : c.ProjectionBraidingAssoc :=
  @CategoryTheory.Enriched.ModuleMappingR.SourceContext.projection_braiding_assoc V _ _ _ _ I _ _ _ _ _ _ _ q D _ c

end SourceContextMethodCompatibility

section SourceContextProjectionCompatibility

universe uV vV uI vI uD vD

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  {q : ModuleMappingR.SelectedSource V I} {D : Type uD} [Category.{vD} D]

set_option linter.deprecated false in
/-- The original projection preserves field notation on the former source context type. -/
@[deprecated CategoryTheory.Enriched.ModuleMappingR.SourceContext.equivalence (since := "2026-11-12")]
abbrev SourceContext.equivalence (self : SourceContext q D) : q.Module ≌ D :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.equivalence self

end SourceContextProjectionCompatibility

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12"), match_pattern]
alias SourceContext.mk :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.mk

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
alias SourceContext.casesOn :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.casesOn

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
alias SourceContext.ctorIdx :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.ctorIdx

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
alias SourceContext.mk.noConfusion :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.mk.noConfusion

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
alias SourceContext.noConfusionType :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.noConfusionType

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
noncomputable alias SourceContext.noConfusion :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.noConfusion

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
noncomputable alias SourceContext.rec :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.rec

/-- Deprecated compatibility for the original source context structure interface. -/
@[deprecated (since := "2026-11-12")]
noncomputable alias SourceContext.recOn :=
  CategoryTheory.Enriched.ModuleMappingR.SourceContext.recOn

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash
