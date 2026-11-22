/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionBase
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSelectedSource
public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensor
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmashStructure

/-!
# Relative sphere smash on continuous orthogonal spaces

The sphere smash is the actual relative tensor of the stock right modules
over the continuous orthogonal sphere Day monoid. Its projection is a map
of genuine enriched orthogonal spaces. Before taking that sphere quotient,
each level is the full Day coend with continuous isometry coefficients.

This module retains both quotients: the Day relations use the entire
product Hom object, and the relative tensor relations use the entire right
sphere action and the left action induced by the actual Day braiding.
The closedness of the ambient continuous Day category is a prerequisite;
the closed sphere smash and its source mapping end are assembled separately.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open CategoryTheory.CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj

universe uV vV uI vI

namespace PointedCGWH.Spectra.Orthogonal.SphereSmash.SourceReadback
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]

/-- The full original Day and scalar source function type, with every future integrand. -/
def OriginalCoendGeneratorType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L) :=
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    letI := EnrichedDayKernel.LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (EnrichedDayKernel.Closed.smallTensorPreservationFamilies d b).2
    letI : MonoidalCategory (CommutativeModuleConversion.RightModule
      (⟨S⟩ : EnrichedFunctorCat V I)) := RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I)
    ∀ (X Y : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (k : I) (a : I × I),
      EnrichedDayKernel.objects d.tensorEnrichedFunctor
        X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ⟶
          (X ⊗ Y).X.toEnrichedFunctor.obj k

/-- The original entire generator/source HEq, retaining the actual Internal source supplier. -/
def OriginalGeneratorHEqType (d : EnrichedMonoidalCategoryData V I)
    (b : EnrichedBraidedMonoidalCategoryData V I d) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (B : EnrichedFunctor.LaxBraidedData L)
    (g : OriginalCoendGeneratorType d b S L B) : Prop :=
  HEq g (SphereSmashStructure.Internal.coendGenerator d b S L B)

/-- The full original function type independently checks the selected canonical generator. -/
def selectedOriginalGenerator (q : Enriched.ModuleMappingR.SelectedSource V I) :
    OriginalCoendGeneratorType q.monoidalData q.braidedData q.coefficientFunctor
      q.coefficientMonoidal q.coefficientBraided :=
  q.coendGenerator

/-- The original complete source function computes the selected whole generator. -/
theorem selectedOriginalGenerator_heq (q : Enriched.ModuleMappingR.SelectedSource V I) :
    OriginalGeneratorHEqType q.monoidalData q.braidedData q.coefficientFunctor
      q.coefficientMonoidal q.coefficientBraided (selectedOriginalGenerator q) := by
  rfl

end PointedCGWH.Spectra.Orthogonal.SphereSmash.SourceReadback

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

/-- The pointed CGWH coefficient category at the selected universes. -/
abbrev V := PointedCGWH.{u, v}

/-- The original pointed-space category has the small limits used by the source generators. -/
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

/-- The original native enriched Day source, with every named datum selected explicitly. -/
def sourceData : Enriched.ModuleMappingR.SelectedSource PointedCGWH.{u, v} OrthogonalIndex where
  monoidalData := OrthogonalIndex.enrichedMonoidalData.{u, v}
  braidedData := OrthogonalIndex.enrichedSymmetricData.{u, v}
  coefficientFunctor := orthogonalSphereFunctor.{u, v}
  coefficientMonoidal := orthogonalSphereMonoidalData.{u, v}
  coefficientBraided := orthogonalSphereBraidedData.{u, v}

/-- Continuous orthogonal spaces with their full enriched Hom actions. -/
abbrev ISpace := EnrichedFunctorCat V.{u, v} OrthogonalIndex

/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory ISpace.{u, v} := SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance : SymmetricCategory ISpace.{u, v} := SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj (⟨orthogonalSphereFunctor.{u, v}⟩ : ISpace.{u, v}) :=
  SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj (⟨orthogonalSphereFunctor.{u, v}⟩ : ISpace.{u, v}) :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}

local instance : HasCoequalizers ISpace.{u, v} := SphereSmashStructure.hasCoequalizers.{u, v}

/-- The actual relative tensor on the original right sphere modules. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}

/-- The canonical relative sphere tensor on the original source modules. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}

/-- The actual sphere smash symmetry descends the continuous Day braid. -/
@[instance_reducible]
def symmetricCategory : SymmetricCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.symmetricCategory.{u, v}

/-- The canonical relative sphere symmetry on the same source modules. -/
local instance : SymmetricCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.symmetricCategory.{u, v}

/-- The whole right sphere module obtained by smashing the two original modules. -/
abbrev object (X Y : NativeSphereModule.Carrier.{u, v}) :
    NativeSphereModule.Carrier.{u, v} := X ⊗ Y

/-- The quotient map from the complete continuous Day tensor. -/
def projection : (sourceData.{u, v}).ProjectionType := (sourceData.{u, v}).projection

/-- The first relation acts on the original right sphere module. -/
def balanceFirst (X Y : NativeSphereModule.Carrier.{u, v}) :
    (X.X ⊗ sphereISpace.{u, v}) ⊗ Y.X ⟶ X.X ⊗ Y.X := X.action ▷ Y.X

/-- The second relation uses the sphere left action induced by the entire Day braid. -/
def balanceSecond (X Y : NativeSphereModule.Carrier.{u, v}) :
    (X.X ⊗ sphereISpace.{u, v}) ⊗ Y.X ⟶ X.X ⊗ Y.X :=
  (α_ X.X sphereISpace.{u, v} Y.X).hom ≫
    (X.X ◁ CommutativeModuleConversion.leftAction sphereISpace.{u, v} Y)

/-- The full carrier identification with the coequalizer of both original action arrows. -/
abbrev carrierEqCoequalizer :=
  (sourceData.{u, v}).carrierEqCoequalizer

/-- The relative projection balances both whole sphere-action maps. -/
abbrev projectionBalance :=
  (sourceData.{u, v}).projectionBalance

/-- The same complete original sphere-action cofork is colimiting. -/
abbrev quotientIsColimit :=
  (sourceData.{u, v}).quotientIsColimit

/-- The right action on the smash is induced by the original second factor action. -/
abbrev projectionAction :=
  (sourceData.{u, v}).projectionAction

/-- The entire sphere quotient projection is epimorphic. -/
theorem projection_epi : (sourceData.{u, v}).ProjectionEpiType :=
  (sourceData.{u, v}).projectionEpi

/-- Both complete original native source arrows act through the actual quotient tensor. -/
theorem projectionMap : (sourceData.{u, v}).ProjectionMapType :=
  (sourceData.{u, v}).projectionMap

/-- The entire native projection is the same complete selected source quotient function. -/
theorem projection_eq_whole_source :
    projection.{u, v} =
      (sourceData.{u, v}).projection := by
  rfl


/-- The full output-isometry Hom acts naturally on the actual quotient projection. -/
theorem projection_fullHom : (sourceData.{u, v}).ProjectionFullHomType :=
  (sourceData.{u, v}).projection_fullHom

/-- The original integrand has the full continuous isometry coefficient. -/
abbrev integrand (X Y : NativeSphereModule.Carrier.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) : V.{u, v} :=
  EnrichedDayKernel.objects OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a

/-- The isometry coefficient and both complete input values are retained literally. -/
theorem integrand_eq (X Y : NativeSphereModule.Carrier.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    integrand X Y k a =
      OrthogonalIndex.hom.{u, v} (a.1 + a.2) k ⊗
        (X.X.toEnrichedFunctor.obj a.1 ⊗ Y.X.toEnrichedFunctor.obj a.2) := rfl

/-- Each original Day generator is followed by the actual relative sphere projection. -/
def generator :
    SourceReadback.OriginalCoendGeneratorType
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      OrthogonalIndex.enrichedSymmetricData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereMonoidalData.{u, v} orthogonalSphereBraidedData.{u, v} :=
  SourceReadback.selectedOriginalGenerator (sourceData.{u, v})

/-- Generator balancing uses every original product Hom, before taking the sphere quotient. -/
theorem generators_balanced : (sourceData.{u, v}).CoendBalancedType :=
  (sourceData.{u, v}).coendGenerators_balanced

/-- The whole generator function is the original complete Day/scalar source function. -/
theorem generator_heq_source :
    SourceReadback.OriginalGeneratorHEqType
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      OrthogonalIndex.enrichedSymmetricData.{u, v} orthogonalSphereFunctor.{u, v}
      orthogonalSphereMonoidalData.{u, v} orthogonalSphereBraidedData.{u, v} generator.{u, v} :=
  SourceReadback.selectedOriginalGenerator_heq (sourceData.{u, v})

/-- The complete input-map formula, with every actual continuous coefficient retained. -/
abbrev generatorMap : (sourceData.{u, v}).CoendGeneratorMapType :=
  (sourceData.{u, v}).coendGenerator_map

/-- The complete relative tensor universal property on the original stock right modules. -/
def homEquiv : (sourceData.{u, v}).HomEquivType :=
  (sourceData.{u, v}).homEquiv

/-- The forward universal-property map retains the same whole projection. -/
theorem homEquiv_hom : (sourceData.{u, v}).HomEquivHomType :=
  (sourceData.{u, v}).homEquiv_hom

/-- The inverse universal-property map retains the actual relative coequalizer descent. -/
theorem homEquiv_symm : (sourceData.{u, v}).HomEquivSymmType :=
  (sourceData.{u, v}).homEquiv_symm

/-- Projection followed by the entire inverse function recovers the original balanced map. -/
@[reassoc]
theorem projection_homEquiv_symm : (sourceData.{u, v}).ProjectionHomEquivSymmType :=
  (sourceData.{u, v}).projection_homEquiv_symm

/-- Every continuous integrand is conserved by the actual inverse Hom function. -/
@[reassoc]
theorem generator_homEquiv_symm : (sourceData.{u, v}).GeneratorHomEquivSymmType :=
  (sourceData.{u, v}).generator_homEquiv_symm

/-- Actual smash arrows are determined by their values on all original continuous integrands. -/
theorem hom_ext : (sourceData.{u, v}).HomExtType :=
  (sourceData.{u, v}).hom_ext

end PointedCGWH.Spectra.Orthogonal.SphereSmash
