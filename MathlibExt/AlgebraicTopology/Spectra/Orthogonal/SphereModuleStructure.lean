/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereDayMonoid
public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Generators
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ActionReconstruction
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceOperatorReconstruction

/-!
# Original continuous structure maps of stock sphere Day modules

The carrier is the existing stock category of right modules over the original
continuous sphere Day monoid. Its actual action yields a genuine continuous
sphere transformation with all original index Hom maps. The complete coend
generator family reconstructs the original entire action. Module/operator
inverse functors and their source unit and associativity laws are subsequent
constructions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalOpposite CategoryTheory.Spectra
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeSphereModule
open OrthogonalSourceRightModule
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The original Day monoidal structure on the full enriched orthogonal sequence carrier. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original sphere I-space monoid in that same enriched Day category. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}

/-- The actual stock right modules over the original continuous sphere Day monoid. -/
abbrev Carrier := CommutativeModuleConversion.RightModule sphereISpace.{u, v}

/-- Extract the genuine sphere transformation from the entire original stock Day action. -/
def externalSphereTransformation (M : Carrier.{u, v}) :
    GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
      (M.X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
      (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
        PointedCGWH.{u, v} M.X.toEnrichedFunctor) :=
  EnrichedDayKernel.ActionFromTransformation.extract
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} M.X.toEnrichedFunctor
    (CommutativeModuleConversion.RightModule.action M)

/-- The complete original sphere structure map at each pair of genuine index objects. -/
def sphereComponent (M : Carrier.{u, v}) (n a : OrthogonalIndex) :
    M.X.toEnrichedFunctor.obj n ⊗ PointedCGWH.orthogonalSphere.{u, v} a ⟶
      M.X.toEnrichedFunctor.obj (n + a) :=
  Enriched.SphereOperator.Reconstruction.sphereComponent
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    M.X.toEnrichedFunctor (externalSphereTransformation.{u, v} M) n a

/-- Every structure map is the original identity-weight Day generator followed by the stock
action. -/
theorem sphereComponent_day_point (M : Carrier.{u, v}) (n a : OrthogonalIndex) :
    sphereComponent.{u, v} M n a =
      EnrichedDayKernel.Generators.point
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} (n, a) ≫
      EnrichedFunctorCat.component (CommutativeModuleConversion.RightModule.action M) (n + a) := by
  have h₀ := GradedNatTrans.unitComp_component
    (EnrichedDayKernel.Generators.transformation
      OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v})
    (EnrichedFunctorCat.restrictionMap
      OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      (CommutativeModuleConversion.RightModule.action M)) (n, a)
  have h₁ := EnrichedDayKernel.Generators.transformation_component
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} (n, a)
  have h₂ := EnrichedFunctorCat.restrictionMap_component
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    (CommutativeModuleConversion.RightModule.action M) (n, a)
  exact h₀.trans (congrArg₂ (fun f g => f ≫ g) h₁ h₂)

/-- Both original source arrows act naturally on every full sphere structure map. -/
theorem sphereComponent_twoInputs (M : Carrier.{u, v})
    (n m a b : OrthogonalIndex) (f : n ⟶ m) (g : a ⟶ b) :
    (M.X.toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ
      orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map g) ≫
        sphereComponent.{u, v} M m b =
      sphereComponent.{u, v} M n a ≫
        M.X.toEnrichedFunctor.toOrdinaryFunctor.map (f ⊗ₘ g) :=
  Enriched.SphereOperator.Reconstruction.sphereComponent_twoInputs
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    M.X.toEnrichedFunctor (externalSphereTransformation.{u, v} M) n m a b f g


/-- The full continuous product Hom action preserves the complete source structure maps. -/
theorem externalSphereTransformation_fullHom (M : Carrier.{u, v})
    (a b : OrthogonalIndex × OrthogonalIndex) :
    MonoidalClosed.uncurry
      ((M.X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v}).map a b) ≫
        sphereComponent.{u, v} M b.1 b.2 =
      (sphereComponent.{u, v} M a.1 a.2 ⊗ₘ
        𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        MonoidalClosed.uncurry
          ((OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
            PointedCGWH.{u, v} M.X.toEnrichedFunctor).map a b) :=
  (externalSphereTransformation.{u, v} M).uncurriedNaturality a b

/-- Every full original continuous Day generator is conserved by sphere-action extraction. -/
theorem original_action_full_generator (M : Carrier.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    EnrichedDayKernel.gen OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} k a ≫
        EnrichedFunctorCat.component (CommutativeModuleConversion.RightModule.action M) k =
      EnrichedDayKernel.ActionFromTransformation.generator
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} M.X.toEnrichedFunctor
        (externalSphereTransformation.{u, v} M) k a :=
  (EnrichedDayKernel.ActionFromTransformation.gen_extract
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} M.X.toEnrichedFunctor
    (CommutativeModuleConversion.RightModule.action M) k a).symm

/-- Descending the extracted source transformation recovers the entire original module action. -/
theorem reconstruct_original_action (M : Carrier.{u, v}) :
    EnrichedDayKernel.ActionFromTransformation.transformation
      OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} M.X.toEnrichedFunctor
      (externalSphereTransformation.{u, v} M) =
      CommutativeModuleConversion.RightModule.action M :=
  EnrichedDayKernel.ActionFromTransformation.transformation_extract
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    M.X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} M.X.toEnrichedFunctor
    (CommutativeModuleConversion.RightModule.action M)

end PointedCGWH.Spectra.Orthogonal.NativeSphereModule
