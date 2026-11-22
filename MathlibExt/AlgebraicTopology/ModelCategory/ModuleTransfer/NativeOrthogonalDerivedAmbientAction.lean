/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.NativeOrthogonalOriginalRankSources
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalStableMonoidalModel

/-!
# The original orthogonal stable model acts on its original module homotopy categories

Both original free-image source algorithms produce the module model at its
unchanged realized-generator cardinal and caller bottom. The original stable
base model, full generation, closed smash laws and sphere-unit cofibrancy
produce the complete coherent ambient action and its actual Q computations.
The full associator and both unit laws are those of the constructed action;
no scalar cofibrancy, diagonal-bimodule cofibrancy or positive-unit premise enters.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed CategoryTheory.MonObj MonoidalLeftAction

namespace HomotopicalAlgebra.ModuleTransfer.NativeDerivedAmbientAction.Orthogonal

open CategoryTheory.HomogeneousLocalization

private abbrev C := Actual.OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.monoidalCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.symmetricCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.monoidalClosed
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexMonoidalCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexEnrichedOrdinaryCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexSymmetricCategory

/-- The original orthogonal stable model for the actual ambient derived action. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.orthogonalModelCategory (B := B)

local instance originalMonoidalModel : IsClosedSymmetricMonoidalModelCategory C.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableSmashMonoidalModel (B := B)

local instance originalSphereCofibrant : IsCofibrant (𝟙_ C.{u, v}) :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableTensorUnit_isCofibrant (B := B)

variable (A : C.{u, v}) [MonObj A]

local notation "dC" => StableModelConstruction.orthogonalGenerationData (B := B)
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "tA" => NativeOriginalRankSources.Orthogonal.originalModuleTransfer (B := B) A
local notation "qA" => RightTransfer.OriginalRankModelTransfer.replacements tA
local notation "H" => DerivedTensorConstructions.MonoidalHo (qC)
local notation "P" => DerivedTensorConstructions.MonoidalHo.projection (qC)
local notation "HA" => MorphismProperty.Localization (DerivedAmbientAction.moduleWeak tA)
local notation "πA" => MorphismProperty.Q (DerivedAmbientAction.moduleWeak tA)

/-- The two actual original models have the full coherent native orthogonal ambient action. -/
@[instance_reducible]
def originalMonoidalAction : MonoidalLeftAction H HA :=
  DerivedAmbientAction.Coherence.monoidalAction tA dC

/-- Every original pair retains exactly the tensor of its two original generated Q objects. -/
def originalComparison (U : C.{u, v}) (N : Mod C.{u, v} A) :
    letI := originalMonoidalAction A
    letI : ModelCategory (Mod C.{u, v} A) := (tA).model
    (P).obj U ⊙ₗ (πA).obj N ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj U) ((qA).Q.obj N)) :=
  DerivedAmbientAction.comparison tA dC U N

/-- The original ordinary tensor computes the same native derived action at the actual cofibrant endpoints. -/
def originalCofibrantComparison (U : C.{u, v}) [IsCofibrant U] (N : Mod C.{u, v} A) :
    letI := originalMonoidalAction A
    letI : ModelCategory (Mod C.{u, v} A) := (tA).model
    ∀ [_hN : IsCofibrant N], (P).obj U ⊙ₗ (πA).obj N ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A U N) := by
  letI : ModelCategory (Mod C.{u, v} A) := (tA).model
  intro hN
  exact DerivedAmbientAction.cofibrantComparison tA dC U N

/-- The complete native unit remains the original whole natural sphere-unit comparison. -/
theorem originalUnit (N : HA) :
    letI := originalMonoidalAction A
    λₗ[H] N = (DerivedAmbientAction.unitIso tA dC).app N :=
  DerivedAmbientAction.Coherence.monoidalAction_unit tA dC N

/-- The native action retains every original coefficient homotopy map. -/
theorem originalCoefficientMap {X Y : H} (f : X ⟶ Y) (N : HA) :
    letI := originalMonoidalAction A
    f ⊵ₗ N = ((DerivedAmbientAction.action tA dC).map f).app N := rfl

/-- The native action retains every original module homotopy map. -/
theorem originalModuleMap (X : H) {N N' : HA} (p : N ⟶ N') :
    letI := originalMonoidalAction A
    X ⊴ₗ p = ((DerivedAmbientAction.action tA dC).obj X).map p := rfl

end HomotopicalAlgebra.ModuleTransfer.NativeDerivedAmbientAction.Orthogonal
