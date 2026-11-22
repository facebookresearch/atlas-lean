/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.NativeOriginalRankSources
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeSymmetricStableMonoidalModel

/-!
# The original native symmetric stable model acts on its original module homotopy categories

The base model, monoidal model laws, sphere-unit cofibrancy, and base Q factory
are the actual original symmetric constructions. The module model and its Q
factory come from both original free-I/full-K source algorithms at the unchanged
realized-generator cardinal and caller bottom. No scalar cofibrancy or new model,
flatness, replacement-unit, or action-coherence premise is supplied.

This is the ordinary symmetric native application. The independent orthogonal
and positive source producers are not asserted by this construction.
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

namespace HomotopicalAlgebra.ModuleTransfer.NativeDerivedAmbientAction.Symmetric

open CategoryTheory.HomogeneousLocalization

private abbrev C := Actual.SymmetricCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original symmetric stable model for the actual ambient derived action. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.symmetricModelCategory (B := B)

local instance originalMonoidalModel : IsClosedSymmetricMonoidalModelCategory C.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableSmashMonoidalModel (B := B)

local instance originalSphereCofibrant : IsCofibrant (𝟙_ C.{u, v}) :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableTensorUnit_isCofibrant (B := B)

variable (A : C.{u, v}) [MonObj A]

local notation "dC" => StableModelConstruction.symmetricGenerationData (B := B)
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "tA" => NativeOriginalRankSources.Symmetric.originalModuleTransfer (B := B) A
local notation "qA" => RightTransfer.OriginalRankModelTransfer.replacements tA
local notation "H" => DerivedTensorConstructions.MonoidalHo (qC)
local notation "P" => DerivedTensorConstructions.MonoidalHo.projection (qC)
local notation "HA" => MorphismProperty.Localization (DerivedAmbientAction.moduleWeak tA)
local notation "πA" => MorphismProperty.Q (DerivedAmbientAction.moduleWeak tA)

/-- The original symmetric base model and source-produced original module model have the full coherent action. -/
@[instance_reducible]
def originalMonoidalAction : MonoidalLeftAction H HA :=
  DerivedAmbientAction.Coherence.monoidalAction tA dC

/-- Every original source pair retains the exact tensor of the two original generated Q objects. -/
def originalComparison (U : C.{u, v}) (N : Mod C.{u, v} A) :
    letI := originalMonoidalAction A
    letI : ModelCategory (Mod C.{u, v} A) := (tA).model
    (P).obj U ⊙ₗ (πA).obj N ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj U) ((qA).Q.obj N)) :=
  DerivedAmbientAction.comparison tA dC U N

/-- At the actual cofibrant endpoints the original ordinary ambient tensor computes the native derived action. -/
def originalCofibrantComparison (U : C.{u, v}) [IsCofibrant U] (N : Mod C.{u, v} A) :
    letI := originalMonoidalAction A
    letI : ModelCategory (Mod C.{u, v} A) := (tA).model
    ∀ [_hN : IsCofibrant N], (P).obj U ⊙ₗ (πA).obj N ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A U N) := by
  letI : ModelCategory (Mod C.{u, v} A) := (tA).model
  intro hN
  exact DerivedAmbientAction.cofibrantComparison tA dC U N

/-- The actual native unit is the original whole natural sphere-unit comparison. -/
theorem originalUnit (N : HA) :
    letI := originalMonoidalAction A
    λₗ[H] N = (DerivedAmbientAction.unitIso tA dC).app N :=
  DerivedAmbientAction.Coherence.monoidalAction_unit tA dC N

/-- All original coefficient homotopy arrows retain their complete source-derived map function. -/
theorem originalCoefficientMap {X Y : H} (f : X ⟶ Y) (N : HA) :
    letI := originalMonoidalAction A
    f ⊵ₗ N = ((DerivedAmbientAction.action tA dC).map f).app N := rfl

/-- All original module homotopy arrows retain their complete source-derived map function. -/
theorem originalModuleMap (X : H) {N N' : HA} (p : N ⟶ N') :
    letI := originalMonoidalAction A
    X ⊴ₗ p = ((DerivedAmbientAction.action tA dC).obj X).map p := rfl

end HomotopicalAlgebra.ModuleTransfer.NativeDerivedAmbientAction.Symmetric
