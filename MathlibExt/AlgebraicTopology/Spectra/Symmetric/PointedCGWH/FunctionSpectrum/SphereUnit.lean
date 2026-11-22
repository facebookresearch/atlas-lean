/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerCoefficient
public import MathlibExt.CategoryTheory.Enriched.ScalarCorners
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensorUnit

/-!
# Cotensor comparison at the sphere unit

The unit coefficient of the symmetric sphere sequence is identified with the pointed
smash unit by the tensor-power unit map. Cotensoring with that coefficient is naturally
isomorphic to the identity on enriched diagrams, with the component map expressed
through the closed-unit evaluation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uJ
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.OriginalSphereUnit

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

/-- The finite-bijection index category used by the symmetric sequence construction. -/
abbrev I := Operad.SmallFinBijGroupoid
/-- The pointed CGWH coefficient category at the selected universes. -/
abbrev V := PointedCGWH.{u, v}

/-- The original native sphere at the tensor-unit index is identified with
the tensor unit by its unchanged actual sphere coefficient unit map. -/
def iso : (𝟙_ V.{u, v}) ≅ PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ I) :=
  @asIso V.{u, v} _ _ _ PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon
    PointedCGWH.sphereCopowerStrongData.{u, v}.unitIso

/-- The chosen sphere-unit comparison retains the original coefficient unit. -/
theorem iso_hom : iso.{u, v}.hom = PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon := rfl

/-- The actual sphere-unit coefficient comparison and original cotensor unit
give a full comparison at the original sphere of index zero. -/
def cotensorComparison {J : Type uJ} [EnrichedCategory V.{u, v} J] :
    cotensor (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ I)) ≅
      𝟭 (EnrichedFunctorCat V.{u, v} J) :=
  (ScalarLeibniz.cotensorBifunctor (V := V.{u, v}) (A := J)).mapIso iso.{u, v}.op ≪≫
    OriginalCotensorUnit.comparison

/-- Every complete forward component is the actual original coefficient
pre-map followed by the original chosen closed unit evaluation. -/
theorem cotensorComparison_hom_component {J : Type uJ} [EnrichedCategory V.{u, v} J]
    (F : EnrichedFunctorCat V.{u, v} J) (a : J) :
    component (cotensorComparison.{u, v}.hom.app F) a =
      (MonoidalClosed.pre PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon).app
          (F.toEnrichedFunctor.obj a) ≫
        (MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)).hom := by
  change component (cotensorScalarMap PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon F ≫
    OriginalCotensorUnit.counitMap F) a = _
  rw [component_comp, cotensorScalarMap_component, OriginalCotensorUnit.counitMap_component]

end NativeOmegaRecovery.OriginalSphereUnit
