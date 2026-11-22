/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricStableSmashCellular

/-!
# Original native level smash unit

The proved original generator products and actual sphere-unit cofibrancy
give the level monoidal model laws. The unit witness uses the whole
original native functorial factorization of the initial sphere-unit map,
including its original middle object, both maps and factor equation.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CGWH.limits

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} Operator.{u, v}

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

local instance originalLevelSphereUnitCofibrant : IsCofibrant (𝟙_ Carrier.{u, v}) :=
  tensorUnit_isCofibrant (B := B)

/-- The original native I-factorization evaluated at its initial sphere-unit map. -/
def originalLevelUnitFactor :
    MapFactorizationData (cofibrations Carrier.{u, v}) (trivialFibrations Carrier.{u, v})
      (initial.to (𝟙_ Carrier.{u, v})) :=
  (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
    (A := Operator.{u, v}) (B := B)).factorizationData (initial.to (𝟙_ Carrier.{u, v}))

/-- The native level unit witness contains the actual original factor and map. -/
def levelUnitAxiomWitness : MonoidalUnitAxiomWitness Carrier.{u, v} :=
  (levelPushoutProductAxiom (B := B)).unitAxiomWitnessOfUnitFactor
    (originalLevelUnitFactor (B := B))

/-- Its middle object is the original native factorization's middle functor value. -/
theorem levelUnitAxiomWitness_Q :
    (levelUnitAxiomWitness (B := B)).Q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).Z.obj
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- Its map to the actual sphere unit is the original native right factor. -/
theorem levelUnitAxiomWitness_q :
    (levelUnitAxiomWitness (B := B)).q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).p.app
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- Both original native factors retain the same initial-unit factor equation. -/
theorem levelUnitAxiomWitness_fac :
    (originalLevelUnitFactor (B := B)).i ≫ (levelUnitAxiomWitness (B := B)).q =
      initial.to (𝟙_ Carrier.{u, v}) :=
  (originalLevelUnitFactor (B := B)).fac

/-- The original level replacement has the full actual left unit comparison. -/
theorem levelUnitReplacement_left (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v}
      ((leftUnitReplacementMap (levelUnitAxiomWitness (B := B)).q).app X) := by
  let w : MonoidalUnitAxiomWitness Carrier.{u, v} := levelUnitAxiomWitness (B := B)
  change weakEquivalences Carrier.{u, v} ((leftUnitReplacementMap w.q).app X)
  exact (levelPushoutProductAxiom (B := B)).leftUnitReplacementMap_weak
    w.q w.Q_cofibrant w.q_trivialFibration X

/-- The same replacement has the full actual right unit comparison. -/
theorem levelUnitReplacement_right (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v}
      ((rightUnitReplacementMap (levelUnitAxiomWitness (B := B)).q).app X) := by
  let w : MonoidalUnitAxiomWitness Carrier.{u, v} := levelUnitAxiomWitness (B := B)
  change weakEquivalences Carrier.{u, v} ((rightUnitReplacementMap w.q).app X)
  exact (levelPushoutProductAxiom (B := B)).rightUnitReplacementMap_weak
    w.q w.Q_cofibrant w.q_trivialFibration X

/-- The actual left unit comparison satisfies every original Omega-target test. -/
theorem levelUnitReplacement_left_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((leftUnitReplacementMap (levelUnitAxiomWitness (B := B)).q).app X) :=
  NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (levelUnitReplacement_left X)

/-- The same actual right unit comparison satisfies every original Omega-target test. -/
theorem levelUnitReplacement_right_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((rightUnitReplacementMap (levelUnitAxiomWitness (B := B)).q).app X) :=
  NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (levelUnitReplacement_right X)

/-- The original native level model has its actual closed symmetric smash
model laws, using its original sphere-unit replacement. -/
theorem levelSmashMonoidalModel : IsClosedSymmetricMonoidalModelCategory Carrier.{u, v} :=
  (levelPushoutProductAxiom (B := B)).monoidalModelOfUnitFactor
    (originalLevelUnitFactor (B := B))

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
