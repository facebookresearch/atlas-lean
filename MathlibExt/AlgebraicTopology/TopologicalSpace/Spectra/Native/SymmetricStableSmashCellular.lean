/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricStableSmashPushoutProduct
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Data
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion

/-!
# Closure of original symmetric smash generator products

The actual original native generation data extend the proved boundary
products to all cofibrations. The original horn products extend to the
level trivial branch through the same tensor lifting adjunction and the
same weak factorization systems.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
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

private def originalSmashGeneration :
    CofibrantGenerationData Carrier.{u, v} realizedGeneratorCardinal.{v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.Data.generationData
    (A := Operator.{u, v}) (B := B)

private theorem originalSmashGeneration_I :
    (originalSmashGeneration (B := B)).I = NativeK.levelI (I := Operator.{u, v}) := rfl

private theorem originalSmashGeneration_J :
    (originalSmashGeneration (B := B)).J = NativeK.levelJ (I := Operator.{u, v}) := rfl

/-- All native cofibrations have actual symmetric smash cofibration
products, by closure of the complete original boundary family. -/
theorem cofibrations_pushoutProduct_cofibrations :
    PushoutProductLe (cofibrations Carrier.{u, v}) (cofibrations Carrier.{u, v})
      (cofibrations Carrier.{u, v}) := by
  apply (originalSmashGeneration (B := B)).cofibrationPushoutProduct_of_generatorProducts
  rw [originalSmashGeneration_I]
  exact levelI_pushoutProduct_levelI_cofibrations (B := B)

/-- All original level trivial cofibrations have actual symmetric smash
trivial products against every native cofibration. -/
theorem levelTrivialCofibrations_pushoutProduct_cofibrations :
    PushoutProductLe (trivialCofibrations Carrier.{u, v}) (cofibrations Carrier.{u, v})
      (trivialCofibrations Carrier.{u, v}) := by
  apply (originalSmashGeneration (B := B)).trivialPushoutProductLeft_of_generatorProducts
  rw [originalSmashGeneration_I, originalSmashGeneration_J]
  exact levelJ_pushoutProduct_levelI_trivialCofibrations (B := B)

/-- The original native level model satisfies all three smash pushout
product laws. The other trivial branch uses the actual whole-arrow braid. -/
theorem levelPushoutProductAxiom : MonoidalPushoutProductAxiom Carrier.{u, v} := by
  apply (originalSmashGeneration (B := B)).pushoutProductAxiom_of_generatorProducts
  · rw [originalSmashGeneration_I]
    exact levelI_pushoutProduct_levelI_cofibrations (B := B)
  · rw [originalSmashGeneration_I, originalSmashGeneration_J]
    exact levelJ_pushoutProduct_levelI_trivialCofibrations (B := B)

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
