/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceGENSupport.NativeOriginalSourceWord

/-!
# The full original native symmetric source GEN
The checked original source word, action and Omega components identify the
literal native lambda/R map on every original native input and output.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.WholeOriginalGEN


attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

attribute [local irreducible] Mod.internalHom

set_option maxHeartbeats 500000 in
/-- The full native lambda comparison is the original stabilization on every actual native input. -/
theorem original_firstSource_whole_gen :
    originalFirstComparison.{u, v} = originalFirstStructure.{u, v} := by
  exact native_whole_eq_of_action_data
    (r := NativeSymmetricDelooping.firstIndex) (K := PointedCGWH.sphereOne.{u, v})
    (c := originalFirstComparison.{u, v}) (d := originalFirstStructure.{u, v})
    (p := _) (q := _) (hc := original_firstSource_gen.{u, v})
    (hpq := original_module_action_omega.{u, v})
    (hd := fun N n => originalFirstStructure_component
      (originalCarrierEquivalence.{u, v}.functor.obj N) n)


end NativeOmegaRecovery.NativeSymmetricSourceGEN.WholeOriginalGEN
