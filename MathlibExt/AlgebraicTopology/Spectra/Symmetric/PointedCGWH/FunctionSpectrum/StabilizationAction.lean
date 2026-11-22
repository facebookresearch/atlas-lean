/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.StabilizationTarget
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.StabilizationPoint

/-!
# The module action formula for symmetric stabilization

Expresses the stabilization adjoint of a symmetric spectrum presented as a sphere module as the curry of its Day pair action. The formula retains both index objects and the coefficient-first block braiding.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeModuleOmegaFormula
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation


/-- The genuine original all-pair Omega transpose is precisely the original
module pair action at its actual coefficient-first block braid. -/
theorem adjoint (N : Mod PointedCGWH.SymmetricSequence.{u, v} PointedCGWH.sphereSequence.{u, v})
    (x a : Operad.SmallFinBijGroupoid) :
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree.adjoint
      (PointedCGWH.symmetricOperatorObj.{u, v} x)
      (PointedCGWH.symmetricOperatorObj.{u, v} (x ⊗ a))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a)
      (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricNu.{u, v}
        x a) (toOperatorFunctor N) =
      MonoidalClosed.curry ((DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (a, x) ≫
        N.mod.smul.natTrans.app (a ⊗ x) ≫ N.X.functor.map (β_ a x).hom) := by
  open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree in
  have h := action_operatorGenerator_eq_reconstructed
    (toOperatorFunctor N) a x (x ⊗ a) (β_ a x).hom
  have hAction := reconstructedArrowAction_forward N a x (x ⊗ a) (β_ a x).hom
  exact congrArg MonoidalClosed.curry (h.trans hAction)

end NativeOmegaRecovery.NativeModuleOmegaFormula
