/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSource
public import MathlibExt.CategoryTheory.Enriched.ModuleFreeStabilizationPoint

/-!
# Free-adjunction formula for symmetric stabilization

The coefficient of a symmetric stabilization map is expressed through the Day
free-evaluation adjunction and the native module-to-operator equivalence. The formula
retains the given sphere coefficient, stabilization generator and both free-source
comparison maps at every pair of finite-bijection indices.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeSource
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

set_option maxHeartbeats 500000 in
-- The complete free-unit adjunct checks the native evaluation and module counit comparisons.
/-- Every all-pair symmetric source has its actual full free-unit adjunct,
retaining the original evaluation comparison and complete carrier counit. -/
theorem stabilization_point (r a : Operad.SmallFinBijGroupoid) :
    ModuleFreeStabilizationPoint.Equation PointedCGWH.sphereSequenceCommMon.{u, v} moduleOperatorEquivalence.{u, v}
      (PointedCGWH.symmetricOperatorObj.{u, v} r)
      (PointedCGWH.symmetricOperatorObj.{u, v} (r ⊗ a))
      (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r) (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} r)
      (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} r)
      (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} r)
      (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} (r ⊗ a))
      (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} (r ⊗ a))
      (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} (r ⊗ a))
      (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} (r ⊗ a))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a)
      (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricNu.{u, v}
        r a) := by
  exact ModuleFreeStabilizationPoint.equation A.{u, v} moduleOperatorEquivalence.{u, v}
      (PointedCGWH.symmetricOperatorObj.{u, v} r)
      (PointedCGWH.symmetricOperatorObj.{u, v} (r ⊗ a))
      (Mod.dayFreeAt S.{u, v} r) (Mod.dayEvaluation S.{u, v} r)
      (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
      (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} r)
      (Mod.dayFreeAt S.{u, v} (r ⊗ a)) (Mod.dayEvaluation S.{u, v} (r ⊗ a))
      (Mod.dayFreeAtEvaluationAdjunction S.{u, v} (r ⊗ a))
      (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} (r ⊗ a))
      (S.{u, v}.functor.obj a)
      (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricNu.{u, v}
        r a)

end NativeOmegaRecovery.NativeSymmetricFreeSource
