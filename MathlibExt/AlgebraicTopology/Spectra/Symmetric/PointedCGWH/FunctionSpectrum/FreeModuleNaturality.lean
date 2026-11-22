/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeTargetFunctor
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.TargetNaturality

/-!
# Naturality of the free function-spectrum comparison

The internal Hom from a free sphere module is naturally isomorphic to its
shifted coefficient-cotensor target module. The comparison is natural in target
module maps and respects the module action. Transport through the module-to-operator
functor gives a natural isomorphism with the shifted cotensor of symmetric spectra.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers

open PointedCGWH.SymmetricModulePresentation



private abbrev freeSequence (r : I) (M : V.{u, v}) : Sequence.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} r).obj M)

set_option maxHeartbeats 1000000 in
-- The natural comparison retains the complete free-unit, end and target-module maps.
/-- The actual full module comparison is natural on every original target map,
using the proved native action equation and original target-sequence NatIso. -/
def moduleComparisonNat (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    Mod.internalHom PointedCGWH.sphereSequenceCommMon.{u, v}
      ((Mod.free PointedCGWH.sphereSequence.{u, v}).obj
        (DayFunctor.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj M))) ≅
      targetModuleFunctor r M :=
  FullFreeFunctionTargetNaturality.comparison (I := Operad.SmallFinBijGroupoid)
    (V := PointedCGWH.{u, v}) PointedCGWH.sphereSequenceCommMon.{u, v} r M
    (targetModuleFunctor r M) (targetSequenceNatIso r M) (native_target_pair_square r M)

set_option maxHeartbeats 1000000 in
-- Both whole carrier functors and their original counit enter this natural Iso.
/-- The complete original carrier functor and original operator counit carry
that full module NatIso to the actual native shifted cotensor target functor. -/
def moduleOperatorComparison (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    Mod.internalHom PointedCGWH.sphereSequenceCommMon.{u, v}
      ((Mod.free PointedCGWH.sphereSequence.{u, v}).obj
        (DayFunctor.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj M))) ⋙
        moduleToOperator.{u, v} ≅
      moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M :=
  Functor.isoWhiskerRight (moduleComparisonNat r M) moduleToOperator.{u, v} ≪≫
    Functor.isoWhiskerLeft
      (moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
      operatorRecoveryNatIso.{u, v}

end NativeOmegaRecovery.NativeSymmetricFreeFunction
