/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeModuleNaturality

/-!
# Function spectra of free symmetric modules

For every finite-set index `r` and coefficient `M`, the free-source
function-spectrum functor is naturally isomorphic to the symmetric shift
by `r` followed by scalar cotensoring with `M`. The comparison transports
module internal Hom through the module–operator equivalence and the free
module comparison, retaining the recovery counit. The native operator free
objects receive the corresponding comparison through `originalFreeComparison`.
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



set_option maxHeartbeats 1000000 in
-- The complete native comparison checks the module transport and both original free isomorphisms.
/-- The original full free-source function spectrum is naturally the genuine
native right shift followed by the original scalar cotensor, retaining its counit. -/
def comparison (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r M ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M :=
  eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj
      PointedCGWH.sphereSequenceCommMon.{u, v}
      moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M)) ≪≫
    Functor.isoWhiskerLeft operatorToModule.{u, v} (moduleOperatorComparison r M) ≪≫
      Functor.isoWhiskerRight operatorRecoveryNatIso.{u, v}
        (PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)

set_option maxHeartbeats 1000000 in
-- The complete native comparison checks the module transport and both original free isomorphisms.
/-- The actual whole native free source uses its unchanged original source
comparison and full function-spectrum functor. -/
def nativeFreeComparison (r : Operad.SmallFinBijGroupoid) (M : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) M) ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M :=
  (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r M).symm ≪≫
    comparison r M

end NativeOmegaRecovery.NativeSymmetricFreeFunction
