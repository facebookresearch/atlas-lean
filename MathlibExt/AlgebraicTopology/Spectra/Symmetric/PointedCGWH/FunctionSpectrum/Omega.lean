/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKIsoTransport
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftOmega
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSphereUnitComparison

/-!
# Free-unit function spectra preserve Omega conditions

If a native symmetric spectrum satisfies `Actual.SymmetricIsOmega`, its
function spectrum from a free tensor-unit object at any index satisfies the
same condition. The analogous statement holds for the sphere-sequence
coefficient at the index tensor unit. Both results transport the full Omega
family through the free-unit comparisons and preservation under symmetric
shifts.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- The function spectrum from the actual free unit preserves every original Omega label. -/
theorem nativeFreeUnit_isOmega (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (hE : Actual.SymmetricIsOmega E) (r : Operad.SmallFinBijGroupoid) :
    Actual.SymmetricIsOmega
      ((NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
          (𝟙_ PointedCGWH.{u, v}))).obj E) := by
  apply NativeOmegaIsoTransport.isOmega_obj_of_natIso Actual.symmetricFamily
    (nativeFreeUnitComparison r) E
  exact NativeSymmetricShiftOmega.shift_isOmega E hE r

/-- The original free zero-sphere source preserves the same whole Omega family. -/
theorem nativeFreeSphereUnit_isOmega (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (hE : Actual.SymmetricIsOmega E) (r : Operad.SmallFinBijGroupoid) :
    Actual.SymmetricIsOmega
      ((NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
          (PointedCGWH.sphereSequence.{u, v}.functor.obj
            (𝟙_ Operad.SmallFinBijGroupoid)))).obj E) := by
  apply NativeOmegaIsoTransport.isOmega_obj_of_natIso Actual.symmetricFamily
    (nativeFreeSphereUnitComparison r) E
  exact NativeSymmetricShiftOmega.shift_isOmega E hE r

end NativeOmegaRecovery.NativeSymmetricFreeFunction
