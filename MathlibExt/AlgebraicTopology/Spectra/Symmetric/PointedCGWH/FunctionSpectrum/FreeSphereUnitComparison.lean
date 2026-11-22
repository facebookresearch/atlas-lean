/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeUnitComparison
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SphereUnit

/-!
# Free function spectra and the sphere unit

Composes the free function-spectrum comparison with the sphere coefficient unit to obtain the native right-shift comparison. The module retains the free coefficient map and the contravariant function-spectrum map induced by that unit.
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
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed

/-- The original sphere unit acts on the entire native free coefficient. -/
def sphereUnitSource (r : Operad.SmallFinBijGroupoid) :
    Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) (𝟙_ PointedCGWH.{u, v}) ⟶
      Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
        (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid)) :=
  Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) OriginalSphereUnit.iso.{u, v}.hom

/-- This entire source arrow uses the unchanged original sphere unit map. -/
theorem sphereUnitSource_eq (r : Operad.SmallFinBijGroupoid) :
    sphereUnitSource r = Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r)
      PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon := rfl

set_option maxHeartbeats 1000000 in
-- The whole free-function Iso is composed with the actual sphere coefficient unit.
/-- The original free function at the actual sphere of index zero retains
the original sphere coefficient unit and complete chosen cotensor comparison. -/
def sphereUnitComparison (r : Operad.SmallFinBijGroupoid) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid)) ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r :=
  comparison r
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid)) ≪≫
    Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
      OriginalSphereUnit.cotensorComparison.{u, v} ≪≫
        Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} r)

set_option maxHeartbeats 1000000 in
-- The complete native free comparison retains the sphere unit and scalar cotensor Iso.
/-- The original whole native free sphere source uses that same actual
coefficient unit and its complete original function comparison. -/
def nativeFreeSphereUnitComparison (r : Operad.SmallFinBijGroupoid) :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
          (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid))) ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r :=
  nativeFreeComparison r
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid)) ≪≫
    Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
      OriginalSphereUnit.cotensorComparison.{u, v} ≪≫
        Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} r)

/-- The entire original sphere-unit source pre-map has its actual native
function endpoints, before comparison with the chosen unit maps. -/
def sphereUnitPrecompose (r : Operad.SmallFinBijGroupoid) :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r)
          (PointedCGWH.sphereSequence.{u, v}.functor.obj (𝟙_ Operad.SmallFinBijGroupoid))) ⟶
      NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) (𝟙_ PointedCGWH.{u, v})) :=
  NativeOmegaPreparation.NativeSymmetricFunction.precompose (sphereUnitSource r)

end NativeOmegaRecovery.NativeSymmetricFreeFunction
