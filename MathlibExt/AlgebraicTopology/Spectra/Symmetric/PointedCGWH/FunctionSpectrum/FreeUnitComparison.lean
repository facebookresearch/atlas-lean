/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeComparison
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensorUnit

/-!
# Free-unit function spectrum comparisons

At the tensor-unit coefficient, the free-source function spectrum is
naturally the symmetric shift by its source index. The module and native
operator comparisons compose the free shift–cotensor isomorphisms with the
selected cotensor-unit comparison and the functor right unitor.
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

attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers

set_option maxHeartbeats 1000000 in
-- The complete free-function Iso is composed with the actual scalar unit comparison.
/-- The full original function spectrum at the native tensor unit uses the
actual chosen cotensor unit and its original enriched evaluation. -/
def unitComparison (r : Operad.SmallFinBijGroupoid) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r (𝟙_ PointedCGWH.{u, v}) ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r :=
  comparison r (𝟙_ PointedCGWH.{u, v}) ≪≫
    Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
      OriginalCotensorUnit.comparison ≪≫
        Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} r)

set_option maxHeartbeats 1000000 in
-- The native free comparison and whole cotensor unit determine this composite Iso.
/-- The actual native free unit source retains the original free comparison
and complete chosen scalar cotensor unit comparison. -/
def nativeFreeUnitComparison (r : Operad.SmallFinBijGroupoid) :
    NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
        (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} r) (𝟙_ PointedCGWH.{u, v})) ≅
      PointedCGWH.SymmetricShift.functor.{u, v} r :=
  nativeFreeComparison r (𝟙_ PointedCGWH.{u, v}) ≪≫
    Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
      OriginalCotensorUnit.comparison ≪≫
        Functor.rightUnitor (PointedCGWH.SymmetricShift.functor.{u, v} r)

end NativeOmegaRecovery.NativeSymmetricFreeFunction
