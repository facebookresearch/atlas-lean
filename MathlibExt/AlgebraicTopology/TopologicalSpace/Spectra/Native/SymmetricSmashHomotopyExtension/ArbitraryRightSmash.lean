/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.ScalarSmashEndpoints

/-!
# Smash products preserve based homotopy extension

Right smashing with an arbitrary native symmetric spectrum preserves based
homotopy extension of a map. The same statement holds for the chosen realized
interval extension property. Both results transport the time and endpoint
comparisons through the right-smash adjunction.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension

open SymmetricScalarSmash

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

attribute [local irreducible] rightSmashAdjunction

/-- Smashing with any original right spectrum preserves genuine all-target based free-time HEP. -/
theorem rightSmash_preserves_basedHEP {A X : Carrier.{u, v}} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (i ▷ Y) :=
  CategoryTheory.IntervalHomotopyExtension.map_mem_of_adjunction
    (rightSmashAdjunction Y)
    PointedCGWH.EnrichedIntervalContraction.timeFunctor
    (PointedCGWH.EnrichedIntervalContraction.timeInclusionNatTrans 0)
    PointedCGWH.EnrichedIntervalContraction.timeFunctor
    (PointedCGWH.EnrichedIntervalContraction.timeInclusionNatTrans 0)
    (scalarSmashFunctorIso PointedCGWH.RealizedIntervalContraction.time Y).symm
    (timeRightSmash_endpoint Y) i hi

/-- Smashing with any original right spectrum preserves genuine all-target HEP for the original realized interval. -/
theorem rightSmash_preserves_intervalHEP {A X : Carrier.{u, v}} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property i) (Y : Carrier.{u, v}) :
    PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property (i ▷ Y) :=
  CategoryTheory.IntervalHomotopyExtension.map_mem_of_adjunction
    (rightSmashAdjunction Y)
    PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (scalarSmashFunctorIso PointedCGWH.IntervalCoefficient.interval Y).symm
    (intervalRightSmash_endpoint Y) i hi




end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension
