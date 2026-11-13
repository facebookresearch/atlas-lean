/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.ComponentThirdSplit
import Code.Exact3D.BoundaryGhostHardField
import Code.Exact3D.ExponentTheorem
import Code.Exact3D.FKReparameterization
import Code.Percolation.SharpnessUnconditional
import Code.Sharpness.BcEqIsing
import Code.Ising.TransitionAssembly












namespace StatMech
namespace Exact3D

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      hcompare)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
        hone hboundary hcmp))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
        hone hboundary hcmp))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
      hfirst)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxGeometry_componentThirdsAbsorption hthirds)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxRatioComponentShare hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxRatioComponentSum hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_capBound_boxRatioComponentShare hcap hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_capBound_boxRatioComponentSum hcap hcapNonneg hsum)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim hfixed
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim hfixed
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
      hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
      hmajor hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hmajor hshare)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hmajor hsum)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      hmajor h)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hmajor hshare)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hmajor hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum
        h))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
        h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleComponents
      hbudget hone hboundary hempty hshell)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrict
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption
      h)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum
      hstrict hshare)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
        h))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleComponentsTailStrictRemainderDenominatorFree
        hremaining htail hsingleton hpayment))
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonTailStrictRemainderDenominatorFree
        hremaining htail hpayment hsingletonResidual))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignTailStrictRemainderDenominatorFree
        hR hstrict hremaining htail hsingletonResidual))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    hlim hfixed hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_denominatorNonnegativePayment
      hsingletonResidual)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
        (schedule := schedule)
        hR hstrict hremaining htail hpayment))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
        (schedule := schedule) (label := label)
        hR hstrict hremaining htail hpayment))
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
        hR hraw))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    hlim hfixed
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hpos)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
        (label := label) hR hraw))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    hlim hfixed
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hpos)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim hfixed
    (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption
        (ι := ι) (label := label) h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum
      h)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum
      h)
    hprojection

section CanonicalRawRowDependentLabelBudget15RemainderFacade

variable {ι :
  (n : ℕ) →
    FK.boxVerts 3 n →
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
variable [∀ n v hasGhost hasOrigin hasEndpoint R,
  Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
variable [∀ n v hasGhost hasOrigin hasEndpoint R,
  DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
variable {label :
  ∀ {n : ℕ},
    Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
    (v : FK.boxVerts 3 n) →
    ∀ hasGhost hasOrigin hasEndpoint R,
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ι n v hasGhost hasOrigin hasEndpoint R}

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive
      (ι := ι) (label := label) hpos hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictSharePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hrawRatio :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSumPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hrawRatio)
    hprojection

end CanonicalRawRowDependentLabelBudget15RemainderFacade

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
        (boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
          hprofile)
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
          hone hboundary hcmp)))
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignRawProfilePayment
      hR hrawStrict hrawPayment)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdom :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaidPlusProfileDominatesSimonPlusActive
      hrawStrict hdom)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeProfileSlack
      hrawStrict hslack)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprofile :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusActiveLeProfile
      hrawStrict hprofile)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcollapsed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedActiveImageLeProfile
      hrawStrict hcollapsed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (htarget :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
      hrawStrict htarget)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsplit :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
      hrawStrict hsplit)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
      hrawStrict hslack)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmain :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityMainAndImageWeightEmpty
      hrawStrict hmain)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hempty :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignBoundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty
      hrawStrict hempty)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixed
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteAtomCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in



theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in



theorem freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdScalar_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hranked :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRankedPrefix_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hranked hone hboundary hcmp)

set_option linter.style.longLine false in



theorem freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsorted :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalSortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hsorted hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hinjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hinjection hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hhall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hhall hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcapacityHall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hcapacityHall hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in



theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdisjoint :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hdisjoint hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in





theorem freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hranked :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hranked hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsorted :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hsorted hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hinjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hinjection hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsubtypeInjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge
      hsubtypeInjection)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hallocation :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
      hallocation)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hgap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGap
      hrawStrict hgap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmass :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
      hrawStrict hmass)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hnonpos :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderNonpositive
      hrawStrict hnonpos)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmainGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainGapSum
      hrawStrict hmainGap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hemptyGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedEmptyGap
      hrawStrict hemptyGap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchCover
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchDisjunction
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchSelector
      (chooseBranch := chooseBranch) hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchCover
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchDisjunction
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchSelector
      (chooseBranch := chooseBranch) hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchFirstTrueSelector
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hhall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hhall hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcapacityHall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hcapacityHall hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdisjoint :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hdisjoint hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




theorem freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in



theorem freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in




structure FiniteCurrentActualScheduleProjectionInputs where
  thermodynamicLimit : FreeIsingThermodynamicLimitPositiveSubcritical
  fixedInner : FreeQ2FixedInnerTwoSidedPositiveSubcritical
  onePointPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical
  boundaryPairPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical
  emptyComparison :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
      boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget
  projection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


theorem boundaryGhostComparison
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    I.onePointPayment I.boundaryPairPayment I.emptyComparison

set_option linter.style.longLine false in


theorem simonFreeSum
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    I.boundaryGhostComparison

set_option linter.style.longLine false in


noncomputable def massBridge
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    I.thermodynamicLimit I.fixedInner I.simonFreeSum I.projection

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

end FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in





structure FiniteCurrentThresholdCandidateEmbeddingProjectionInputs where
  thermodynamicLimit : FreeIsingThermodynamicLimitPositiveSubcritical
  fixedInner : FreeQ2FixedInnerTwoSidedPositiveSubcritical
  rawStrict :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical
  thresholdCandidateEmbedding :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical
  onePointPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical
  boundaryPairPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical
  emptyComparison :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
      boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget
  projection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical

namespace FiniteCurrentThresholdCandidateEmbeddingProjectionInputs

set_option linter.style.longLine false in


theorem boundaryGhostComparison
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
    I.rawStrict I.thresholdCandidateEmbedding I.onePointPayment
    I.boundaryPairPayment I.emptyComparison

set_option linter.style.longLine false in


theorem simonFreeSum
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    I.boundaryGhostComparison

set_option linter.style.longLine false in


noncomputable def massBridge
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection
    I.thermodynamicLimit I.fixedInner I.rawStrict
    I.thresholdCandidateEmbedding I.onePointPayment I.boundaryPairPayment
    I.emptyComparison I.projection

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

end FiniteCurrentThresholdCandidateEmbeddingProjectionInputs

set_option linter.style.longLine false in





structure FiniteCurrentExpandedDemandProjectionInputs where
  thermodynamicLimit : FreeIsingThermodynamicLimitPositiveSubcritical
  fixedInner : FreeQ2FixedInnerTwoSidedPositiveSubcritical
  rawStrict :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical
  expandedDemand :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical
  onePointPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical
  boundaryPairPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical
  emptyComparison :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
      boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget
  projection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical

namespace FiniteCurrentExpandedDemandProjectionInputs

set_option linter.style.longLine false in


theorem profileSlack
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    I.rawStrict I.expandedDemand

set_option linter.style.longLine false in


theorem boundaryGhostComparison
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
    I.rawStrict I.expandedDemand I.onePointPayment I.boundaryPairPayment
    I.emptyComparison

set_option linter.style.longLine false in


theorem simonFreeSum
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison
    I.rawStrict I.expandedDemand I.onePointPayment I.boundaryPairPayment
    I.emptyComparison

set_option linter.style.longLine false in


noncomputable def massBridge
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection
    I.thermodynamicLimit I.fixedInner I.rawStrict I.expandedDemand
    I.onePointPayment I.boundaryPairPayment I.emptyComparison I.projection

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

end FiniteCurrentExpandedDemandProjectionInputs

set_option linter.style.longLine false in



theorem ising3D_positiveMagnetizationSet_nonempty_of_meanfield
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    (Ising.positiveMagnetizationSet 3).Nonempty := by
  refine ⟨Sharpness.tildeBetaCIsing 3 + 1, ?_⟩
  rw [Ising.mem_positiveMagnetizationSet]
  exact
    Sharpness.posMag_of_meanfield_sqrt
      (d := 3) htc_pos hsqrt
      (Sharpness.tildeBetaCIsing 3 + 1) (by linarith)

set_option linter.style.longLine false in



theorem ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    BddBelow (Ising.positiveMagnetizationSet 3) := by
  refine ⟨Sharpness.tildeBetaCIsing 3, ?_⟩
  intro β hβ
  rw [Ising.mem_positiveMagnetizationSet] at hβ
  by_contra hnot
  rw [not_le] at hnot
  have hz := hzero β hnot
  rw [hz] at hβ
  exact lt_irrefl 0 hβ

set_option linter.style.longLine false in



theorem ising3D_tildeBetaCIsing_pos_of_positive_mem
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (hmem : β0 ∈ Sharpness.tildeBetaCIsingSet 3) :
    0 < Sharpness.tildeBetaCIsing 3 := by
  unfold Sharpness.tildeBetaCIsing
  exact lt_of_lt_of_le hβ0 (le_csSup hbdd hmem)

set_option linter.style.longLine false in




theorem ising3D_tildeBetaCIsing_pos_of_positive_phi_witness
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (S : Finset (StatMech.Lattice.Site 3))
    (hS : StatMech.Percolation.origin 3 ∈ S)
    (hphi : Sharpness.phiIsing 3 β0 S < 1) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_positive_mem
    hbdd hβ0 ⟨le_of_lt hβ0, S, hS, hphi⟩

set_option linter.style.longLine false in



theorem corrOriginInner_le_one
    (d : ℕ) (β : ℝ) (S : Finset (StatMech.Lattice.Site d))
    (x : StatMech.Lattice.Site d) :
    Sharpness.corrOriginInner d β S x ≤ 1 := by
  classical
  unfold Sharpness.corrOriginInner
  split
  · split
    · exact le_trans (le_abs_self _) (Sharpness.abs_freeCorr_le_one d β S _ _)
    · norm_num
  · norm_num

set_option linter.style.longLine false in


theorem phiIsing_le_tanh_mul_boundaryEdges_card
    (d : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site d)) :
    Sharpness.phiIsing d β S ≤
      Real.tanh β * (StatMech.Percolation.boundaryEdges d S).card := by
  unfold Sharpness.phiIsing
  have htanh_nonneg : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  apply mul_le_mul_of_nonneg_left _ htanh_nonneg
  calc
    ∑ e ∈ StatMech.Percolation.boundaryEdges d S,
        Sharpness.corrOriginInner d β S e.1
        ≤ ∑ _e ∈ StatMech.Percolation.boundaryEdges d S, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => corrOriginInner_le_one d β S e.1)
    _ = (StatMech.Percolation.boundaryEdges d S).card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]

set_option linter.style.longLine false in


theorem phiIsing_le_tanh_mul_card_mul_two_d
    (d : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site d)) :
    Sharpness.phiIsing d β S ≤ Real.tanh β * (S.card * (2 * d)) := by
  have hboundary :=
    phiIsing_le_tanh_mul_boundaryEdges_card d hβ S
  have htanh_nonneg : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  have hcard :
      ((StatMech.Percolation.boundaryEdges d S).card : ℝ) ≤
        S.card * (2 * d) := by
    exact_mod_cast StatMech.Percolation.card_boundaryEdges_le_su
      (d := d) S
  exact le_trans hboundary (mul_le_mul_of_nonneg_left hcard htanh_nonneg)

set_option linter.style.longLine false in



theorem tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one
    {β : ℝ}
    (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site 3))
    (hS : StatMech.Percolation.origin 3 ∈ S)
    (hsmall : Real.tanh β * (S.card * (2 * 3)) < 1) :
    β ∈ Sharpness.tildeBetaCIsingSet 3 := by
  rw [Sharpness.mem_tildeBetaCIsingSet]
  refine ⟨hβ, S, hS, ?_⟩
  exact lt_of_le_of_lt
    (phiIsing_le_tanh_mul_card_mul_two_d 3 hβ S) hsmall

noncomputable def ising3DPositiveWitnessBeta : ℝ :=
  Real.artanh (1 / 7)

noncomputable def ising3DOriginSingleton :
    Finset (StatMech.Lattice.Site 3) :=
  {StatMech.Percolation.origin 3}

set_option linter.style.longLine false in




theorem ising3D_tildeBetaCIsingSet_positive_singleton_mem :
    ising3DPositiveWitnessBeta ∈ Sharpness.tildeBetaCIsingSet 3 := by
  classical
  have hβ_pos : 0 < ising3DPositiveWitnessBeta := by
    rw [ising3DPositiveWitnessBeta]
    exact Real.artanh_pos (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo 0 1)
  refine
    tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one
      (le_of_lt hβ_pos) ising3DOriginSingleton ?_ ?_
  · rw [ising3DOriginSingleton]
    exact Finset.mem_singleton_self _
  · have htanh :
        Real.tanh ising3DPositiveWitnessBeta = (1 / 7 : ℝ) := by
      rw [ising3DPositiveWitnessBeta]
      exact Real.tanh_artanh
        (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo (-1) 1)
    rw [htanh, ising3DOriginSingleton, Finset.card_singleton]
    norm_num

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_bddAbove
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3)) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_positive_mem
    hbdd
    (by
      rw [ising3DPositiveWitnessBeta]
      exact Real.artanh_pos (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo 0 1))
    ising3D_tildeBetaCIsingSet_positive_singleton_mem

set_option linter.style.longLine false in



theorem tildeBetaCIsingSet_bddAbove_of_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
  refine ⟨B, ?_⟩
  intro β hβ
  rw [Sharpness.mem_tildeBetaCIsingSet] at hβ
  obtain ⟨_, S, hS, hphi⟩ := hβ
  by_contra hnot
  rw [not_le] at hnot
  have hge := hbarrier β hnot S hS
  linarith

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_bddAbove
    (tildeBetaCIsingSet_bddAbove_of_phi_barrier hbarrier)

set_option linter.style.longLine false in




theorem tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
  obtain ⟨B, hpos⟩ := heventual
  refine ⟨B, ?_⟩
  intro β hβ
  by_contra hnot
  rw [not_le] at hnot
  have hz := hzeroSet β hβ
  have hp := hpos β hnot
  rw [hz] at hp
  exact lt_irrefl 0 hp

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_bddAbove
    (tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)

set_option linter.style.longLine false in




abbrev Ising3DTransitionRegime : Prop :=
  ∃ βc : ℝ, 0 < βc ∧
    (∀ β, 0 < β → β < βc → Ising.magnetization 3 β = 0) ∧
    (∀ β, βc < β → 0 < Ising.magnetization 3 β)

set_option linter.style.longLine false in




structure Ising3DTransitionAssemblyInputs where
  isingBox :
    ∀ β, 0 < β → ∀ n, 1 ≤ n →
      IsingFK.fvMagnetization 3 β n =
        IsingFK.esWiredOnePoint
          (FK.boxGraph 3 (n + 1))
          (FK.boxBoundary 3 (n + 1))
          (0 : Fin 2) (IsingFK.pOfBeta β)
          (IsingFK.boxOrigin 3 (n + 1))
  thetaPc :
    ∀ (hp : 0 < FK.fkPc 3 2) (hp1 : FK.fkPc 3 2 < 1),
      FK.fkTheta 3 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0
  pc_lt_one : FK.fkPc 3 2 < 1

namespace Ising3DTransitionAssemblyInputs

set_option linter.style.longLine false in



theorem transitionRegime
    (I : Ising3DTransitionAssemblyInputs) :
    Ising3DTransitionRegime :=
  Ising.ita_ising_transition 3 (by norm_num)
    I.isingBox I.thetaPc I.pc_lt_one

end Ising3DTransitionAssemblyInputs

set_option linter.style.longLine false in


theorem ising3D_transitionRegime_of_transitionAssemblyInputs
    (I : Ising3DTransitionAssemblyInputs) :
    Ising3DTransitionRegime :=
  I.transitionRegime

set_option linter.style.longLine false in





abbrev Ising3DNoPositiveMagnetizationAtNonpositiveBeta : Prop :=
  ∀ β, β ≤ 0 → ¬ 0 < Ising.magnetization 3 β

set_option linter.style.longLine false in


theorem ising3D_eventual_positiveMagnetization_of_transition_regime
    (hregime : Ising3DTransitionRegime) :
    ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β := by
  obtain ⟨βc, _hβc, _hsub, hsuper⟩ := hregime
  exact ⟨βc, hsuper⟩

set_option linter.style.longLine false in

theorem tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_transition_regime
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) :=
  tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_transition_regime
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)

set_option linter.style.longLine false in


theorem exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC
    {β : ℝ}
    (hβ : β < Sharpness.tildeBetaCIsing 3) :
    ∃ γ ∈ Sharpness.tildeBetaCIsingSet 3, β < γ := by
  unfold Sharpness.tildeBetaCIsing at hβ
  exact
    exists_lt_of_lt_csSup
      ⟨ising3DPositiveWitnessBeta,
        ising3D_tildeBetaCIsingSet_positive_singleton_mem⟩
      hβ

set_option linter.style.longLine false in





theorem ising3D_magnetization_monotone_of_volume_tendsto
    {volumeMag : ℕ → ℝ → ℝ}
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β))) :
    Monotone (Ising.magnetization 3) := by
  intro β₁ β₂ hβ
  exact le_of_tendsto_of_tendsto (hfullLimit β₁) (hfullLimit β₂)
    (Filter.Eventually.of_forall fun N => hfiniteMono N hβ)

set_option linter.style.longLine false in



theorem ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0 := by
  intro β hβ
  obtain ⟨γ, hγ, hβγ⟩ :=
    exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC hβ
  have hle : Ising.magnetization 3 β ≤ 0 := by
    have hmono_le := hmono hβγ.le
    rw [hzeroSet γ hγ] at hmono_le
    exact hmono_le
  exact le_antisymm hle (hnonneg β)

set_option linter.style.longLine false in


theorem ising3D_vanish_below_tildeBetaC_of_zero_on_set_volumeMonotone_nonneg
    {volumeMag : ℕ → ℝ → ℝ}
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β)))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0 :=
  ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
    hzeroSet
    (ising3D_magnetization_monotone_of_volume_tendsto
      hfiniteMono hfullLimit)
    hnonneg

set_option linter.style.longLine false in



theorem ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hmono : Monotone (Ising.magnetization 3)) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β := by
  intro β hβ hpos
  obtain ⟨γ, hγ, hβγ⟩ :=
    exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC hβ
  have hle : Ising.magnetization 3 β ≤ 0 := by
    have hmono_le := hmono hβγ.le
    rw [hzeroSet γ hγ] at hmono_le
    exact hmono_le
  linarith

set_option linter.style.longLine false in


theorem ising3D_not_positive_below_tildeBetaC_of_zero_on_set_volumeMonotone
    {volumeMag : ℕ → ℝ → ℝ}
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β))) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β :=
  ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
    hzeroSet
    (ising3D_magnetization_monotone_of_volume_tendsto
      hfiniteMono hfullLimit)

set_option linter.style.longLine false in






theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hne : (Ising.positiveMagnetizationSet 3).Nonempty)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 := by
  have heq :
      Ising.betaC 3 = Sharpness.tildeBetaCIsing 3 :=
    Sharpness.bc_eq_ising_of_meanfield
      (d := 3) htc_pos hbdd hne hsqrt hzero
  rwa [heq]

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs
    htc_pos hbdd
    (ising3D_positiveMagnetizationSet_nonempty_of_meanfield htc_pos hsqrt)
    hsqrt hzero

set_option linter.style.longLine false in




theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
    htc_pos
    (ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC
      hzero)
    hsqrt hzero

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_bddAbove hbddTilde)
    hsqrt hzero

set_option linter.style.longLine false in




theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_phi_barrier hbarrier)
    hsqrt hzero

set_option linter.style.longLine false in




theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt hzero

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt
    (ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
      hzeroSet hmono hnonneg)

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hnotpos : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β) :
    0 < Ising.betaC 3 := by
  have hne :
      (Ising.positiveMagnetizationSet 3).Nonempty :=
    ising3D_positiveMagnetizationSet_nonempty_of_meanfield htc_pos hsqrt
  have htilde_le : Sharpness.tildeBetaCIsing 3 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf hne ?_
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    exact hnotpos β hnotle hβ
  exact lt_of_lt_of_le htc_pos htilde_le

set_option linter.style.longLine false in




theorem ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt
    (ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
      hzeroSet hmono)

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)
    hmono hsqrt

set_option linter.style.longLine false in



theorem ising3D_betaC_pos_of_sharpness_zeroSet_transitionAssembly_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone
    hzeroSet htransition.transitionRegime hmono hsqrt

set_option linter.style.longLine false in





theorem ising3D_betaC_pos_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    0 < Ising.betaC 3 := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hne : (Ising.positiveMagnetizationSet 3).Nonempty := by
    refine ⟨β0 + 1, ?_⟩
    rw [Ising.mem_positiveMagnetizationSet]
    exact hsuper (β0 + 1) (by linarith)
  have hβ0_le : β0 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf hne ?_
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    by_cases hβpos : 0 < β
    · have hz := hsub β hβpos hnotle
      rw [hz] at hβ
      exact lt_irrefl 0 hβ
    · exact hnonpos β (not_lt.mp hβpos) hβ
  exact lt_of_lt_of_le hβ0 hβ0_le

set_option linter.style.longLine false in





theorem ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hβ0_lower : ∀ β, β ∈ Ising.positiveMagnetizationSet 3 → β0 ≤ β := by
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    by_cases hβpos : 0 < β
    · have hz := hsub β hβpos hnotle
      rw [hz] at hβ
      exact lt_irrefl 0 hβ
    · exact hnonpos β (not_lt.mp hβpos) hβ
  have hbdd : BddBelow (Ising.positiveMagnetizationSet 3) :=
    ⟨β0, hβ0_lower⟩
  have hle : β0 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf ?_ ?_
    · exact ⟨β0 + 1, by
        rw [Ising.mem_positiveMagnetizationSet]
        exact hsuper (β0 + 1) (by linarith)⟩
    · intro β hβ
      exact hβ0_lower β hβ
  have hge : Ising.betaC 3 ≤ β0 := by
    unfold Ising.betaC
    refine le_of_forall_gt_imp_ge_of_dense ?_
    intro β hβ
    exact csInf_le hbdd (by
      rw [Ising.mem_positiveMagnetizationSet]
      exact hsuper β hβ)
  exact ⟨β0, hβ0, le_antisymm hge hle, hsub, hsuper⟩

set_option linter.style.longLine false in





theorem ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
    (hregime : Ising3DTransitionRegime) :
    ∃ β0 : ℝ, 0 < β0 ∧
      IsingFK.betaC (Ising.magnetization 3) = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  let S : Set ℝ := {β : ℝ | 0 < β ∧ Ising.magnetization 3 β = 0}
  have hupper : ∀ β, β ∈ S → β ≤ β0 := by
    intro β hβ
    by_contra hnotle
    rw [not_le] at hnotle
    have hpos := hsuper β hnotle
    rw [hβ.2] at hpos
    exact lt_irrefl 0 hpos
  have hbdd : BddAbove S := ⟨β0, hupper⟩
  have hne : S.Nonempty := by
    refine ⟨β0 / 2, ?_⟩
    exact ⟨by linarith, hsub (β0 / 2) (by linarith) (by linarith)⟩
  have hle : IsingFK.betaC (Ising.magnetization 3) ≤ β0 := by
    unfold IsingFK.betaC
    exact csSup_le hne hupper
  have hge : β0 ≤ IsingFK.betaC (Ising.magnetization 3) := by
    unfold IsingFK.betaC
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · have hmem : β0 / 2 ∈ S :=
        ⟨by linarith, hsub (β0 / 2) (by linarith) (by linarith)⟩
      exact le_trans (by linarith) (le_csSup hbdd hmem)
    · have hapos : 0 < a := lt_of_not_ge ha0
      let c : ℝ := (a + β0) / 2
      have hcpos : 0 < c := by
        dsimp [c]
        linarith
      have hcβ0 : c < β0 := by
        dsimp [c]
        linarith
      have hac : a ≤ c := by
        dsimp [c]
        linarith
      have hmem : c ∈ S := ⟨hcpos, hsub c hcpos hcβ0⟩
      exact le_trans hac (le_csSup hbdd hmem)
  exact ⟨β0, hβ0, le_antisymm hle hge, hsub, hsuper⟩

set_option linter.style.longLine false in




theorem ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hfull :
      ∃ γ : ℝ, 0 < γ ∧ Ising.betaC 3 = γ ∧
        (∀ β, 0 < β → β < γ → Ising.magnetization 3 β = 0) ∧
        (∀ β, γ < β → 0 < Ising.magnetization 3 β) :=
    ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
      ⟨β0, hβ0, hsub, hsuper⟩ hnonpos
  have hpositive :
      ∃ γ : ℝ, 0 < γ ∧ IsingFK.betaC (Ising.magnetization 3) = γ ∧
        (∀ β, 0 < β → β < γ → Ising.magnetization 3 β = 0) ∧
        (∀ β, γ < β → 0 < Ising.magnetization 3 β) :=
    ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
      ⟨β0, hβ0, hsub, hsuper⟩
  obtain ⟨βfull, _hβfull, hfull_eq, hfull_sub, hfull_super⟩ := hfull
  obtain ⟨βpos, _hβpos, hpos_eq, hpos_sub, hpos_super⟩ := hpositive
  have hfull_le_pos : βfull ≤ βpos := by
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact le_trans ha0 (le_of_lt _hβpos)
    · have hapos : 0 < a := lt_of_not_ge ha0
      by_contra hnotle
      rw [not_le] at hnotle
      have hz := hfull_sub a hapos ha
      have hp := hpos_super a hnotle
      rw [hz] at hp
      exact lt_irrefl 0 hp
  have hpos_le_full : βpos ≤ βfull := by
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact le_trans ha0 (le_of_lt _hβfull)
    · have hapos : 0 < a := lt_of_not_ge ha0
      by_contra hnotle
      rw [not_le] at hnotle
      have hz := hpos_sub a hapos ha
      have hp := hfull_super a hnotle
      rw [hz] at hp
      exact lt_irrefl 0 hp
  rw [hfull_eq, hpos_eq, le_antisymm hfull_le_pos hpos_le_full]

set_option linter.style.longLine false in


theorem ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transitionAssembly
    (htransition : Ising3DTransitionAssemblyInputs) :
    ∃ β0 : ℝ, 0 < β0 ∧
      IsingFK.betaC (Ising.magnetization 3) = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) :=
  ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
    htransition.transitionRegime

set_option linter.style.longLine false in


theorem ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) :=
  ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

set_option linter.style.longLine false in


theorem ising3D_exists_betaC_eq_transition_threshold_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) :=
  ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassExactPowerLawNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  massPrefactor : ℝ → ℝ
  massPrefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (massPrefactor β) /
        Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      freeSelectedPositiveSubcriticalMass hmass β =
        massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  amplitude : ℝ
  amplitude_pos : 0 < amplitude
  relativePrefactor : ℝ → ℝ
  relativePrefactor_tendsto_one :
    Filter.Tendsto relativePrefactor
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 1)
  mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      freeSelectedPositiveSubcriticalMass hmass β =
        amplitude * relativePrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical D hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  amplitude := h.amplitude
  amplitude_pos := h.amplitude_pos
  relativePrefactor := h.relativePrefactor
  relativePrefactor_tendsto_one := h.relativePrefactor_tendsto_one
  mass_scaling := by
    intro β hβ
    simpa [hpred] using h.mass_scaling β hβ

end FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass := by
  classical
  let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
  have hrelpos :
      ∀ᶠ β in L, 0 < hasymp.relativePrefactor β := by
    have hdist :=
      (Metric.tendsto_nhds.mp hasymp.relativePrefactor_tendsto_one)
        ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hdist] with β hβ
    rw [Real.dist_eq] at hβ
    have hbounds := abs_sub_lt_iff.mp hβ
    linarith
  let posWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hposWindow_spec :
      0 < posWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - posWindow) (Ising.betaC 3) →
          0 < hasymp.relativePrefactor β := by
    simpa [posWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hprefLog :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (hasymp.amplitude * hasymp.relativePrefactor β) /
            Real.log (Ising.betaC 3 - β))
        L (nhds 0) := by
    have hpref :
        Filter.Tendsto
          (fun β : ℝ => hasymp.amplitude * hasymp.relativePrefactor β)
          L (nhds hasymp.amplitude) := by
      simpa using
        (tendsto_const_nhds.mul hasymp.relativePrefactor_tendsto_one)
    have hlogpref :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hasymp.amplitude * hasymp.relativePrefactor β))
          L (nhds (Real.log hasymp.amplitude)) :=
      (Real.continuousAt_log hasymp.amplitude_pos.ne').tendsto.comp hpref
    have hlogd :
        Filter.Tendsto (fun β : ℝ => Real.log (Ising.betaC 3 - β))
          L Filter.atBot := by
      simpa [L, Ising3DModel] using tendsto_log_betaC_sub_atBot Ising3DModel
    exact hlogpref.div_atBot hlogd
  exact
    { δ := min hasymp.δ posWindow
      δ_pos := lt_min hasymp.δ_pos hposWindow_spec.1
      δ_le_betaC := by
        exact le_trans (min_le_left hasymp.δ posWindow) hasymp.δ_le_betaC
      massPrefactor := fun β =>
        hasymp.amplitude * hasymp.relativePrefactor β
      massPrefactor_pos := by
        intro β hβ
        have hβPos :
            β ∈ Set.Ioo (Ising.betaC 3 - posWindow) (Ising.betaC 3) := by
          constructor
          · linarith [hβ.1, min_le_right hasymp.δ posWindow]
          · exact hβ.2
        exact mul_pos hasymp.amplitude_pos (hposWindow_spec.2 β hβPos)
      massPrefactor_log_negligible := by
        simpa [L] using hprefLog
      mass_scaling := by
        intro β hβ
        have hβAsymp :
            β ∈ Set.Ioo (Ising.betaC 3 - hasymp.δ) (Ising.betaC 3) := by
          constructor
          · linarith [hβ.1, min_le_left hasymp.δ posWindow]
          · exact hβ.2
        simpa [mul_assoc] using hasymp.mass_scaling β hβAsymp }

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  logRemainder : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  logRemainder_negligible :
    Filter.Tendsto
      (fun β : ℝ => logRemainder β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        C.predictedExponent * Real.log (Ising.betaC 3 - β) +
          logRemainder β

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassLogRatioLimitNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_ratio_tendsto :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds C.predictedExponent)

set_option linter.style.longLine false in





structure FreePositiveSubcriticalMassLogRatioSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_ratio_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        C.predictedExponent - ε <
            Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) ∧
          Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) <
            C.predictedExponent + ε

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hexact :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass where
  δ := hexact.δ
  δ_pos := hexact.δ_pos
  δ_le_betaC := hexact.δ_le_betaC
  logRemainder := fun β => Real.log (hexact.massPrefactor β)
  mass_pos := by
    intro β hβ
    rw [hexact.mass_scaling β hβ]
    exact mul_pos (hexact.massPrefactor_pos β hβ) (Real.exp_pos _)
  logRemainder_negligible := hexact.massPrefactor_log_negligible
  log_mass_scaling := by
    intro β hβ
    have hpref_pos : 0 < hexact.massPrefactor β :=
      hexact.massPrefactor_pos β hβ
    have hpref_ne : hexact.massPrefactor β ≠ 0 := hpref_pos.ne'
    have hexp_ne :
        Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [hexact.mass_scaling β hβ, Real.log_mul hpref_ne hexp_ne,
      Real.log_exp]
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
    C hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hlog.δ
  δ_pos := hlog.δ_pos
  δ_le_betaC := hlog.δ_le_betaC
  mass_pos := hlog.mass_pos
  log_mass_ratio_tendsto := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hlimit :
        Filter.Tendsto
          (fun β : ℝ =>
            C.predictedExponent +
              hlog.logRemainder β / Real.log (Ising.betaC 3 - β))
          L (nhds C.predictedExponent) := by
      simpa [L] using tendsto_const_nhds.add hlog.logRemainder_negligible
    refine Filter.Tendsto.congr' ?_ hlimit
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising.betaC 3 - hlog.δ < Ising.betaC 3 by
          linarith [hlog.δ_pos]),
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - (1 : ℝ) < Ising.betaC 3 by norm_num)]
      with β hβδ hβone
    have hdiff : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβone.1, hβone.2]
    have hden : Real.log (Ising.betaC 3 - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      C.predictedExponent +
          hlog.logRemainder β / Real.log (Ising.betaC 3 - β) =
        Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β)
    rw [hlog.log_mass_scaling β hβδ]
    field_simp [hden]

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hexact :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_logAffineNearCritical
    C hmass
    (freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
      C hmass hexact)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_exactPowerLaw
    C hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassPowerSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  mass_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        Real.exp
            ((C.predictedExponent + ε) *
              Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            Real.exp
              ((C.predictedExponent - ε) *
                Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in





structure FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ → ℝ
  upperPrefactor : ℝ → ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        0 < lowerPrefactor ε β
  upperPrefactor_pos :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        0 < upperPrefactor ε β
  lowerPrefactor_log_negligible :
    ∀ ε, 0 < ε →
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (lowerPrefactor ε β) / Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  upperPrefactor_log_negligible :
    ∀ ε, 0 < ε →
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (upperPrefactor ε β) / Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε β *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            upperPrefactor ε β *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ → ℝ
  upperPrefactor : ℝ → ℝ → ℝ
  lowerPrefactorLo : ℝ → ℝ
  lowerPrefactorHi : ℝ → ℝ
  upperPrefactorLo : ℝ → ℝ
  upperPrefactorHi : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactorLo_pos : ∀ ε, 0 < ε → 0 < lowerPrefactorLo ε
  lowerPrefactorHi_pos : ∀ ε, 0 < ε → 0 < lowerPrefactorHi ε
  upperPrefactorLo_pos : ∀ ε, 0 < ε → 0 < upperPrefactorLo ε
  upperPrefactorHi_pos : ∀ ε, 0 < ε → 0 < upperPrefactorHi ε
  lowerPrefactor_bounds :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactorLo ε ≤ lowerPrefactor ε β ∧
          lowerPrefactor ε β ≤ lowerPrefactorHi ε
  upperPrefactor_bounds :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        upperPrefactorLo ε ≤ upperPrefactor ε β ∧
          upperPrefactor ε β ≤ upperPrefactorHi ε
  mass_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε β *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            upperPrefactor ε β *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass where
  δ := hbounded.δ
  δ_pos := hbounded.δ_pos
  δ_le_betaC := hbounded.δ_le_betaC
  lowerPrefactor := hbounded.lowerPrefactor
  upperPrefactor := hbounded.upperPrefactor
  mass_pos := hbounded.mass_pos
  lowerPrefactor_pos := by
    intro ε hε
    filter_upwards [hbounded.lowerPrefactor_bounds ε hε] with β hβ
    exact lt_of_lt_of_le (hbounded.lowerPrefactorLo_pos ε hε) hβ.1
  upperPrefactor_pos := by
    intro ε hε
    filter_upwards [hbounded.upperPrefactor_bounds ε hε] with β hβ
    exact lt_of_lt_of_le (hbounded.upperPrefactorLo_pos ε hε) hβ.1
  lowerPrefactor_log_negligible := by
    intro ε hε
    simpa [Ising3DModel] using
      tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
        (hbounded.lowerPrefactorLo_pos ε hε)
        (hbounded.lowerPrefactorHi_pos ε hε)
        (hbounded.lowerPrefactor_bounds ε hε)
  upperPrefactor_log_negligible := by
    intro ε hε
    simpa [Ising3DModel] using
      tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
        (hbounded.upperPrefactorLo_pos ε hε)
        (hbounded.upperPrefactorHi_pos ε hε)
        (hbounded.upperPrefactor_bounds ε hε)
  mass_prefactor_power_sandwich := hbounded.mass_prefactor_power_sandwich

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  mass_constant_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  window : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  window_pos : ∀ ε, 0 < ε → 0 < window ε
  mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - window ε) (Ising.betaC 3) →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  lowerWindow : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  lowerWindow_pos : ∀ ε, 0 < ε → 0 < lowerWindow ε
  mass_lower_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - lowerWindow ε) (Ising.betaC 3) →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  upperPrefactor : ℝ → ℝ
  upperWindow : ℝ → ℝ
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  upperWindow_pos : ∀ ε, 0 < ε → 0 < upperWindow ε
  mass_upper_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - upperWindow ε) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β ≤
          upperPrefactor ε *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          freeSelectedPositiveSubcriticalMass hmass β ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

noncomputable abbrev Ising3DFKBetaC : ℝ :=
  IsingFK.betaC (Ising.magnetization 3)

noncomputable abbrev Ising3DFKPC : ℝ :=
  IsingFK.pOfBeta Ising3DFKBetaC

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKBetaC - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in

structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC →
          freeSelectedPositiveSubcriticalMass hmass β ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  window : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  window_pos : ∀ ε, 0 < ε → 0 < window ε
  mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - window ε) Ising3DFKBetaC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKBetaC - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

namespace FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  window := h.window
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  window_pos := h.window_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using
      h.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  betaWindow : ℝ → ℝ
  pWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  betaWindow_pos : ∀ ε, 0 < ε → 0 < betaWindow ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        freeSelectedPositiveSubcriticalMass hmass β = fkMass (IsingFK.pOfBeta β)
  beta_to_p_window :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC
  p_mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p ∧
          fkMass p ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p))
  beta_to_p_power_transfer_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKBetaC - β)) ≤
            lowerPrefactor ε *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ∧
          upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

namespace FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  betaWindow := h.betaWindow
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  betaWindow_pos := h.betaWindow_pos
  pWindow_pos := h.pWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  beta_to_p_window := h.beta_to_p_window
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp
  beta_to_p_power_transfer_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using h.beta_to_p_power_transfer_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  lowerPrefactor := hpull.lowerPrefactor
  upperPrefactor := hpull.upperPrefactor
  window := hpull.betaWindow
  lowerPrefactor_pos := hpull.lowerPrefactor_pos
  upperPrefactor_pos := hpull.upperPrefactor_pos
  window_pos := hpull.betaWindow_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hpwin := hpull.beta_to_p_window ε hε β hβ
    have hpsand :=
      hpull.p_mass_constant_prefactor_power_sandwich_on_Ioo
        ε hε (IsingFK.pOfBeta β) hpwin
    have htransfer := hpull.beta_to_p_power_transfer_on_Ioo ε hε β hβ
    have hsel := hpull.selected_mass_eq_fkMass ε hε β hβ
    constructor
    · rw [hsel]
      exact le_trans htransfer.1 hpsand.1
    · rw [hsel]
      exact le_trans hpsand.2 htransfer.2

set_option linter.style.longLine false in





structure FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β,
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow pWindow_pos ε)
          Ising3DFKBetaC →
          freeSelectedPositiveSubcriticalMass hmass β =
            fkMass (IsingFK.pOfBeta β)
  p_mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p ∧
          fkMass p ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p))
  beta_to_p_power_transfer_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β,
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow pWindow_pos ε)
          Ising3DFKBetaC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKBetaC - β)) ≤
            lowerPrefactor ε *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ∧
          upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

namespace FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp
  beta_to_p_power_transfer_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using h.beta_to_p_power_transfer_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  fkMass := hcanon.fkMass
  lowerPrefactor := hcanon.lowerPrefactor
  upperPrefactor := hcanon.upperPrefactor
  betaWindow :=
    FKReparameterization.pOfBetaLeftPullbackWindow
      Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos
  pWindow := hcanon.pWindow
  lowerPrefactor_pos := hcanon.lowerPrefactor_pos
  upperPrefactor_pos := hcanon.upperPrefactor_pos
  betaWindow_pos := by
    intro ε hε
    exact
      FKReparameterization.pOfBetaLeftPullbackWindow_pos
        Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos hε
  pWindow_pos := hcanon.pWindow_pos
  selected_mass_eq_fkMass := hcanon.selected_mass_eq_fkMass
  beta_to_p_window := by
    intro ε hε β hβ
    simpa [Ising3DFKPC] using
      FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
        Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos hε hβ
  p_mass_constant_prefactor_power_sandwich_on_Ioo :=
    hcanon.p_mass_constant_prefactor_power_sandwich_on_Ioo
  beta_to_p_power_transfer_on_Ioo := hcanon.beta_to_p_power_transfer_on_Ioo

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCCanonicalWindowPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
    C hmass
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C hmass hcanon)

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  selectedWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  selectedWindow_pos : ∀ ε, 0 < ε → 0 < selectedWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - selectedWindow ε) Ising3DFKBetaC →
        freeSelectedPositiveSubcriticalMass hmass β = fkMass (IsingFK.pOfBeta β)
  p_mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p ∧
          fkMass p ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p))

namespace FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  selectedWindow := h.selectedWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  selectedWindow_pos := h.selectedWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  selectedWindow : ℝ → ℝ
  selectedWindow_pos : ∀ ε, 0 < ε → 0 < selectedWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - selectedWindow ε) Ising3DFKBetaC →
        freeSelectedPositiveSubcriticalMass hmass β = fkMass (IsingFK.pOfBeta β)

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
    (hmass : FreePositiveSubcriticalMassBridge)
    (fkMass : ℝ → ℝ)
    (hEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass hmass β =
          fkMass (IsingFK.pOfBeta β)) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass := by
  classical
  let selectedWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have hselectedWindow_spec :
      0 < selectedWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - selectedWindow) Ising3DFKBetaC →
          freeSelectedPositiveSubcriticalMass hmass β =
            fkMass (IsingFK.pOfBeta β) := by
    simpa [selectedWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { fkMass := fkMass
      selectedWindow := fun _ => selectedWindow
      selectedWindow_pos := by
        intro _ _
        exact hselectedWindow_spec.1
      selected_mass_eq_fkMass := by
        intro _ _ β hβ
        exact hselectedWindow_spec.2 β hβ }

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_forallEq
    (hmass : FreePositiveSubcriticalMassBridge)
    (fkMass : ℝ → ℝ)
    (hEq :
      ∀ β,
        freeSelectedPositiveSubcriticalMass hmass β =
          fkMass (IsingFK.pOfBeta β)) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass :=
  freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
    hmass fkMass
    (Filter.Eventually.of_forall fun β => hEq β)

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  lowerPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  p_mass_lower_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  upperPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  p_mass_upper_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        fkMass p ≤
          upperPrefactor ε *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising3DFKPC - p))

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  p_mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ q, q ∈ Set.Ioo (Ising3DFKPC - p.2) Ising3DFKPC →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - q)) ≤
            fkMass q

set_option linter.style.longLine false in

structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  p_mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ q, q ∈ Set.Ioo (Ising3DFKPC - p.2) Ising3DFKPC →
          fkMass q ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - q))

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
      D fkMass where
  lowerPrefactor := h.lowerPrefactor
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  pWindow_pos := h.pWindow_pos
  p_mass_lower_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using h.p_mass_lower_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
      D fkMass where
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  p_mass_upper_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using h.p_mass_upper_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
      D fkMass where
  p_mass_lower_exists := by
    intro ε hε
    rcases h.p_mass_lower_exists ε hε with ⟨w, hw1, hw2, hbound⟩
    exact ⟨w, hw1, hw2, by
      intro q hq
      simpa [hpred] using hbound q hq⟩

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
      D fkMass where
  p_mass_upper_exists := by
    intro ε hε
    rcases h.p_mass_upper_exists ε hε with ⟨w, hw1, hw2, hbound⟩
    exact ⟨w, hw1, hw2, by
      intro q hq
      simpa [hpred] using hbound q hq⟩

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  massPrefactor : ℝ → ℝ
  massPrefactor_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < massPrefactor p
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (massPrefactor p) / Real.log (Ising3DFKPC - p))
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)) (nhds 0)
  mass_scaling :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      fkMass p =
        massPrefactor p *
          Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p))

namespace FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  massPrefactor := h.massPrefactor
  massPrefactor_pos := h.massPrefactor_pos
  massPrefactor_log_negligible := h.massPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    simpa [hpred] using h.mass_scaling p hp

end FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical

set_option linter.style.longLine false in





structure FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  amplitude : ℝ
  amplitude_pos : 0 < amplitude
  relativePrefactor : ℝ → ℝ
  relativePrefactor_tendsto_one :
    Filter.Tendsto relativePrefactor
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)) (nhds 1)
  mass_scaling :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      fkMass p =
        amplitude * relativePrefactor p *
          Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p))

namespace FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
      D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  amplitude := h.amplitude
  amplitude_pos := h.amplitude_pos
  relativePrefactor := h.relativePrefactor
  relativePrefactor_tendsto_one := h.relativePrefactor_tendsto_one
  mass_scaling := by
    intro p hp
    simpa [hpred] using h.mass_scaling p hp

end FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass := by
  classical
  let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
  have hrelpos :
      ∀ᶠ p in L, 0 < hasymp.relativePrefactor p := by
    have hdist :=
      (Metric.tendsto_nhds.mp hasymp.relativePrefactor_tendsto_one)
        ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hdist] with p hp
    rw [Real.dist_eq] at hp
    have hbounds := abs_sub_lt_iff.mp hp
    linarith
  let posWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hposWindow_spec :
      0 < posWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - posWindow) Ising3DFKPC →
          0 < hasymp.relativePrefactor p := by
    simpa [posWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hprefLog :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (hasymp.amplitude * hasymp.relativePrefactor p) /
            Real.log (Ising3DFKPC - p))
        L (nhds 0) := by
    have hpref :
        Filter.Tendsto
          (fun p : ℝ => hasymp.amplitude * hasymp.relativePrefactor p)
          L (nhds hasymp.amplitude) := by
      simpa using
        (tendsto_const_nhds.mul hasymp.relativePrefactor_tendsto_one)
    have hlogpref :
        Filter.Tendsto
          (fun p : ℝ =>
            Real.log (hasymp.amplitude * hasymp.relativePrefactor p))
          L (nhds (Real.log hasymp.amplitude)) :=
      (Real.continuousAt_log hasymp.amplitude_pos.ne').tendsto.comp hpref
    have hlogd :
        Filter.Tendsto (fun p : ℝ => Real.log (Ising3DFKPC - p))
          L Filter.atBot := by
      simpa [L, ParameterModel] using
        tendsto_log_betaC_sub_atBot (ParameterModel Ising3DFKPC)
    exact hlogpref.div_atBot hlogd
  exact
    { pδ := min hasymp.pδ posWindow
      pδ_pos := lt_min hasymp.pδ_pos hposWindow_spec.1
      massPrefactor := fun p => hasymp.amplitude * hasymp.relativePrefactor p
      massPrefactor_pos := by
        intro p hp
        have hpPos :
            p ∈ Set.Ioo (Ising3DFKPC - posWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hasymp.pδ posWindow]
          · exact hp.2
        exact mul_pos hasymp.amplitude_pos (hposWindow_spec.2 p hpPos)
      massPrefactor_log_negligible := by
        simpa [L] using hprefLog
      mass_scaling := by
        intro p hp
        have hpAsymp :
            p ∈ Set.Ioo (Ising3DFKPC - hasymp.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hasymp.pδ posWindow]
          · exact hp.2
        simpa [mul_assoc] using hasymp.mass_scaling p hpAsymp }

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassFKPCLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  logRemainder : ℝ → ℝ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  logRemainder_negligible :
    Filter.Tendsto
      (fun p : ℝ => logRemainder p / Real.log (Ising3DFKPC - p))
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)) (nhds 0)
  log_fk_mass_scaling :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      Real.log (fkMass p) =
        C.predictedExponent * Real.log (Ising3DFKPC - p) +
          logRemainder p

set_option linter.style.longLine false in




structure FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  log_fk_mass_ratio_tendsto :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkMass p) / Real.log (Ising3DFKPC - p))
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC))
      (nhds C.predictedExponent)

set_option linter.style.longLine false in



structure FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  log_fk_mass_ratio_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        C.predictedExponent - ε <
            Real.log (fkMass p) / Real.log (Ising3DFKPC - p) ∧
          Real.log (fkMass p) / Real.log (Ising3DFKPC - p) <
            C.predictedExponent + ε

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass where
  pδ := hexact.pδ
  pδ_pos := hexact.pδ_pos
  logRemainder := fun p => Real.log (hexact.massPrefactor p)
  fkMass_pos := by
    intro p hp
    rw [hexact.mass_scaling p hp]
    exact mul_pos (hexact.massPrefactor_pos p hp) (Real.exp_pos _)
  logRemainder_negligible := hexact.massPrefactor_log_negligible
  log_fk_mass_scaling := by
    intro p hp
    have hpref_pos : 0 < hexact.massPrefactor p :=
      hexact.massPrefactor_pos p hp
    have hpref_ne : hexact.massPrefactor p ≠ 0 := hpref_pos.ne'
    have hexp_ne :
        Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [hexact.mass_scaling p hp, Real.log_mul hpref_ne hexp_ne,
      Real.log_exp]
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
    C fkMass
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass where
  pδ := hlog.pδ
  pδ_pos := hlog.pδ_pos
  fkMass_pos := hlog.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
    have hlimit :
        Filter.Tendsto
          (fun p : ℝ =>
            C.predictedExponent +
              hlog.logRemainder p / Real.log (Ising3DFKPC - p))
          L (nhds C.predictedExponent) := by
      simpa [L] using tendsto_const_nhds.add hlog.logRemainder_negligible
    refine Filter.Tendsto.congr' ?_ hlimit
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - hlog.pδ < Ising3DFKPC by
          linarith [hlog.pδ_pos]),
        Ioo_mem_nhdsLT
          (show Ising3DFKPC - (1 : ℝ) < Ising3DFKPC by norm_num)]
      with p hpδ hpone
    have hdiff : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hpone.1, hpone.2]
    have hden : Real.log (Ising3DFKPC - p) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      C.predictedExponent +
          hlog.logRemainder p / Real.log (Ising3DFKPC - p) =
        Real.log (fkMass p) / Real.log (Ising3DFKPC - p)
    rw [hlog.log_fk_mass_scaling p hpδ]
    field_simp [hden]

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logAffineNearCritical
    C fkMass
    (freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
      C fkMass hexact)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_exactPowerLaw
    C fkMass
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
      C fkMass hasymp)

namespace FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  fkMass_pos := h.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    simpa [hpred] using h.log_fk_mass_ratio_tendsto

end FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    {fkMass modelMass : ℝ → ℝ}
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass := by
  classical
  let eqWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have heqWindow_spec :
      0 < eqWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
          fkMass p = modelMass p := by
    simpa [eqWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { pδ := min hratio.pδ eqWindow
      pδ_pos := lt_min hratio.pδ_pos heqWindow_spec.1
      fkMass_pos := by
        intro p hp
        have hpMass :
            p ∈ Set.Ioo (Ising3DFKPC - hratio.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hratio.pδ eqWindow]
          · exact hp.2
        have hpEq :
            p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hratio.pδ eqWindow]
          · exact hp.2
        have hlocal : fkMass p = modelMass p :=
          heqWindow_spec.2 p hpEq
        rw [hlocal]
        exact hratio.fkMass_pos p hpMass
      log_fk_mass_ratio_tendsto := by
        refine Filter.Tendsto.congr' ?_ hratio.log_fk_mass_ratio_tendsto
        filter_upwards [hEq] with p hlocal
        simp [hlocal] }

namespace FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  fkMass_pos := h.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro ε hε
    filter_upwards [h.log_fk_mass_ratio_sandwich ε hε] with p hp
    simpa [hpred] using hp

end FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    {fkMass modelMass : ℝ → ℝ}
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass := by
  classical
  let eqWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have heqWindow_spec :
      0 < eqWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
          fkMass p = modelMass p := by
    simpa [eqWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { pδ := min hsand.pδ eqWindow
      pδ_pos := lt_min hsand.pδ_pos heqWindow_spec.1
      fkMass_pos := by
        intro p hp
        have hpMass :
            p ∈ Set.Ioo (Ising3DFKPC - hsand.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hsand.pδ eqWindow]
          · exact hp.2
        have hpEq :
            p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hsand.pδ eqWindow]
          · exact hp.2
        have hlocal : fkMass p = modelMass p :=
          heqWindow_spec.2 p hpEq
        rw [hlocal]
        exact hsand.fkMass_pos p hpMass
      log_fk_mass_ratio_sandwich := by
        intro ε hε
        filter_upwards [hsand.log_fk_mass_ratio_sandwich ε hε, hEq]
          with p hp hlocal
        constructor
        · simpa [hlocal] using hp.1
        · simpa [hlocal] using hp.2 }

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass where
  pδ := hsand.pδ
  pδ_pos := hsand.pδ_pos
  fkMass_pos := hsand.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsand.log_fk_mass_ratio_sandwich ε hε] with p hp
    rw [Real.dist_eq]
    exact abs_sub_lt_iff.mpr (by constructor <;> linarith [hp.1, hp.2])

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLogRatioSandwich_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := hratio.pδ
  pδ_pos := hratio.pδ_pos
  fkMass_pos := hratio.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro ε hε
    have hdist :=
      (Metric.tendsto_nhds.mp hratio.log_fk_mass_ratio_tendsto) ε hε
    filter_upwards [hdist] with p hp
    rw [Real.dist_eq] at hp
    have hpabs := abs_sub_lt_iff.mp hp
    constructor <;> linarith [hpabs.1, hpabs.2]

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass where
  pδ := hratio.pδ
  pδ_pos := hratio.pδ_pos
  logRemainder := fun p =>
    Real.log (fkMass p) -
      C.predictedExponent * Real.log (Ising3DFKPC - p)
  fkMass_pos := hratio.fkMass_pos
  logRemainder_negligible := by
    let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
    have hconst :
        Filter.Tendsto (fun _ : ℝ => C.predictedExponent) L
          (nhds C.predictedExponent) :=
      tendsto_const_nhds
    have hshift :
        Filter.Tendsto
          (fun p : ℝ =>
            Real.log (fkMass p) / Real.log (Ising3DFKPC - p) -
              C.predictedExponent)
          L (nhds 0) := by
      simpa [L] using hratio.log_fk_mass_ratio_tendsto.sub hconst
    refine Filter.Tendsto.congr' ?_ hshift
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - 1 < Ising3DFKPC by linarith)] with p hp
    have hdiff : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hp.1, hp.2]
    have hden : Real.log (Ising3DFKPC - p) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      Real.log (fkMass p) / Real.log (Ising3DFKPC - p) -
          C.predictedExponent =
        (Real.log (fkMass p) -
            C.predictedExponent * Real.log (Ising3DFKPC - p)) /
          Real.log (Ising3DFKPC - p)
    field_simp [hden]
  log_fk_mass_scaling := by
    intro p hp
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass where
  pδ := hlog.pδ
  pδ_pos := hlog.pδ_pos
  massPrefactor := fun p => Real.exp (hlog.logRemainder p)
  massPrefactor_pos := by
    intro p hp
    exact Real.exp_pos _
  massPrefactor_log_negligible := by
    simpa [Real.log_exp] using hlog.logRemainder_negligible
  mass_scaling := by
    intro p hp
    have hmpos : 0 < fkMass p := hlog.fkMass_pos p hp
    calc
      fkMass p =
          Real.exp (Real.log (fkMass p)) := by
        rw [Real.exp_log hmpos]
      _ =
          Real.exp
            (C.predictedExponent * Real.log (Ising3DFKPC - p) +
              hlog.logRemainder p) := by
        rw [hlog.log_fk_mass_scaling p hp]
      _ =
          Real.exp (hlog.logRemainder p) *
            Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) := by
        rw [Real.exp_add, mul_comm]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
    C fkMass
    (freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
      C fkMass hratio)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C T.fkMass where
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  massPrefactor := T.fkMassPrefactor
  massPrefactor_pos := by
    intro p hp
    exact T.fkMassPrefactor_pos p (by
      simpa [Ising3DFKPC, ← hβeq] using hp)
  massPrefactor_log_negligible := by
    simpa [Ising3DFKPC, ← hβeq] using T.fkMassPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    simpa [Ising3DFKPC, ← hβeq] using
      T.fk_mass_scaling p (by
        simpa [Ising3DFKPC, ← hβeq] using hp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {fkMass : ℝ → ℝ}
    (hfkMass : T.fkMass = fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass := by
  subst fkMass
  exact freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget
    C hβeq T

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {fkMass : ℝ → ℝ}
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = fkMass p) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass where
  pδ :=
    min T.pδ
      (Classical.choose
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass))
  pδ_pos := by
    exact lt_min T.pδ_pos
      (Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)).1
  massPrefactor := T.fkMassPrefactor
  massPrefactor_pos := by
    intro p hp
    have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.pδ) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_left T.pδ
          (Classical.choose
            (FKReparameterization.exists_Ioo_subset_of_eventually_left
              hfkMass))]
      · exact hp.2
    exact T.fkMassPrefactor_pos p (by
      simpa [Ising3DFKPC, ← hβeq] using hpT)
  massPrefactor_log_negligible := by
    simpa [Ising3DFKPC, ← hβeq] using T.fkMassPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    let eqWindow : ℝ :=
      Classical.choose
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)
    have heqWindow_spec :
        0 < eqWindow ∧
          ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
            T.fkMass p = fkMass p := by
      simpa [eqWindow] using
        Classical.choose_spec
          (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)
    have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.pδ) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_left T.pδ eqWindow]
      · exact hp.2
    have hpEq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_right T.pδ eqWindow]
      · exact hp.2
    have hlocal : T.fkMass p = fkMass p :=
      heqWindow_spec.2 p hpEq
    have hscale :
        T.fkMass p =
          T.fkMassPrefactor p *
            Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) := by
      simpa [Ising3DFKPC, ← hβeq] using
        T.fk_mass_scaling p (by
          simpa [Ising3DFKPC, ← hβeq] using hpT)
    exact hlocal.symm.trans hscale

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass := by
  classical
  let pWindow : ℝ → ℝ := fun _ => T.pδ
  have hpWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε := by
    intro _ _
    exact T.pδ_pos
  have hfkLength_event :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          T.fkCorrelationLength (IsingFK.pOfBeta β) := by
    simpa [Ising3DFKBetaC, ← hβeq] using T.ising_fk_length_agree
  let fkLengthWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left
        hfkLength_event)
  have hfkLengthWindow_spec :
      0 < fkLengthWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - fkLengthWindow) Ising3DFKBetaC →
          T.isingCorrelationLength β =
            T.fkCorrelationLength (IsingFK.pOfBeta β) := by
    simpa [fkLengthWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left
          hfkLength_event)
  let selectedLengthWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left
        hisingLength)
  have hselectedLengthWindow_spec :
      0 < selectedLengthWindow ∧
        ∀ β,
          β ∈ Set.Ioo (Ising3DFKBetaC - selectedLengthWindow) Ising3DFKBetaC →
            T.isingCorrelationLength β =
              freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β := by
    simpa [selectedLengthWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left
          hisingLength)
  refine
    { fkMass := T.fkMass
      selectedWindow := fun ε =>
        min (min fkLengthWindow selectedLengthWindow)
          (FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC pWindow hpWindow_pos ε)
      selectedWindow_pos := ?_
      selected_mass_eq_fkMass := ?_ }
  · intro ε hε
    exact lt_min (lt_min hfkLengthWindow_spec.1 hselectedLengthWindow_spec.1)
      (FKReparameterization.pOfBetaLeftPullbackWindow_pos
        Ising3DFKBetaC pWindow hpWindow_pos hε)
  · intro ε hε β hβ
    have hfkLength_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          fkLengthWindow :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hselectedLength_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          selectedLengthWindow :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hpull_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC pWindow hpWindow_pos ε :=
      min_le_right _ _
    have hβ_fkLength :
        β ∈ Set.Ioo (Ising3DFKBetaC - fkLengthWindow) Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hfkLength_le]
      · exact hβ.2
    have hβ_selectedLength :
        β ∈ Set.Ioo (Ising3DFKBetaC - selectedLengthWindow)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hselectedLength_le]
      · exact hβ.2
    have hβ_pullback :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hpull_le]
      · exact hβ.2
    have hpwin :
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - T.pδ)
          Ising3DFKPC := by
      simpa [pWindow, Ising3DFKPC] using
        FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
          Ising3DFKBetaC pWindow hpWindow_pos hε hβ_pullback
    have hfkAgree :=
      hfkLengthWindow_spec.2 β hβ_fkLength
    have hselectedAgree :=
      hselectedLengthWindow_spec.2 β hβ_selectedLength
    have hlength :
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          T.fkCorrelationLength (IsingFK.pOfBeta β) :=
      hselectedAgree.symm.trans hfkAgree
    have hfk_length :
        T.fkCorrelationLength (IsingFK.pOfBeta β) =
          (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
      exact T.fk_length_eq_inv_mass (IsingFK.pOfBeta β) (by
        simpa [Ising3DFKPC, ← hβeq] using hpwin)
    have hinv :
        (freeSelectedPositiveSubcriticalMass hmass β)⁻¹ =
          (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
      unfold freeSelectedPositiveSubcriticalCorrelationLengthFromMass at hlength
      simpa [hfk_length] using hlength
    simpa using congrArg Inv.inv hinv

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass :=
  freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
    C hmass hβeq T
    (Filter.Eventually.of_forall fun β => by
      rw [hisingLength])

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCLowerExists_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    {fkMass : ℝ → ℝ}
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
      C fkMass where
  p_mass_lower_exists := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hsmall :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          Real.log (hexact.massPrefactor p) /
              Real.log (Ising3DFKPC - p) <
            ε / 2 := by
      have hdist :=
        (Metric.tendsto_nhds.mp hexact.massPrefactor_log_negligible)
          (ε / 2) hhalf
      filter_upwards [hdist] with p hp
      rw [Real.dist_eq] at hp
      exact (abs_lt.mp (by simpa using hp)).2
    have hevent :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          (1 : ℝ) *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - p)) ≤
            fkMass p := by
      filter_upwards
        [hsmall,
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - hexact.pδ < Ising3DFKPC by
              linarith [hexact.pδ_pos]),
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - 1 < Ising3DFKPC by norm_num)]
        with p hsmallp hpδ hpone
      let L := Real.log (Ising3DFKPC - p)
      have hdist01 : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hpone.1, hpone.2]
      have hLneg : L < 0 := by
        simpa [L] using Real.log_neg hdist01.1 hdist01.2
      have hLne : L ≠ 0 := hLneg.ne
      have hpref_pos : 0 < hexact.massPrefactor p :=
        hexact.massPrefactor_pos p hpδ
      have hlog_pref_lower :
          (ε / 2) * L < Real.log (hexact.massPrefactor p) := by
        calc
          (ε / 2) * L <
              (Real.log (hexact.massPrefactor p) / L) * L := by
            exact mul_lt_mul_of_neg_right hsmallp hLneg
          _ = Real.log (hexact.massPrefactor p) := by
            field_simp [hLne]
      have hexp_le :
          Real.exp
              ((C.predictedExponent + ε / 2) * L) ≤
            hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) := by
        calc
          Real.exp
              ((C.predictedExponent + ε / 2) * L) ≤
              Real.exp
                (Real.log (hexact.massPrefactor p) +
                  C.predictedExponent * L) := by
            rw [Real.exp_le_exp]
            linarith
          _ =
              hexact.massPrefactor p *
                Real.exp (C.predictedExponent * L) := by
            rw [Real.exp_add, Real.exp_log hpref_pos]
      calc
        (1 : ℝ) *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) =
          Real.exp
            ((C.predictedExponent + ε / 2) * L) := by
            simp [L]
        _ ≤
          hexact.massPrefactor p *
            Real.exp (C.predictedExponent * L) :=
            hexp_le
        _ = fkMass p := by
            rw [hexact.mass_scaling p hpδ]
    obtain ⟨δ, hδpos, hδ⟩ :=
      FKReparameterization.exists_Ioo_subset_of_eventually_left hevent
    exact ⟨(1, δ), by norm_num, hδpos, hδ⟩

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCUpperExists_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    {fkMass : ℝ → ℝ}
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
      C fkMass where
  p_mass_upper_exists := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hsmall :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          -(ε / 2) <
            Real.log (hexact.massPrefactor p) /
              Real.log (Ising3DFKPC - p) := by
      have hdist :=
        (Metric.tendsto_nhds.mp hexact.massPrefactor_log_negligible)
          (ε / 2) hhalf
      filter_upwards [hdist] with p hp
      rw [Real.dist_eq] at hp
      exact (abs_lt.mp (by simpa using hp)).1
    have hevent :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          fkMass p ≤
            (1 : ℝ) *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p)) := by
      filter_upwards
        [hsmall,
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - hexact.pδ < Ising3DFKPC by
              linarith [hexact.pδ_pos]),
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - 1 < Ising3DFKPC by norm_num)]
        with p hsmallp hpδ hpone
      let L := Real.log (Ising3DFKPC - p)
      have hdist01 : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hpone.1, hpone.2]
      have hLneg : L < 0 := by
        simpa [L] using Real.log_neg hdist01.1 hdist01.2
      have hLne : L ≠ 0 := hLneg.ne
      have hpref_pos : 0 < hexact.massPrefactor p :=
        hexact.massPrefactor_pos p hpδ
      have hlog_pref_upper :
          Real.log (hexact.massPrefactor p) < -(ε / 2) * L := by
        calc
          Real.log (hexact.massPrefactor p) =
              (Real.log (hexact.massPrefactor p) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hsmallp hLneg
      have hexp_le :
          hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) ≤
            Real.exp
              ((C.predictedExponent - ε / 2) * L) := by
        calc
          hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) =
              Real.exp
                (Real.log (hexact.massPrefactor p) +
                  C.predictedExponent * L) := by
            rw [Real.exp_add, Real.exp_log hpref_pos]
          _ ≤
              Real.exp
                ((C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_le_exp]
            linarith
      calc
        fkMass p =
          hexact.massPrefactor p *
            Real.exp (C.predictedExponent * L) := by
            rw [hexact.mass_scaling p hpδ]
        _ ≤
          Real.exp
            ((C.predictedExponent - ε / 2) * L) :=
            hexp_le
        _ =
          (1 : ℝ) *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising3DFKPC - p)) := by
            simp [L]
    obtain ⟨δ, hδpos, hδ⟩ :=
      FKReparameterization.exists_Ioo_subset_of_eventually_left hevent
    exact ⟨(1, δ), by norm_num, hδpos, hδ⟩

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLower_of_exists
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
      C fkMass where
  lowerPrefactor := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hlower.p_mass_lower_exists ε hε)).1
    else 1
  pWindow := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hlower.p_mass_lower_exists ε hε)).2
    else 1
  lowerPrefactor_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).1
  pWindow_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).2.1
  p_mass_lower_on_Ioo := by
    intro ε hε q hq
    have hq' :
        q ∈ Set.Ioo
          (Ising3DFKPC -
            (Classical.choose (hlower.p_mass_lower_exists ε hε)).2)
          Ising3DFKPC := by
      simpa [dif_pos hε] using hq
    simpa [dif_pos hε] using
      (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).2.2 q hq'

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCUpper_of_exists
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
      C fkMass where
  upperPrefactor := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hupper.p_mass_upper_exists ε hε)).1
    else 1
  pWindow := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hupper.p_mass_upper_exists ε hε)).2
    else 1
  upperPrefactor_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).1
  pWindow_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).2.1
  p_mass_upper_on_Ioo := by
    intro ε hε q hq
    have hq' :
        q ∈ Set.Ioo
          (Ising3DFKPC -
            (Classical.choose (hupper.p_mass_upper_exists ε hε)).2)
          Ising3DFKPC := by
      simpa [dif_pos hε] using hq
    simpa [dif_pos hε] using
      (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).2.2 q hq'

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  fkMass := hselected.fkMass
  lowerPrefactor := hlower.lowerPrefactor
  upperPrefactor := hupper.upperPrefactor
  pWindow := fun ε => min (hlower.pWindow ε) (hupper.pWindow ε)
  selectedWindow := hselected.selectedWindow
  lowerPrefactor_pos := hlower.lowerPrefactor_pos
  upperPrefactor_pos := hupper.upperPrefactor_pos
  pWindow_pos := by
    intro ε hε
    exact lt_min (hlower.pWindow_pos ε hε) (hupper.pWindow_pos ε hε)
  selectedWindow_pos := hselected.selectedWindow_pos
  selected_mass_eq_fkMass := hselected.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    have hp_lower :
        p ∈ Set.Ioo (Ising3DFKPC - hlower.pWindow ε) Ising3DFKPC := by
      constructor
      · have hle :
            Ising3DFKPC - hlower.pWindow ε ≤
              Ising3DFKPC - min (hlower.pWindow ε) (hupper.pWindow ε) :=
          sub_le_sub_left
            (min_le_left (hlower.pWindow ε) (hupper.pWindow ε))
            Ising3DFKPC
        exact lt_of_le_of_lt hle hp.1
      · exact hp.2
    have hp_upper :
        p ∈ Set.Ioo (Ising3DFKPC - hupper.pWindow ε) Ising3DFKPC := by
      constructor
      · have hle :
            Ising3DFKPC - hupper.pWindow ε ≤
              Ising3DFKPC - min (hlower.pWindow ε) (hupper.pWindow ε) :=
          sub_le_sub_left
            (min_le_right (hlower.pWindow ε) (hupper.pWindow ε))
            Ising3DFKPC
        exact lt_of_le_of_lt hle hp.1
      · exact hp.2
    constructor
    · exact hlower.p_mass_lower_on_Ioo ε hε p hp_lower
    · exact hupper.p_mass_upper_on_Ioo ε hε p hp_upper

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
    C hmass hselected
    (freePositiveSubcriticalMassFKPCLower_of_exists C hselected.fkMass hlower)
    (freePositiveSubcriticalMassFKPCUpper_of_exists C hselected.fkMass hupper)

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
    C hmass hselected
    (freePositiveSubcriticalMassFKPCLowerExists_of_exactPowerLaw C hexact)
    (freePositiveSubcriticalMassFKPCUpperExists_of_exactPowerLaw C hexact)

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  lowerPrefactor := fun ε =>
    hp.lowerPrefactor ε *
      Real.exp
        ((C.predictedExponent + ε / 2) *
          Real.log (Real.exp (-2 * Ising3DFKBetaC)))
  upperPrefactor := fun ε =>
    hp.upperPrefactor ε *
      FKReparameterization.expLogUpperComparisonPrefactor
        (Real.exp (-2 * Ising3DFKBetaC))
        (3 * Real.exp (-2 * Ising3DFKBetaC))
        (C.predictedExponent - ε / 2)
  window := fun ε =>
    min
      (min
        (hp.selectedWindow ε)
        (FKReparameterization.pOfBetaLeftPullbackWindow
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
      (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
        Ising3DFKBetaC)
  lowerPrefactor_pos := by
    intro ε hε
    exact mul_pos (hp.lowerPrefactor_pos ε hε) (Real.exp_pos _)
  upperPrefactor_pos := by
    intro ε hε
    exact mul_pos (hp.upperPrefactor_pos ε hε)
      (FKReparameterization.expLogUpperComparisonPrefactor_pos _ _ _)
  window_pos := by
    intro ε hε
    exact lt_min
      (lt_min (hp.selectedWindow_pos ε hε)
        (FKReparameterization.pOfBetaLeftPullbackWindow_pos
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos hε))
      (FKReparameterization.pOfBetaCriticalDistanceComparableWindow_pos
        Ising3DFKBetaC)
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    let lo : ℝ := Real.exp (-2 * Ising3DFKBetaC)
    let hi : ℝ := 3 * Real.exp (-2 * Ising3DFKBetaC)
    let d : ℝ := Ising3DFKBetaC - β
    let pd : ℝ := Ising3DFKPC - IsingFK.pOfBeta β
    have hlo : 0 < lo := by
      dsimp [lo]
      exact Real.exp_pos _
    have hhi : 0 < hi := by
      dsimp [hi]
      exact mul_pos (by norm_num) (Real.exp_pos _)
    have hd : 0 < d := by
      dsimp [d]
      exact sub_pos.mpr hβ.2
    have hwin_selected :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          hp.selectedWindow ε :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hwin_pullback :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hwin_compare :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          FKReparameterization.pOfBetaCriticalDistanceComparableWindow
            Ising3DFKBetaC :=
      min_le_right _ _
    have hβ_selected :
        β ∈ Set.Ioo (Ising3DFKBetaC - hp.selectedWindow ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_selected]
      · exact hβ.2
    have hβ_pullback :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_pullback]
      · exact hβ.2
    have hβ_compare :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_compare]
      · exact hβ.2
    have hpwin :
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - hp.pWindow ε)
          Ising3DFKPC := by
      simpa [Ising3DFKPC] using
        FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos hε hβ_pullback
    have hcmp_raw :=
      FKReparameterization.pOfBeta_criticalDistance_comparable_of_mem_Ioo_left
        hβ_compare
    have hcmp :
        lo * d ≤ pd ∧ pd ≤ hi * d := by
      simpa [lo, hi, d, pd, Ising3DFKPC] using hcmp_raw
    have hsel := hp.selected_mass_eq_fkMass ε hε β hβ_selected
    have hpsand :=
      hp.p_mass_constant_prefactor_power_sandwich_on_Ioo
        ε hε (IsingFK.pOfBeta β) hpwin
    rw [hsel]
    constructor
    · have hk :
          0 ≤ C.predictedExponent + ε / 2 := by
        exact le_of_lt (add_pos (C.predictedExponent_pos) (half_pos hε))
      have htransfer :
          Real.exp ((C.predictedExponent + ε / 2) * Real.log lo) *
              Real.exp ((C.predictedExponent + ε / 2) * Real.log d) ≤
            Real.exp ((C.predictedExponent + ε / 2) * Real.log pd) :=
        FKReparameterization.exp_log_lower_power_transfer_no_slack_of_mul_le
          hlo hd hk hcmp.1
      calc
        (hp.lowerPrefactor ε *
              Real.exp
                ((C.predictedExponent + ε / 2) * Real.log lo)) *
            Real.exp ((C.predictedExponent + ε / 2) * Real.log d)
            =
          hp.lowerPrefactor ε *
            (Real.exp
                ((C.predictedExponent + ε / 2) * Real.log lo) *
              Real.exp ((C.predictedExponent + ε / 2) * Real.log d)) := by
            ring
        _ ≤
          hp.lowerPrefactor ε *
            Real.exp ((C.predictedExponent + ε / 2) * Real.log pd) := by
            exact mul_le_mul_of_nonneg_left htransfer
              (le_of_lt (hp.lowerPrefactor_pos ε hε))
        _ ≤ hp.fkMass (IsingFK.pOfBeta β) := by
            simpa [pd] using hpsand.1
    · have htransfer :
          Real.exp ((C.predictedExponent - ε / 2) * Real.log pd) ≤
            FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2) *
              Real.exp ((C.predictedExponent - ε / 2) * Real.log d) :=
        FKReparameterization.exp_log_upper_power_transfer_of_comparable
          hlo hhi hd hcmp.1 hcmp.2
      calc
        hp.fkMass (IsingFK.pOfBeta β) ≤
          hp.upperPrefactor ε *
            Real.exp ((C.predictedExponent - ε / 2) * Real.log pd) := by
            simpa [pd] using hpsand.2
        _ ≤
          hp.upperPrefactor ε *
            (FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2) *
              Real.exp ((C.predictedExponent - ε / 2) * Real.log d)) := by
            exact mul_le_mul_of_nonneg_left htransfer
              (le_of_lt (hp.upperPrefactor_pos ε hε))
        _ =
          (hp.upperPrefactor ε *
              FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2)) *
            Real.exp ((C.predictedExponent - ε / 2) * Real.log d) := by
            ring

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCLowerBoundExistsNoWindow_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
      C hmass where
  mass_lower_exists := by
    intro ε hε
    refine ⟨(hsand.lowerPrefactor ε, hsand.window ε), ?_, ?_, ?_⟩
    · exact hsand.lowerPrefactor_pos ε hε
    · exact hsand.window_pos ε hε
    · intro β hβ
      exact (hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ).1

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCUpperExists_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
      C hmass where
  mass_upper_exists := by
    intro ε hε
    refine ⟨(hsand.upperPrefactor ε, hsand.window ε), ?_, ?_, ?_⟩
    · exact hsand.upperPrefactor_pos ε hε
    · exact hsand.window_pos ε hε
    · intro β hβ
      exact (hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ).2

set_option linter.style.longLine false in


def freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindow_of_fkBetaC
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
      C hmass where
  mass_lower_exists := by
    intro ε hε
    obtain ⟨p, hp_pref, hp_window, hp_bound⟩ := hlower.mass_lower_exists ε hε
    refine ⟨p, hp_pref, hp_window, ?_⟩
    intro β hβ
    have hβ_fk : β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using hp_bound β hβ_fk

set_option linter.style.longLine false in


def freePositiveSubcriticalMassConstantPrefactorWeakIooUpperExists_of_fkBetaC
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
      C hmass where
  mass_upper_exists := by
    intro ε hε
    obtain ⟨p, hp_pref, hp_window, hp_bound⟩ := hupper.mass_upper_exists ε hε
    refine ⟨p, hp_pref, hp_window, ?_⟩
    intro β hβ
    have hβ_fk : β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using hp_bound β hβ_fk

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_fkBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  δ := min (hsand.window 1) (Ising.betaC 3)
  δ_pos := lt_min (hsand.window_pos 1 zero_lt_one) hβc
  δ_le_betaC := min_le_right _ _
  lowerPrefactor := hsand.lowerPrefactor
  upperPrefactor := hsand.upperPrefactor
  window := hsand.window
  mass_pos := by
    intro β hβ
    have hβ_window :
        β ∈ Set.Ioo (Ising.betaC 3 - hsand.window 1) (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, min_le_left (hsand.window 1) (Ising.betaC 3)]
      · exact hβ.2
    have hβ_fk :
        β ∈ Set.Ioo (Ising3DFKBetaC - hsand.window 1) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ_window
    have hlower :=
      (hsand.mass_constant_prefactor_power_sandwich_on_Ioo
        1 zero_lt_one β hβ_fk).1
    have hprod_pos :
        0 <
          hsand.lowerPrefactor 1 *
            Real.exp
              ((C.predictedExponent + 1 / 2) *
                Real.log (Ising3DFKBetaC - β)) :=
      mul_pos (hsand.lowerPrefactor_pos 1 zero_lt_one) (Real.exp_pos _)
    exact lt_of_lt_of_le hprod_pos hlower
  lowerPrefactor_pos := hsand.lowerPrefactor_pos
  upperPrefactor_pos := hsand.upperPrefactor_pos
  window_pos := hsand.window_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hβ_fk :
        β ∈ Set.Ioo (Ising3DFKBetaC - hsand.window ε) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using
      hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ_fk

set_option linter.style.longLine false in



noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExists_of_betaC_pos_noWindow
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
      C hmass where
  δ :=
    min (Ising.betaC 3)
      (Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2
  δ_pos := by
    classical
    exact
      lt_min hβc
        (Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2.1
  δ_le_betaC := by
    exact min_le_left _ _
  mass_lower_exists := hlower.mass_lower_exists

set_option linter.style.longLine false in



noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLowerExists_of_lowerBoundExists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
      C hmass where
  δ :=
    min hlower.δ
      (Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2
  δ_pos := by
    classical
    exact
      lt_min hlower.δ_pos
        (Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2.1
  δ_le_betaC := by
    exact le_trans (min_le_left _ _) hlower.δ_le_betaC
  mass_pos := by
    intro β hβ
    classical
    let p :=
      Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))
    have hp :
        0 < p.1 ∧ 0 < p.2 ∧
          ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
            p.1 *
                Real.exp
                  ((C.predictedExponent + (1 : ℝ) / 2) *
                    Real.log (Ising.betaC 3 - β)) ≤
              freeSelectedPositiveSubcriticalMass hmass β := by
      simpa [p] using
        Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))
    change
      β ∈ Set.Ioo (Ising.betaC 3 - min hlower.δ p.2)
        (Ising.betaC 3) at hβ
    have hmin : min hlower.δ p.2 ≤ p.2 := min_le_right _ _
    have hβp : β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin]
      · exact hβ.2
    have hle := hp.2.2 β hβp
    have hleft_pos :
        0 <
          p.1 *
            Real.exp
              ((C.predictedExponent + (1 : ℝ) / 2) *
                Real.log (Ising.betaC 3 - β)) := by
      exact mul_pos hp.1 (Real.exp_pos _)
    exact lt_of_lt_of_le hleft_pos hle
  mass_lower_exists := hlower.mass_lower_exists

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLower_of_exists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
      C hmass where
  δ := hlower.δ
  δ_pos := hlower.δ_pos
  δ_le_betaC := hlower.δ_le_betaC
  lowerPrefactor := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hlower.mass_lower_exists ε hε)
      else
        (1, 1)).1
  lowerWindow := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hlower.mass_lower_exists ε hε)
      else
        (1, 1)).2
  mass_pos := hlower.mass_pos
  lowerPrefactor_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).1
  lowerWindow_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).2.1
  mass_lower_on_Ioo := by
    intro ε hε β hβ
    classical
    rw [dif_pos hε] at hβ ⊢
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).2.2 β hβ

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooUpper_of_exists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
      C hmass where
  upperPrefactor := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hupper.mass_upper_exists ε hε)
      else
        (1, 1)).1
  upperWindow := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hupper.mass_upper_exists ε hε)
      else
        (1, 1)).2
  upperPrefactor_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).1
  upperWindow_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).2.1
  mass_upper_on_Ioo := by
    intro ε hε β hβ
    classical
    rw [dif_pos hε] at hβ ⊢
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).2.2 β hβ

set_option linter.style.longLine false in



noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  δ := hlower.δ
  δ_pos := hlower.δ_pos
  δ_le_betaC := hlower.δ_le_betaC
  lowerPrefactor := hlower.lowerPrefactor
  upperPrefactor := hupper.upperPrefactor
  window := fun ε => min (hlower.lowerWindow ε) (hupper.upperWindow ε)
  mass_pos := hlower.mass_pos
  lowerPrefactor_pos := hlower.lowerPrefactor_pos
  upperPrefactor_pos := hupper.upperPrefactor_pos
  window_pos := by
    intro ε hε
    exact lt_min (hlower.lowerWindow_pos ε hε) (hupper.upperWindow_pos ε hε)
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hmin_lower :
        min (hlower.lowerWindow ε) (hupper.upperWindow ε) ≤
          hlower.lowerWindow ε :=
      min_le_left _ _
    have hmin_upper :
        min (hlower.lowerWindow ε) (hupper.upperWindow ε) ≤
          hupper.upperWindow ε :=
      min_le_right _ _
    have hβ_lower :
        β ∈ Set.Ioo (Ising.betaC 3 - hlower.lowerWindow ε)
          (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin_lower]
      · exact hβ.2
    have hβ_upper :
        β ∈ Set.Ioo (Ising.betaC 3 - hupper.upperWindow ε)
          (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin_upper]
      · exact hβ.2
    exact
      ⟨hlower.mass_lower_on_Ioo ε hε β hβ_lower,
        hupper.mass_upper_on_Ioo ε hε β hβ_upper⟩

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
      C hmass where
  δ := hIoo.δ
  δ_pos := hIoo.δ_pos
  δ_le_betaC := hIoo.δ_le_betaC
  lowerPrefactor := hIoo.lowerPrefactor
  upperPrefactor := hIoo.upperPrefactor
  mass_pos := hIoo.mass_pos
  lowerPrefactor_pos := hIoo.lowerPrefactor_pos
  upperPrefactor_pos := hIoo.upperPrefactor_pos
  mass_constant_prefactor_power_sandwich := by
    intro ε hε
    have hleft : Ising.betaC 3 - hIoo.window ε < Ising.betaC 3 := by
      linarith [hIoo.window_pos ε hε]
    filter_upwards [Ioo_mem_nhdsLT hleft] with β hβ
    exact hIoo.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass where
  δ := hsub.δ
  δ_pos := hsub.δ_pos
  δ_le_betaC := hsub.δ_le_betaC
  mass_pos := hsub.mass_pos
  mass_power_sandwich := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hlowerSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          Real.log (hsub.lowerPrefactor ε β) /
              Real.log (Ising.betaC 3 - β) <
            ε / 2 := by
      have hdist :=
        (Metric.tendsto_nhds.mp
          (hsub.lowerPrefactor_log_negligible ε hε)) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).2
    have hupperSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          -(ε / 2) <
            Real.log (hsub.upperPrefactor ε β) /
              Real.log (Ising.betaC 3 - β) := by
      have hdist :=
        (Metric.tendsto_nhds.mp
          (hsub.upperPrefactor_log_negligible ε hε)) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).1
    filter_upwards
      [hsub.mass_prefactor_power_sandwich ε hε,
        hsub.lowerPrefactor_pos ε hε,
        hsub.upperPrefactor_pos ε hε,
        hlowerSmall,
        hupperSmall,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpref hlowerPos hupperPos hlowerSmallβ hupperSmallβ hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hLne : L ≠ 0 := hLneg.ne
    constructor
    · have hlowerLog :
          (ε / 2) * L < Real.log (hsub.lowerPrefactor ε β) := by
        calc
          (ε / 2) * L <
              (Real.log (hsub.lowerPrefactor ε β) / L) * L := by
            exact mul_lt_mul_of_neg_right hlowerSmallβ hLneg
          _ = Real.log (hsub.lowerPrefactor ε β) := by
            field_simp [hLne]
      have hexpLower :
          Real.exp ((C.predictedExponent + ε) * L) <
            hsub.lowerPrefactor ε β *
              Real.exp ((C.predictedExponent + ε / 2) * L) := by
        calc
          Real.exp ((C.predictedExponent + ε) * L) <
              Real.exp
                (Real.log (hsub.lowerPrefactor ε β) +
                  (C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_lt_exp]
            linarith
          _ =
              hsub.lowerPrefactor ε β *
                Real.exp ((C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log hlowerPos]
      exact lt_trans hexpLower hβpref.1
    · have hupperLog :
          Real.log (hsub.upperPrefactor ε β) < -(ε / 2) * L := by
        calc
          Real.log (hsub.upperPrefactor ε β) =
              (Real.log (hsub.upperPrefactor ε β) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hupperSmallβ hLneg
      have hexpUpper :
          hsub.upperPrefactor ε β *
              Real.exp ((C.predictedExponent - ε / 2) * L) <
            Real.exp ((C.predictedExponent - ε) * L) := by
        calc
          hsub.upperPrefactor ε β *
              Real.exp ((C.predictedExponent - ε / 2) * L) =
              Real.exp
                (Real.log (hsub.upperPrefactor ε β) +
                  (C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log hupperPos]
          _ < Real.exp ((C.predictedExponent - ε) * L) := by
            rw [Real.exp_lt_exp]
            linarith
      exact lt_trans hβpref.2 hexpUpper

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassPowerSandwich_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
    C hmass
    (freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass where
  δ := hconst.δ
  δ_pos := hconst.δ_pos
  δ_le_betaC := hconst.δ_le_betaC
  mass_pos := hconst.mass_pos
  mass_power_sandwich := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hlowerNegligible :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hconst.lowerPrefactor ε) /
              Real.log (Ising.betaC 3 - β))
          (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
          (nhds 0) := by
      simpa [Ising3DModel] using
        tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
          (hconst.lowerPrefactor_pos ε hε)
          (hconst.lowerPrefactor_pos ε hε)
          (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    have hupperNegligible :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hconst.upperPrefactor ε) /
              Real.log (Ising.betaC 3 - β))
          (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
          (nhds 0) := by
      simpa [Ising3DModel] using
        tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
          (hconst.upperPrefactor_pos ε hε)
          (hconst.upperPrefactor_pos ε hε)
          (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    have hlowerSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          Real.log (hconst.lowerPrefactor ε) /
              Real.log (Ising.betaC 3 - β) <
            ε / 2 := by
      have hdist := (Metric.tendsto_nhds.mp hlowerNegligible) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).2
    have hupperSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          -(ε / 2) <
            Real.log (hconst.upperPrefactor ε) /
              Real.log (Ising.betaC 3 - β) := by
      have hdist := (Metric.tendsto_nhds.mp hupperNegligible) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).1
    filter_upwards
      [hconst.mass_constant_prefactor_power_sandwich ε hε,
        hlowerSmall,
        hupperSmall,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpref hlowerSmallβ hupperSmallβ hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hLne : L ≠ 0 := hLneg.ne
    constructor
    · have hlowerLog :
          (ε / 2) * L < Real.log (hconst.lowerPrefactor ε) := by
        calc
          (ε / 2) * L <
              (Real.log (hconst.lowerPrefactor ε) / L) * L := by
            exact mul_lt_mul_of_neg_right hlowerSmallβ hLneg
          _ = Real.log (hconst.lowerPrefactor ε) := by
            field_simp [hLne]
      have hexpLower :
          Real.exp ((C.predictedExponent + ε) * L) <
            hconst.lowerPrefactor ε *
              Real.exp ((C.predictedExponent + ε / 2) * L) := by
        calc
          Real.exp ((C.predictedExponent + ε) * L) <
              Real.exp
                (Real.log (hconst.lowerPrefactor ε) +
                  (C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_lt_exp]
            linarith
          _ =
              hconst.lowerPrefactor ε *
                Real.exp ((C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log (hconst.lowerPrefactor_pos ε hε)]
      exact lt_of_lt_of_le hexpLower hβpref.1
    · have hupperLog :
          Real.log (hconst.upperPrefactor ε) < -(ε / 2) * L := by
        calc
          Real.log (hconst.upperPrefactor ε) =
              (Real.log (hconst.upperPrefactor ε) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hupperSmallβ hLneg
      have hexpUpper :
          hconst.upperPrefactor ε *
              Real.exp ((C.predictedExponent - ε / 2) * L) <
            Real.exp ((C.predictedExponent - ε) * L) := by
        calc
          hconst.upperPrefactor ε *
              Real.exp ((C.predictedExponent - ε / 2) * L) =
              Real.exp
                (Real.log (hconst.upperPrefactor ε) +
                  (C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log (hconst.upperPrefactor_pos ε hε)]
          _ < Real.exp ((C.predictedExponent - ε) * L) := by
            rw [Real.exp_lt_exp]
            linarith
      exact lt_of_le_of_lt hβpref.2 hexpUpper

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioSandwich_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass where
  δ := hpow.δ
  δ_pos := hpow.δ_pos
  δ_le_betaC := hpow.δ_le_betaC
  mass_pos := hpow.mass_pos
  log_mass_ratio_sandwich := by
    intro ε hε
    filter_upwards
      [hpow.mass_power_sandwich ε hε,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpow hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hmpos : 0 < m := by
      exact lt_trans (Real.exp_pos _) hβpow.1
    have hlog_lower :
        (C.predictedExponent + ε) * L < Real.log m := by
      have hlog := Real.log_lt_log (Real.exp_pos _) hβpow.1
      simpa [m, L, Real.log_exp] using hlog
    have hlog_upper :
        Real.log m < (C.predictedExponent - ε) * L := by
      have hlog := Real.log_lt_log hmpos hβpow.2
      simpa [m, L, Real.log_exp] using hlog
    constructor
    · have hLpos : 0 < -L := neg_pos.mpr hLneg
      have hLne : L ≠ 0 := hLneg.ne
      change C.predictedExponent - ε < Real.log m / L
      refine lt_of_mul_lt_mul_right ?_ hLpos.le
      calc
        (C.predictedExponent - ε) * -L =
            -((C.predictedExponent - ε) * L) := by
          ring
        _ < -Real.log m := by
          linarith
        _ = (Real.log m / L) * -L := by
          field_simp [hLne]
    · have hLpos : 0 < -L := neg_pos.mpr hLneg
      have hLne : L ≠ 0 := hLneg.ne
      change Real.log m / L < C.predictedExponent + ε
      refine lt_of_mul_lt_mul_right ?_ hLpos.le
      calc
        (Real.log m / L) * -L = -Real.log m := by
          field_simp [hLne]
        _ < -((C.predictedExponent + ε) * L) := by
          linarith
        _ = (C.predictedExponent + ε) * -L := by
          ring

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hsand.δ
  δ_pos := hsand.δ_pos
  δ_le_betaC := hsand.δ_le_betaC
  mass_pos := hsand.mass_pos
  log_mass_ratio_tendsto := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsand.log_mass_ratio_sandwich ε hε] with β hβ
    rw [Real.dist_eq]
    exact abs_sub_lt_iff.mpr (by constructor <;> linarith [hβ.1, hβ.2])

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
    C hmass
    (freePositiveSubcriticalMassLogRatioSandwich_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    C hmass
    (freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
    C hmass
    (freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    C hmass
    (freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_fkBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_fkBetaCIooSandwich
      C hmass hβeq hβc hsand)

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_fkPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_fkBetaCIooSandwich
    C hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C hmass
      (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
        C hmass hselected
        (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
          C hselected.fkMass hratio)))

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass where
  δ := hratio.δ
  δ_pos := hratio.δ_pos
  δ_le_betaC := hratio.δ_le_betaC
  logRemainder := fun β =>
    Real.log (freeSelectedPositiveSubcriticalMass hmass β) -
      C.predictedExponent * Real.log (Ising.betaC 3 - β)
  mass_pos := hratio.mass_pos
  logRemainder_negligible := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hconst :
        Filter.Tendsto (fun _ : ℝ => C.predictedExponent) L
          (nhds C.predictedExponent) :=
      tendsto_const_nhds
    have hshift :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) -
                C.predictedExponent)
          L (nhds 0) := by
      simpa [L] using hratio.log_mass_ratio_tendsto.sub hconst
    refine Filter.Tendsto.congr' ?_ hshift
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)] with β hβ
    have hdiff : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hden : Real.log (Ising.betaC 3 - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β) -
            C.predictedExponent =
        (Real.log (freeSelectedPositiveSubcriticalMass hmass β) -
            C.predictedExponent * Real.log (Ising.betaC 3 - β)) /
          Real.log (Ising.betaC 3 - β)
    field_simp [hden]
  log_mass_scaling := by
    intro β hβ
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass where
  δ := hlog.δ
  δ_pos := hlog.δ_pos
  δ_le_betaC := hlog.δ_le_betaC
  massPrefactor := fun β => Real.exp (hlog.logRemainder β)
  massPrefactor_pos := by
    intro β hβ
    exact Real.exp_pos _
  massPrefactor_log_negligible := by
    simpa [Real.log_exp] using hlog.logRemainder_negligible
  mass_scaling := by
    intro β hβ
    have hmpos : 0 < freeSelectedPositiveSubcriticalMass hmass β :=
      hlog.mass_pos β hβ
    calc
      freeSelectedPositiveSubcriticalMass hmass β =
          Real.exp (Real.log (freeSelectedPositiveSubcriticalMass hmass β)) := by
        rw [Real.exp_log hmpos]
      _ =
          Real.exp
            (C.predictedExponent * Real.log (Ising.betaC 3 - β) +
              hlog.logRemainder β) := by
        rw [hlog.log_mass_scaling β hβ]
      _ =
          Real.exp (hlog.logRemainder β) *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
        rw [Real.exp_add, mul_comm]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
    C hmass
    (freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
      C hmass hratio)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    hagree hmass hpower.δ hpower.δ_pos hpower.δ_le_betaC
    hpower.massPrefactor hpower.massPrefactor_pos
    hpower.massPrefactor_log_negligible hpower.mass_scaling

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
      C hmass hlog)

set_option linter.style.longLine false in

noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
      C hmass hratio)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLower_of_exists
      C hmass hlower)
    (freePositiveSubcriticalMassConstantPrefactorWeakIooUpper_of_exists
      C hmass hupper)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerExists_of_lowerBoundExists
      C hmass hlower)
    hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExists_of_betaC_pos_noWindow
      C hmass hβc hlower)
    hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hmass hβc
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindow_of_fkBetaC
      C hmass hβeq hlower)
    (freePositiveSubcriticalMassConstantPrefactorWeakIooUpperExists_of_fkBetaC
      C hmass hβeq hupper)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCLowerBoundExistsNoWindow_of_constantPrefactorWeakIooSandwich
      C hmass hsand)
    (freePositiveSubcriticalMassFKBetaCUpperExists_of_constantPrefactorWeakIooSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
      C hmass hpull)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCCanonicalWindowPullbackIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C hmass hcanon)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C hmass hp)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
      C hmass hselected hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
      C hmass hselected hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
      C hmass hselected hexact)

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected hexact).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected hexact).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
      C hselected.fkMass hlog)

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogAffineNearCritical
    C hagree hmass hβeq hβc hselected hlog).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogAffineNearCritical
    C hagree hmass hβeq hβc hselected hlog).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
      C hselected.fkMass hratio)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C hselected.fkMass hsand)

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree hmass hβeq hβc hselected hratio).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree hmass hβeq hβc hselected hratio).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree hmass hβeq hβc hselected hsand).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree hmass hβeq hβc hselected hsand).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
      C hβeq T hfkMass)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
      C hβeq T hfkMass)

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
      C hmass hβeq T hisingLength
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree hmass hβeq hβc hselected T rfl

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
      C hmass hβeq T hisingLength
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree hmass hβeq hβc hselected T rfl

set_option linter.style.longLine false in



theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree hmass hβeq hβc T hisingLength).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree hmass hβeq hβc T hisingLength).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree hmass hβeq hβc T
    (Filter.Eventually.of_forall (fun β => by
      simp [hisingLength]))

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree hmass hβeq hβc T
    (Filter.Eventually.of_forall (fun β => by
      simp [hisingLength]))







structure FiniteCurrentMassBridgeInputs where
  massBridge : FreePositiveSubcriticalMassBridge

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentMassBridgeInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

set_option linter.style.longLine false in


noncomputable def ofActualScheduleProjectionInputs
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in




noncomputable def ofThresholdCandidateEmbeddingProjectionInputs
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in




noncomputable def ofExpandedDemandProjectionInputs
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in




noncomputable def ofBoundaryGhostComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcomparison : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed hcomparison hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofProfileSlackActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hprofile hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofPaidPlusProfileDominatesSimonPlusActiveActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdom :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hdom hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofUnpaidRemainderLeProfileSlackActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofUnpaidRemainderPlusActiveLeProfileActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprofile :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hprofile hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofUnpaidRemainderPlusCollapsedActiveImageLeProfileActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcollapsed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hcollapsed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofTargetMultiplicityMainEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (htarget :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict htarget hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofTargetMultiplicityMainEmptySlackSplitActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsplit :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsplit hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoundaryMultiplicityAndImageWeightLeMainEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoundaryMultiplicityMainAndImageWeightEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmain :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmain hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hempty :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hempty hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitFallbackMixedActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitFallbackMixedDeficitNonpositiveActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitFallbackMixedPaymentDominatesActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofExpandedDemandActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteAtomChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteInjectionChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteSetInjectionChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofScalarThresholdActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofRankedPrefixActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hranked :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hranked hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofSortedAtomSlotActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsorted :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsorted hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hinjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hinjection hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotSubtypeInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsubtypeInjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsubtypeInjection hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofMainEmptyGapAllocationActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hallocation :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hallocation hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofMainEmptyGapActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hgap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hgap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofMainEmptyGapMassSplitActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmass :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmass hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofUnpaidRemainderNonpositiveActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hnonpos :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hnonpos hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofMainGapSumActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmainGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmainGap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofEmptyGapActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hemptyGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hemptyGap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirBranchCoverActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirBranchDisjunctionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirBranchSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitBranchCoverActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitBranchDisjunctionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitBranchSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofReservoirSplitBranchFirstTrueSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotHallActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hhall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hhall hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotCapacityHallActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcapacityHall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hcapacityHall hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotCapacityThresholdActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCanonicalSlotCapacityDisjointActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdisjoint :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hdisjoint hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofThresholdInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofThresholdSubtypeInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofThresholdCandidateEmbeddingActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofExactPolynomialBoundaryActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofPolynomialBoundaryActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in




noncomputable def ofFreeFVQ2ExactRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in



noncomputable def ofFreeFVQ2SubexpRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in




noncomputable def ofBoundaryGhostFirstExitPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfirst hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoxGeometryComponentThirdsAbsorptionProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hthirds hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsum hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCapBoundBoxRatioComponentShareProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCapBoundBoxRatioComponentSumProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hcapNonneg hsum hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofBoxRatioComponentThirdsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofCapBoundBoxRatioComponentsProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsum hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hshare hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hsum hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor h hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hshare hprojection⟩

set_option linter.style.longLine false in




noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15AggregateComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hbudget hone hboundary hempty hshell hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def
    ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hstrict hshare hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hremaining htail hsingleton hpayment hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hremaining htail hpayment hsingletonResidual hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hsingletonResidual hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hsingletonResidual hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hpayment hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule) (label := label)
    hR hstrict hremaining htail hpayment hprojection⟩

set_option linter.style.longLine false in




noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hR hrawStrict hrawPayment hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hR hraw hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hpos hraw hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hpaid hraw hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hR hraw hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hpos hraw hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hpaid hraw hprojection⟩

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hprojection⟩

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile⟩

set_option linter.style.longLine false in


noncomputable def ofSimonFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsimon hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteFKSimonFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteIsingSimonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hprojection⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hstrict hdiag hprofile⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hstrict hdiag hprofile⟩

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale
      hone hprofile)⟩

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale
      hone hprofile)⟩

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in



noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
      honeLocal)
    hprofile

set_option linter.style.longLine false in



noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
      honeLocal)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfiniteAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay
    (freeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical_of_eventually_at
      hfiniteAt)
    honeLocal
    (freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at
      hprofileAt)

set_option linter.style.longLine false in




noncomputable def ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimonAt :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FiniteQ2SimonFreeBoundaryIsingBoxAt β n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay
    (finiteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical_of_eventually_at
      hSimonAt)
    honeLocal
    (freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at
      hprofileAt)

set_option linter.style.longLine false in





noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
        hstrictLocal))
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
        hdiagLocal))
    hprofile

set_option linter.style.longLine false in



noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
        hstrictLocal))
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
        hdiagLocal))
    hprofile

set_option linter.style.longLine false in




noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hstrict hdiag⟩

set_option linter.style.longLine false in



noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hstrict hdiag⟩

set_option linter.style.longLine false in





noncomputable def ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
    hlim hdecay hcompare⟩

set_option linter.style.longLine false in



noncomputable def ofFreeFVQ2TwoSidedPolynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate
    hlim hdecay hrate⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedDirectionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate
    hlim hdecay hdir⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper
    hlim hdecay htension⟩

set_option linter.style.longLine false in




noncomputable def ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper
    hlim hdecay htension⟩

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree I.massBridge hpower

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree I.massBridge hasymp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree I.massBridge hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree I.massBridge hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree I.massBridge hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_powerSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree I.massBridge hpow

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβc hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβeq hβc hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree I.massBridge hβeq hβc hsand

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
    C hagree hβeq hβc (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    C hagree I.massBridge hβeq hβc hpull

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
    C hagree hβeq hβc (hpull.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCCanonicalWindowPullbackIooSandwich
    C hagree I.massBridge hβeq hβc hcanon

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
    C hagree hβeq hβc (hcanon.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree I.massBridge hβeq hβc hp

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
    C hagree hβeq hβc (hp.congr_predictedExponent hpred)

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        D hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    C hagree hβeq hβc hselected
    (hlower.congr_predictedExponent hpred)
    (hupper.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        D hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    C hagree hβeq hβc hselected
    (hlower.congr_predictedExponent hpred)
    (hupper.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget C hagree hpower)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw C hagree hasymp)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logAffine C hagree hlog)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioLimit C hagree hratio)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioSandwich C hagree hsand)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_powerSandwich C hagree hpow)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hβc hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCLowerBoundExistsNoWindowUpperExists
      C hagree hβeq hβc hlower hupper)

set_option linter.style.longLine false in




theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
      C hagree hβeq hβc hsand)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hsand)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
      C hagree hβeq hβc hpull)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hpull)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
      C hagree hβeq hβc hcanon)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hcanon)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
      C hagree hβeq hβc hp)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hp)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
      C hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
      C hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        D hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
      C D hpred hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        D hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
      C D hpred hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree I.massBridge hβeq hβc hselected hexact

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    I C hagree hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
      C hselected.fkMass hlog)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree I.massBridge hβeq hβc hselected hsand

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            I.massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
          hlim hdecay hfinite hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
      hlim hdecay hfinite hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonDoubledBoxPolynomialProjection
          hlim hdecay hSimon hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonDoubledBoxPolynomialProjection
      hlim hdecay hSimon hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
          hlim hdecay hfinite hstrict hdiag).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hdecay hfinite hstrict hdiag)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
          hlim hdecay hSimon hstrict hdiag).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hdecay hSimon hstrict hdiag)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
          hlim hdecay hfinite hstrict hdiag hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
      hlim hdecay hfinite hstrict hdiag hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
          hlim hdecay hSimon hstrict hdiag hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
      hlim hdecay hSimon hstrict hdiag hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
          hlim hdecay hfinite hone hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
      hlim hdecay hfinite hone hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
          hlim hdecay hSimon hone hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
      hlim hdecay hSimon hone hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
          hlim hdecay hfinite honeLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
      hlim hdecay hfinite honeLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
          hlim hdecay hSimon honeLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
      hlim hdecay hSimon honeLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfiniteAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
          hlim hdecay hfiniteAt honeLocal hprofileAt).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
      hlim hdecay hfiniteAt honeLocal hprofileAt)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimonAt :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FiniteQ2SimonFreeBoundaryIsingBoxAt β n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
          hlim hdecay hSimonAt honeLocal hprofileAt).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
      hlim hdecay hSimonAt honeLocal hprofileAt)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
          hlim hdecay hfinite hstrictLocal hdiagLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
      hlim hdecay hfinite hstrictLocal hdiagLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
          hlim hdecay hSimon hstrictLocal hdiagLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
      hlim hdecay hSimon hstrictLocal hdiagLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2ExactRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2ExactRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2ExactRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2SubexpRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcomparison : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoundaryGhostComparisonProjection
          hlim hfixed hcomparison hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoundaryGhostComparisonProjection
      hlim hfixed hcomparison hprojection)
    C hagree hpower

set_option linter.style.longLine false in






theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostFirstExitPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoundaryGhostFirstExitPositiveProjection
          hlim hdecay hfirst hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoundaryGhostFirstExitPositiveProjection
      hlim hdecay hfirst hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxGeometryComponentThirdsAbsorptionProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxGeometryComponentThirdsAbsorptionProjection
          hlim hdecay hthirds hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxGeometryComponentThirdsAbsorptionProjection
      hlim hdecay hthirds hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentShareProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentShareProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentSumProjection
          hlim hdecay hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentSumProjection
      hlim hdecay hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentShareProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentShareProjection
          hlim hdecay hcap hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentShareProjection
      hlim hdecay hcap hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentSumProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentSumProjection
          hlim hdecay hcap hcapNonneg hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentSumProjection
      hlim hdecay hcap hcapNonneg hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentThirdsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentThirdsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentThirdsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentsProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentsProjection
          hlim hdecay hcap hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentsProjection
      hlim hdecay hcap hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
          hlim hdecay hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
      hlim hdecay hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
          hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
      hlim hdecay hmajor hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
          hlim hdecay hmajor hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
      hlim hdecay hmajor hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
          hlim hdecay hmajor hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
      hlim hdecay hmajor hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
          hlim hdecay hmajor h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
      hlim hdecay hmajor h hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
          hlim hdecay hmajor hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
      hlim hdecay hmajor hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
          hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
      hlim hdecay hmajor hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15CanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15ComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
          hlim hdecay hbudget hone hboundary hempty hshell hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
      hlim hdecay hbudget hone hboundary hempty hshell hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hstrict hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hstrict hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
          hlim hdecay hremaining htail hsingleton hpayment
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
      hlim hdecay hremaining htail hsingleton hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
          hlim hdecay hremaining htail hpayment hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
      hlim hdecay hremaining htail hpayment hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
          hlim hdecay hR hstrict hremaining htail hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
      hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
          hlim hdecay hR hstrict hremaining htail hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
      hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
          hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
      hlim hdecay hR hstrict hremaining htail hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
          hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
      hlim hdecay hR hstrict hremaining htail hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_logRatioLimit
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hratio

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_powerSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hpow

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooExistsLowerUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβc hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkBetaCIooSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hsand

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCPullbackIooSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hpull

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCCanonicalWindowPullbackIooSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hcanon

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedIooSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hp

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpperExists
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
          hlim hdecay hR hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
      hlim hdecay hR hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
          hlim hdecay hR hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
      hlim hdecay hR hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
          hlim hdecay hpos hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
      hlim hdecay hpos hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hpaid hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hpaid hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
          hlim hdecay hpos hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
      hlim hdecay hpos hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hpaid hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hpaid hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hpower

set_option linter.style.longLine false in





theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogAffine
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hlog

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioLimit
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hsand

set_option linter.style.longLine false in





theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementExactPowerLaw
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hexact

set_option linter.style.longLine false in




theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
              hlim hdecay hcompare).massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc T hisingLength

set_option linter.style.longLine false in




theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
            hlim hdecay hcompare).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc T hisingLength

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
          hlim hdecay htension).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hpower

set_option linter.style.longLine false in




theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCSelectedAgreementExactPowerLaw
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
          hlim hdecay htension).massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hβeq hβc hselected hexact

set_option linter.style.longLine false in




theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
              hlim hdecay htension).massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hβeq hβc T hisingLength

end FiniteCurrentMassBridgeInputs

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree I.massBridge hpower

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree I.massBridge hasymp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree I.massBridge hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree I.massBridge hratio

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementExactPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree I.massBridge hβeq hβc hselected hexact

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogAffineNearCritical
    C hagree I.massBridge hβeq hβc hselected hlog

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree I.massBridge hsand

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree I.massBridge hβeq hβc hselected hsand

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementFKMassPowerLawTarget
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree I.massBridge hβeq hβc hselected T hfkMass

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget_eventuallyEq
    C hagree I.massBridge hβeq hβc hselected T hfkMass

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCFKMassPowerLawTargetLengthEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            I.massBridge β) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_powerSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree I.massBridge hpow

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_subpowerPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    C hagree I.massBridge hsub

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_boundedPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    C hagree I.massBridge hbounded

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    C hagree I.massBridge hconst

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    C hagree I.massBridge hIoo

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβc hlower hupper

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget C hagree hpower)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw C hagree hasymp)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logAffine C hagree hlog)

set_option linter.style.longLine false in



structure AnalyticLogRatioBridge
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel) where
  plus_free_agree : PlusFreeTwoPointAgreeBelowBetaC
  free_mass_log_ratio :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_asymptoticPowerLaw
      C I.massBridge hasymp

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_fkPCSelectedAgreementLogRatioLimit
      C I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioLimit C hagree hratio)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_analyticLogRatioBridge
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hbridge : AnalyticLogRatioBridge I C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  I.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    C hbridge.plus_free_agree hbridge.free_mass_log_ratio

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioSandwich C hagree hsand)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_powerSandwich C hagree hpow)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_subpowerPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_subpowerPrefactorSandwich
      C hagree hsub)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_boundedPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_boundedPrefactorSandwich
      C hagree hbounded)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakSandwich
      C hagree hconst)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooSandwich
      C hagree hIoo)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
      C hagree hlower hupper)

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hβc hlower hupper)

end FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in





noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass
            (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
              hlim hfixed hone hboundary hcmp hprojection) β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    δ hδ hδle massPrefactor hmassPrefactor_pos
    hmassPrefactor_log_negligible hmass_scaling

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hpower

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hasymp

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlog

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hratio

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hsand

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hpow

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hsub

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hbounded

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hconst

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hIoo

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hβc hlower hupper

set_option linter.style.longLine false in





theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass
            (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
              hlim hfixed hone hboundary hcmp hprojection) β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection
      C hagree hlim hfixed hone hboundary hcmp hprojection δ hδ hδle
      massPrefactor hmassPrefactor_pos hmassPrefactor_log_negligible
      hmass_scaling)

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
      C hagree hlim hfixed hone hboundary hcmp hprojection hpower)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
      C hagree hlim hfixed hone hboundary hcmp hprojection hasymp)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
      C hagree hlim hfixed hone hboundary hcmp hprojection hlog)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
      C hagree hlim hfixed hone hboundary hcmp hprojection hratio)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hsand)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hpow)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hsub)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hbounded)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hconst)

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hIoo)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hlim hfixed hone hboundary hcmp hprojection hβc hlower hupper)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
      htc_pos hbdd hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
      htc_pos hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeWitnessSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (hβ0mem : β0 ∈ Sharpness.tildeBetaCIsingSet 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_tildeBetaCIsing_pos_of_positive_mem
      hbddTilde hβ0 hβ0mem)
    hsqrt hzero hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeBddSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove
      hbddTilde hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_phiBarrierSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier
      hbarrier hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos
      hzeroSet heventual hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg
      hzeroSet heventual hmono hnonneg hsqrt)
    hlower hupper

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
      hzeroSet heventual hmono hsqrt)
    hlower hupper

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)
    hmono hsqrt hlower hupper

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionAssemblyMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet
    htransition.transitionRegime hmono hsqrt hlower hupper

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_transitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
      htransition hnonpos)
    hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCTransitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
      C hagree
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
        htransition hnonpos)
      hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
      C hagree
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
        htransition hnonpos)
      hsand)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hpull)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCCanonicalWindowPullbackIooSandwichTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hcanon)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hp)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C
        hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C
        hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hlower hupper)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hexact)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
      C hselected.fkMass hratio)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C hselected.fkMass hsand)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
      C
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hfkMass)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
      C
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hfkMass)

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
            hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hmass :=
    freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
      C hmass
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hisingLength
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected T rfl

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
              hlim hfixed hone hboundary hcmp hprojection) β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hmass :=
    freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
      C hmass
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hisingLength
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected T rfl

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hlower hupper

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hexact

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogAffineTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
      C hselected.fkMass hlog)

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hratio

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hsand

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected T hfkMass

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected T hfkMass

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos T
    hisingLength

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            I.massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos T
    hisingLength

end FiniteCurrentActualScheduleProjectionInputs

end Exact3D
end StatMech
