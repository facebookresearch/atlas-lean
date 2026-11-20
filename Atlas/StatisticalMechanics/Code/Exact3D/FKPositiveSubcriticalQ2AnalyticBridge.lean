/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKAnalyticBridgeTarget
import Code.Exact3D.FKPositiveSubcriticalQ2Bridge











open Filter

namespace StatMech
namespace Exact3D

namespace FKToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeQ2ExactPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofFreeQ2SubexpPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofFreeQ2TwoSidedPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofFreeQ2ProfileSeparatePositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ProfileSeparatePositiveSubcritical_components
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
      hlim hsameMass hcombine)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ProfileSeparatePositiveSubcritical_splitSubexpProfile
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
      hlim hfixed hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexPointwisePositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise
      hlim hfixed hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryProfileComparisonPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryProfileFiniteVolumePolynomialComparisonPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexComparisonPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq





noncomputable def
    ofFreeQ2BoundaryVertexFiniteVolumePolynomialComparisonPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexRatePositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate
            hlim hfixed hrate) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate
      hlim hfixed hrate)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexDirectionalRatePositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_directionalRate
            hlim hfixed hdir) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_directionalRate hlim hfixed hdir)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofFreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper
      hlim hfixed htension)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper
      hlim hfixed htension)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofWiredQ2ExactPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2SubexpPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq



noncomputable def ofWiredQ2TwoSidedPositiveSubcritical
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ExactPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2SubexpPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2TwoSidedPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ProfileSeparatePositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ProfileSeparatePositiveSubcriticalMass_components
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
      hlim hsameMass hcombine)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ProfileSeparatePositiveSubcriticalMass_splitSubexpProfile
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
      hlim hfixed hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexPointwisePositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_boundaryVertexPointwise
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_boundaryVertexPointwise
      hlim hfixed hprofile)
    δ hδ hδle fkCorrelationLength hfk hEq





noncomputable def ofFreeQ2BoundaryVertexComparisonPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryProfileFiniteVolumePolynomialComparisonPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryVertexFiniteVolumePolynomialComparisonPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexRatePositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
            hlim hfixed hrate) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
      hlim hfixed hrate)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexDirectionalRatePositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_directionalRate
            hlim hfixed hdir) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_directionalRate hlim hfixed hdir)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
      hlim hfixed htension)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def
    ofFreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
      hlim hfixed htension)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2ExactPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Exact
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2SubexpPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2TwoSidedPositiveSubcriticalMass
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ExactPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2SubexpPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2TwoSidedPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ExactPositiveSubcritical_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2SubexpPositiveSubcritical_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2TwoSidedPositiveSubcritical_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2ExactPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2SubexpPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2TwoSidedPositiveSubcritical_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveCorrelationLengthBridge
    (C := C) hagree
    (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ExactPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2SubexpPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2TwoSidedPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofFreeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
      hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2ExactPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2SubexpPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq




noncomputable def ofWiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C :=
  ofFreePositiveMassBridge
    (C := C) hagree
    (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
      hbad hcmp hdecay)
    δ hδ hδle fkCorrelationLength hfk hEq

end FKToIsingAnalyticRGToExponentTarget

end Exact3D
end StatMech
