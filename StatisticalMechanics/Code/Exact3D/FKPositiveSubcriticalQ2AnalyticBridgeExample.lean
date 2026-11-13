/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.ExponentTheorem
import Code.Exact3D.FKFinitePlusTailBridge
import Code.Exact3D.FKPositiveSubcriticalQ2AnalyticBridge
import Code.Exact3D.FKTableClosedBallBridge
import Code.Exact3D.FinitePlusTailContractionExample
import Code.Exact3D.FiniteWitnessPackageExample











open Filter

namespace StatMech
namespace Exact3D
namespace FKPositiveSubcriticalQ2AnalyticBridgeExample

open FinitePlusTailContractionExample
open FiniteWitnessPackageExample

variable {C : RGCertificate Ising3DModel}

private theorem exact_from_fkTarget
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_hasCriticalNu_from_fkTarget C T

private theorem exact_liminf_from_fkTarget
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_fkTarget C T

variable
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
  (fkCorrelationLength : ℝ → ℝ)
  (hfk :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength C.predictedExponent)

include hagree δ hδ hδle hfk



theorem ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_liminf_hasCriticalNu_from_freeQ2ExactPositiveSubcritical
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_liminf_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2SubexpPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2TwoSidedPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_components
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
          hlim hfixed hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2ProfileSeparatePositiveSubcritical_splitSubexpProfile
      hagree hlim hfixed hprofile δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise
          hlim hfixed hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexPointwisePositiveSubcritical
      hagree hlim hfixed hprofile δ hδ hδle
      fkCorrelationLength hfk hEq)





theorem ising3D_hasCriticalNu_from_freeQ2BoundaryProfileComparison
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryProfileComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparison
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryProfileFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparison
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparison
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparison
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate
            hlim hfixed hrate) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate
          hlim hfixed hrate))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexRatePositiveSubcritical
      hagree hlim hfixed hrate δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_directionalRate
            hlim hfixed hdir) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_directionalRate
          hlim hfixed hdir))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexDirectionalRatePositiveSubcritical
      hagree hlim hfixed hdir δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper
          hlim hfixed htension))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical
      hagree hlim hfixed htension δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper
          hlim hfixed htension))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical
      hagree hlim hfixed htension δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem ising3D_liminf_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_liminf_from_fkTarget
    (ofFreeQ2ProfileSeparatePositiveSubcritical_splitSubexpProfile
      hagree hlim hfixed hprofile δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2ExactPositiveSubcritical
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2SubexpPositiveSubcritical
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcritical
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcriticalMass
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem
    ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2SubexpPositiveSubcriticalMass
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2TwoSidedPositiveSubcriticalMass
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem
    ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_components
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ProfileSeparateMass_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
          hlim hfixed hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2ProfileSeparatePositiveSubcriticalMass_splitSubexpProfile
      hagree hlim hfixed hprofile δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwiseMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_boundaryVertexPointwise
            hlim hfixed hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_boundaryVertexPointwise
          hlim hfixed hprofile))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexPointwisePositiveSubcriticalMass
      hagree hlim hfixed hprofile δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparisonMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparisonMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryProfileFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparisonMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRateMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
            hlim hfixed hrate) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
          hlim hfixed hrate))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexRatePositiveSubcriticalMass
      hagree hlim hfixed hrate δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRateMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_directionalRate
            hlim hfixed hdir) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_directionalRate
          hlim hfixed hdir))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexDirectionalRatePositiveSubcriticalMass
      hagree hlim hfixed hdir δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpperMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
          hlim hfixed htension))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcriticalMass
      hagree hlim hfixed htension δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpperMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
            hlim hfixed htension) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
          hlim hfixed htension))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  open FKToIsingAnalyticRGToExponentTarget in
  exact_from_fkTarget
    (ofFreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcriticalMass
      hagree hlim hfixed htension δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Exact
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2ExactPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem
    ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2SubexpPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2SubexpPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2TwoSidedPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2ExactPositiveSubcritical_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2SubexpPositiveSubcritical_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem
    ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcritical_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcriticalMass_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2SubexpPositiveSubcriticalMass_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2TwoSidedPositiveSubcriticalMass_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem
    ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
          hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2ExactPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2SubexpPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
          hbad hcmp hdecay))
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  exact_from_fkTarget
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)

section PackageBoundaryExamples



theorem closedBall_bridge_from_freeQ2ExactPositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_freeQ2ExactPositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical
      hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcriticalMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcriticalMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass
      hagree hprofile δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_freeQ2ProfileSeparate_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem closedBall_valid_from_freeQ2ProfileSeparate_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem closedBall_hasCriticalNu_from_freeQ2ProfileSeparate_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcritical_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_scaledProfileFiniteVolumePolynomial
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare)) :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_scaledProfileFiniteVolumePolynomial
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare)) :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)




theorem closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomial
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcritical
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_scaledProfileFiniteVolumePolynomialMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare)) :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_scaledProfileFiniteVolumePolynomialMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare)) :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)




theorem closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomialMass
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
            hlim hfixed hcompare) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
          hlim hfixed hcompare))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage
    FKToIsingAnalyticRGToExponentTarget in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (ofFreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonPositiveSubcriticalMass
      hagree hlim hfixed hcompare δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_freeQ2ProfileSeparateMass_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_freeQ2ProfileSeparateMass_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)



theorem closedBall_hasCriticalNu_from_freeQ2ProfileSeparateMass_components
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
            hlim hsameMass hcombine) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
          hlim hsameMass hcombine))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ProfileSeparatePositiveSubcriticalMass_components
      hagree hlim hsameMass hcombine δ hδ hδle
      fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_bridge_from_wiredQ2TwoSidedPositiveSubcriticalMass
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
          hbad hcmp hdecay)) :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_valid_from_wiredQ2TwoSidedPositiveSubcriticalMass
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
          hbad hcmp hdecay)) :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
          hbad hcmp hdecay))
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass
      hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_bridge_from_freeQ2ExactPositiveSubcritical_belowBetaC
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
          hcmp hdecay)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_valid_from_freeQ2ExactPositiveSubcritical_belowBetaC
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
          hcmp hdecay)) :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)



theorem closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC
    (hpred :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent =
          C.predictedExponent)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength
          (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
            hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLength
        (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
          hcmp hdecay))
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofFreeQ2ExactPositiveSubcritical_belowBetaC
        hagree hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_bridge_from_wiredQ2TwoSidedMass_belowBetaC
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
          hbad hcmp hdecay)) :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_valid_from_wiredQ2TwoSidedMass_belowBetaC
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
          hbad hcmp hdecay)) :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)




theorem
    tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedMass_belowBetaC
    (hpred :
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent = C.predictedExponent)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
            hbad hcmp hdecay) β =
            fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass
        (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
          hbad hcmp hdecay))
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    hpred
    (FKToIsingAnalyticRGToExponentTarget.ofWiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC
        hagree hbad hcmp hdecay δ hδ hδle fkCorrelationLength hfk hEq)

end PackageBoundaryExamples

end FKPositiveSubcriticalQ2AnalyticBridgeExample
end Exact3D
end StatMech
