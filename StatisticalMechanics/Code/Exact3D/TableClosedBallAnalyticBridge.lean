/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.AnalyticBridgeTarget
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage










namespace StatMech
namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {M : CriticalModel ι} {n : ℕ}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}



theorem certificate_rgToExponentBridge_of_analyticBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem certificate_valid_of_analyticBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticBridgeInputs scale h)



theorem certificate_hasCriticalNu_of_analyticBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs scale h).hasCriticalNu



theorem certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      scale hpred h)

theorem certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    scale hpred h).hasCriticalNu



theorem certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem certificate_valid_of_analyticPrefactorBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
      scale h)



theorem certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs scale h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem
    certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
      scale hpred h)

theorem
    certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    scale hpred h).hasCriticalNu



theorem certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem certificate_valid_of_analyticMassBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticMassBridgeInputs scale h)



theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs scale h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
      scale hpred h)

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    scale hpred h).hasCriticalNu

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
