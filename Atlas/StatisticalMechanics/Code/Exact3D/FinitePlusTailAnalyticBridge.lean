/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.AnalyticBridgeTarget
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG










namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type} {ι : Type*}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}

theorem certificate_rgToExponentBridge_of_analyticBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (H.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (H.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (H.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_analyticBridgeInputs scale M
    (RGCertificate.AnalyticBridgeInputs.congr_predictedExponent
      (C := D) (D := H.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticPrefactorBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticPrefactorBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_analyticPrefactorBridgeInputs scale M
    (RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent
      (C := D) (D := H.certificate scale M) hpred h)

theorem
    certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticMassBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticMassBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_analyticMassBridgeInputs scale M
    (RGCertificate.AnalyticMassBridgeInputs.congr_predictedExponent
      (C := D) (D := H.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type} {ι : Type*}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}

theorem certificate_rgToExponentBridge_of_analyticBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticBridgeInputs scale M
    (RGCertificate.AnalyticBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticPrefactorBridgeInputs scale M
    (RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem
    certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticMassBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticMassBridgeInputs scale M
    (RGCertificate.AnalyticMassBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type} {ι : Type*}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}

theorem certificate_rgToExponentBridge_of_analyticBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs (P.certificate scale M)
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticBridgeInputs scale M
    (RGCertificate.AnalyticBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M)
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticPrefactorBridgeInputs scale M
    (RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem
    certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

theorem certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  h.rgToExponentBridge

theorem certificate_valid_of_analyticMassBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength h.rgToExponentBridge

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M)
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs scale M h).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_analyticMassBridgeInputs scale M
    (RGCertificate.AnalyticMassBridgeInputs.congr_predictedExponent
      (C := D) (D := P.certificate scale M) hpred h)

theorem certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    scale M hpred h).hasCriticalNu

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
