/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.AnalyticBridgeTarget
import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailTableWitnessPackage









namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}



theorem rgToExponentBridge_of_analyticBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticBridgeInputs h)



theorem hasCriticalNu_of_analyticBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs h).hasCriticalNu



theorem rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs_congr_predictedExponent hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticPrefactorBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs h)



theorem hasCriticalNu_of_analyticPrefactorBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs h).hasCriticalNu

theorem
    rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticMassBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticMassBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticMassBridgeInputs h)



theorem hasCriticalNu_of_analyticMassBridgeInputs
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs h).hasCriticalNu

theorem rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}



theorem rgToExponentBridge_of_analyticBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticBridgeInputs h)



theorem hasCriticalNu_of_analyticBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs h).hasCriticalNu

theorem rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs_congr_predictedExponent hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs h)



theorem hasCriticalNu_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs h).hasCriticalNu

theorem
    rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticMassBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticMassBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticMassBridgeInputs h)



theorem hasCriticalNu_of_analyticMassBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs h).hasCriticalNu

theorem rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]
variable {M : CriticalModel ι}
variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}



theorem rgToExponentBridge_of_analyticBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticBridgeInputs h)



theorem hasCriticalNu_of_analyticBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticBridgeInputs W.certificate
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs h).hasCriticalNu

theorem rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticBridgeInputs D
        correlationLength RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticBridgeInputs_congr_predictedExponent hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs h)



theorem hasCriticalNu_of_analyticPrefactorBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength prefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs W.certificate
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs h).hasCriticalNu

theorem
    rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength prefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticPrefactorBridgeInputs D
        correlationLength prefactor RGCovariance StableManifoldControl
        MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu



theorem rgToExponentBridge_of_analyticMassBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  h.rgToExponentBridge



theorem valid_of_analyticMassBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_analyticMassBridgeInputs h)



theorem hasCriticalNu_of_analyticMassBridgeInputs
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (h :
      RGCertificate.AnalyticMassBridgeInputs W.certificate
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs h).hasCriticalNu

theorem rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    h.rgToExponentBridge hpred

theorem valid_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
      hpred h)

theorem hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength mass massPrefactor : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (h :
      RGCertificate.AnalyticMassBridgeInputs D
        correlationLength mass massPrefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_analyticMassBridgeInputs_congr_predictedExponent
    hpred h).hasCriticalNu

end InfiniteTailTableWitnessPackage

end Exact3D
end StatMech
