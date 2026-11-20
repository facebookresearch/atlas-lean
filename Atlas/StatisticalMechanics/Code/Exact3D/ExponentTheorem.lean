/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.Certificate
import Code.Exact3D.Ising3D
import Code.Exact3D.IsingRGCoordinateBridge
import Code.Exact3D.FKAnalyticBridgeTarget











namespace StatMech
namespace Exact3D


theorem hasCriticalNu_eq_log_scale_div_log_thermal {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hC : C.Valid correlationLength) :
    HasCriticalNu M correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using hC.hasCriticalNu



theorem hasCriticalNu_from_rgToExponentBridge {ι : Type*}
    {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hbridge : C.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.RGToExponentBridge, RGCertificate.predictedExponent,
    predictedNu] using hbridge


theorem placeholder_hasCriticalNu_exact
    (C : RGCertificate PlaceholderModel) (correlationLength : ℝ → ℝ)
    (hC : C.Valid correlationLength) :
    HasCriticalNu PlaceholderModel correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact hasCriticalNu_eq_log_scale_div_log_thermal C correlationLength hC



theorem ising3D_hasCriticalNu_exact
    (C : RGCertificate Ising3DModel) (correlationLength : ℝ → ℝ)
    (hC : C.Valid correlationLength) :
    HasCriticalNu Ising3DModel correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact hasCriticalNu_eq_log_scale_div_log_thermal C correlationLength hC


theorem hasCriticalNu_from_analyticBridgeInputs
    {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (T :
      RGCertificate.AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem hasCriticalNu_from_analyticBridgeInputs_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι}
    {C D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T :
      RGCertificate.AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem hasCriticalNu_from_analyticPrefactorBridgeInputs
    {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength prefactor : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (T :
      RGCertificate.AnalyticPrefactorBridgeInputs C correlationLength
        prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem hasCriticalNu_from_analyticPrefactorBridgeInputs_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι}
    {C D : RGCertificate M} (correlationLength prefactor : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T :
      RGCertificate.AnalyticPrefactorBridgeInputs C correlationLength
        prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred


theorem hasCriticalNu_from_analyticMassBridgeInputs
    {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M)
    (correlationLength mass massPrefactor : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (T :
      RGCertificate.AnalyticMassBridgeInputs C correlationLength mass
        massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem hasCriticalNu_from_analyticMassBridgeInputs_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι}
    {C D : RGCertificate M}
    (correlationLength mass massPrefactor : ℝ → ℝ)
    {RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T :
      RGCertificate.AnalyticMassBridgeInputs C correlationLength mass
        massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem ising3D_hasCriticalNu_from_isingAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu




theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_isingAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_isingMassAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_isingMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_isingMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_freeAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_freeAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_freeMassAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassAnalyticTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    (C : RGCertificate Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_hasCriticalNu_from_isingAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_hasCriticalNu_from_isingMassAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_hasCriticalNu_from_isingMassPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem ising3D_hasCriticalNu_from_freeAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_hasCriticalNu_from_freeMassAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_hasCriticalNu_from_freeMassPowerLawToPlusTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_liminf_from_isingAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_isingMassAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_isingMassPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_freeAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_freeMassAnalyticTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_freeMassPowerLawToPlusTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_coordinateBridge
    (C : RGCertificate Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_coordinateBridge
    (C : RGCertificate Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.toIsingAnalyticTarget.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_massCoordinateBridge
    (C : RGCertificate Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_massCoordinateBridge
    (C : RGCertificate Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.toIsingMassPowerLawTarget.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_coordinateBridge_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem ising3D_hasCriticalNu_from_massCoordinateBridge_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_liminf_from_coordinateBridge_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.toIsingAnalyticTarget.congr_predictedExponent
      hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_massCoordinateBridge_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.toIsingMassPowerLawTarget.congr_predictedExponent
      hpred).hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_fkTarget
    (C : RGCertificate Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu




theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_fkTarget
    (C : RGCertificate Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_pOfBeta_eventually_eq hfk hEq



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq C hfk hEq



theorem ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      hpred hfk hEq



theorem ising3D_liminf_from_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_pOfBeta_eventually_eq_congr_predictedExponent
      C hpred hfk hEq



theorem ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge
    (C : RGCertificate Ising3DModel)
    {fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge C hfk hEq



theorem
    ising3D_rgToExponentBridge_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength := by
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
      hpred hfk hEq



theorem
    ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    hasCriticalNu_from_rgToExponentBridge C isingCorrelationLength
      (ising3D_rgToExponentBridge_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent
        C hpred hfk hEq)



theorem
    ising3D_liminf_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      (D.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_pOfBeta_rgToExponentBridge_congr_predictedExponent
      C hpred hfk hEq



theorem ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
      hpref_pos hlogpref hscaling hEq



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo
      C
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

set_option linter.style.longLine false in



theorem
    ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ
      hpref_pos hlogpref hscaling hEq

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hscaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_hasCriticalNu_from_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    C
    (fun β : ℝ =>
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay)
    fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref
    hscaling hEq



theorem ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo
    (C : RGCertificate Ising3DModel)
    (fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (C.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  exact
    ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo
      C
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref
      hmass_scaling hfk_length_eq_inv_mass hEq

set_option linter.style.longLine false in



theorem
    ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    C.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pδ hpδ hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq

set_option linter.style.longLine false in



theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        0 < fkMassPrefactor p)
    (hlogpref :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (fkMassPrefactor p) /
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
        (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
          (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
    (hmass_scaling :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_hasCriticalNu_from_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    C
    (fun β : ℝ =>
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay)
    fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos
    hlogpref hmass_scaling hfk_length_eq_inv_mass hEq



theorem ising3D_hasCriticalNu_from_fkPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_fkPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_fkMassTarget
    (C : RGCertificate Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassTarget
    (C : RGCertificate Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_fkMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using T.hasCriticalNu



theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_fkMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_liminfCorrelationLength



theorem ising3D_hasCriticalNu_from_fkTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred


theorem ising3D_hasCriticalNu_from_fkPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred


theorem ising3D_hasCriticalNu_from_fkMassTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred


theorem ising3D_hasCriticalNu_from_fkMassPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    T.hasCriticalNu_congr_predictedExponent hpred



theorem
    ising3D_liminf_from_fkTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_fkPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_fkMassTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength



theorem
    ising3D_liminf_from_fkMassPowerLawTarget_congr_predictedExponent
    {C D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log D.scale.toReal / Real.log D.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    (T.congr_predictedExponent hpred).hasCriticalNu_liminfCorrelationLength

end Exact3D
end StatMech
