/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingRGCoordinateBridge
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG










namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_isingAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_isingAnalyticTarget scale T)

theorem certificate_hasCriticalNu_of_isingAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingAnalyticTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_isingMassAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_isingMassAnalyticTarget scale T)

theorem certificate_hasCriticalNu_of_isingMassAnalyticTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassAnalyticTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_isingMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_isingMassPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_isingMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_freeAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget scale T)

theorem certificate_hasCriticalNu_of_freeAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeAnalyticToPlusTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_freeMassAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget scale T)

theorem certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeMassAnalyticToPlusTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_freeMassPowerLawToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength
    (H.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget scale T)

theorem certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeMassPowerLawToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem
    certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem
    certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.correlationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  H.certificate_valid_of_isingAnalyticTarget
    scale T.toIsingAnalyticTarget

theorem certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingRGCoordinateBridgeInputs scale T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  H.certificate_valid_of_isingMassPowerLawTarget
    scale T.toIsingMassPowerLawTarget

theorem certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassRGCoordinateBridgeInputs
    scale T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  H.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T.toIsingAnalyticTarget

theorem
    certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  H.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T.toIsingMassPowerLawTarget

theorem
    certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_isingAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem
    certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_isingAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassAnalyticTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget
    scale T.toIsingAnalyticTarget

theorem certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs scale T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget
    scale T.toIsingMassPowerLawTarget

theorem certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs
    scale T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T.toIsingAnalyticTarget

theorem
    certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T.toIsingMassPowerLawTarget

theorem
    certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_isingAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  T.rgToExponentBridge



theorem
    certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_isingAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassAnalyticTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget
    scale T.toIsingAnalyticTarget

theorem certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs scale T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget
    scale T.toIsingMassPowerLawTarget

theorem certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs
      (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs
    scale T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T.toIsingAnalyticTarget

theorem
    certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T.toIsingMassPowerLawTarget

theorem
    certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
