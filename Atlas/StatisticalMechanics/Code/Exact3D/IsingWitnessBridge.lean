/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingRGCoordinateBridge
import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailTableWitnessPackage










namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {α : Type*} [DecidableEq α]



theorem rgToExponentBridge_of_isingAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_isingAnalyticTarget T)

theorem hasCriticalNu_of_isingAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget T).hasCriticalNu




theorem rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_isingMassAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingMassAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_isingMassAnalyticTarget T)

theorem hasCriticalNu_of_isingMassAnalyticTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget T).hasCriticalNu



theorem rgToExponentBridge_of_isingMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_isingMassPowerLawTarget T)

theorem hasCriticalNu_of_isingMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget T).hasCriticalNu



theorem rgToExponentBridge_of_freeAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_freeAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_freeAnalyticToPlusTarget T)

theorem hasCriticalNu_of_freeAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget T).hasCriticalNu



theorem rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_freeMassAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_freeMassAnalyticToPlusTarget T)

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget T).hasCriticalNu



theorem rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_freeMassPowerLawToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_freeMassPowerLawToPlusTarget T)

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget T).hasCriticalNu

theorem valid_of_isingAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget_congr_predictedExponent hpred T).hasCriticalNu




theorem rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget_congr_predictedExponent
    hpred T).hasCriticalNu




theorem rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu




theorem rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu




theorem
    rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu




theorem
    rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs T).hasCriticalNu



theorem rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingMassRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs T).hasCriticalNu



theorem
    rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu




theorem
    rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem
    hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {α : Type*} [DecidableEq α]



theorem rgToExponentBridge_of_isingAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingMassAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_isingAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget T).hasCriticalNu

theorem valid_of_isingMassAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassAnalyticTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget T).hasCriticalNu

theorem valid_of_isingMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget T).hasCriticalNu

theorem valid_of_freeAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget T).hasCriticalNu

theorem valid_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget T).hasCriticalNu

theorem valid_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget T).hasCriticalNu

theorem valid_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget_congr_predictedExponent hpred T).hasCriticalNu

theorem valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs T).hasCriticalNu



theorem rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs T).hasCriticalNu



theorem
    rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu



theorem
    rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem
    hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {Case α : Type*} [DecidableEq Case] [DecidableEq α]



theorem rgToExponentBridge_of_isingAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingMassAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_isingAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget T).hasCriticalNu

theorem valid_of_isingMassAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassAnalyticTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget T).hasCriticalNu

theorem valid_of_isingMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget T).hasCriticalNu

theorem valid_of_freeAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget T).hasCriticalNu

theorem valid_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassAnalyticRGToPlusExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget T).hasCriticalNu

theorem valid_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget T).hasCriticalNu

theorem valid_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingAnalyticTarget_congr_predictedExponent hpred T).hasCriticalNu

theorem valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassAnalyticTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu

theorem valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.correlationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs T).hasCriticalNu



theorem rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem valid_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs T)

theorem hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : IsingMassRGCoordinateBridgeInputs W.certificate) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs T).hasCriticalNu



theorem
    rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu



theorem
    rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.RGToExponentBridge T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    W.certificate.Valid T.scaffold.correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
      hpred T)

theorem
    hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      W.certificate.predictedExponent :=
  (W.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    hpred T).hasCriticalNu

end InfiniteTailTableWitnessPackage

end Exact3D
end StatMech
