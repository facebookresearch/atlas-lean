/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingRGCoordinateBridge
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage










namespace StatMech
namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {n : ℕ}



theorem certificate_rgToExponentBridge_of_isingAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_isingMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  T.rgToExponentBridge



theorem
    certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred



theorem
    certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_isingAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingAnalyticRGToExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassAnalyticTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_isingMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget
      (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget scale T).hasCriticalNu

theorem certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_freeMassAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget scale T).hasCriticalNu

theorem certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_valid_of_freeMassPowerLawToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale)) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge scale
    T.correlationLength T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget scale T).hasCriticalNu

theorem
    certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.correlationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs (P.certificate scale)) :
    (P.certificate scale).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget
    scale T.toIsingAnalyticTarget

theorem certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingRGCoordinateBridgeInputs (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs scale T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_isingMassRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)) :
    (P.certificate scale).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget
    scale T.toIsingMassPowerLawTarget

theorem certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs
    scale T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    (P.certificate scale).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    scale hpred T.toIsingAnalyticTarget

theorem
    certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale).RGToExponentBridge
      T.scaffold.correlationLength :=
  T.rgToExponentBridge_congr_predictedExponent hpred

theorem
    certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    (P.certificate scale).Valid T.scaffold.correlationLength :=
  P.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    scale hpred T.toIsingMassPowerLawTarget

theorem
    certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs D) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    scale hpred T).hasCriticalNu

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
