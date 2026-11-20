/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKAnalyticBridgeTarget
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage










namespace StatMech
namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {n : ℕ}



theorem certificate_rgToExponentBridge_of_fkTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge



theorem certificate_valid_of_fkTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkTarget scale T)


theorem certificate_hasCriticalNu_of_fkTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge



theorem certificate_valid_of_fkPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkPowerLawTarget scale T)



theorem certificate_hasCriticalNu_of_fkPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget scale T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKMassAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge




theorem certificate_valid_of_fkMassTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKMassAnalyticRGToExponentTarget (P.certificate scale)) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassTarget scale T)



theorem certificate_hasCriticalNu_of_fkMassTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T : FKMassAnalyticRGToExponentTarget (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale)) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge




theorem certificate_valid_of_fkMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale)) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassPowerLawTarget scale T)



theorem certificate_hasCriticalNu_of_fkMassPowerLawTarget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget scale T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength (P.certificate scale).predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    hfk hEq




theorem certificate_valid_of_fk_pOfBeta_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength (P.certificate scale).predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    ((P.certificate scale).rgToExponentBridge_of_fk_pOfBeta_eventually_eq
      hfk hEq)




theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength (P.certificate scale).predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq scale hfk hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P.certificate scale) hpred hfk hEq



theorem certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      (P.certificate scale) hpred hfk hEq)




theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    scale hpred hfk hEq).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    hfk hEq



theorem certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    ((P.certificate scale).rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)




theorem certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    scale hfk hEq).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              (-(P.certificate scale).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref hscaling hEq




theorem certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              (-(P.certificate scale).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
      hpref_pos hlogpref hscaling hEq)



theorem certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              (-(P.certificate scale).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref hscaling hEq).hasCriticalNu




theorem
    certificate_rgBridge_of_fk_power_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref
    (fun p hp => by simpa [← hpred] using hscaling p hp)
    hEq




theorem
    certificate_valid_of_fk_power_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    (P.certificate_rgBridge_of_fk_power_Ioo_congr_exp
      scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ
      hpδ hpref_pos hlogpref hscaling hEq)




theorem
    certificate_hasNu_of_fk_power_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_power_Ioo_congr_exp
    scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ
    hpδ hpref_pos hlogpref hscaling hEq).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              ((P.certificate scale).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq




theorem certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              ((P.certificate scale).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pδ hpδ hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale)
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
              ((P.certificate scale).predictedExponent *
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
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq).hasCriticalNu




theorem
    certificate_rgBridge_of_fk_mass_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
    (P.certificate scale).RGToExponentBridge isingCorrelationLength :=
  (P.certificate scale).rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref
    (fun p hp => by simpa [← hpred] using hmass_scaling p hp)
    hfk_length_eq_inv_mass hEq




theorem
    certificate_valid_of_fk_mass_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
    (P.certificate scale).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale isingCorrelationLength
    (P.certificate_rgBridge_of_fk_mass_Ioo_congr_exp
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pδ hpδ hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)




theorem
    certificate_hasNu_of_fk_mass_Ioo_congr_exp
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex)
      Ising3DModel n)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
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
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_fk_mass_Ioo_congr_exp
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
