/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKAnalyticBridgeTarget
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG









namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_fkTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fkTarget scale T)

theorem certificate_hasCriticalNu_of_fkTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fkPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fkMassTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkMassTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fkMassPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassPowerLawTarget
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (H.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkMassPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkMassTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  H.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (H.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (H.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    ((H.certificate scale Ising3DModel).rgToExponentBridge_of_fk_pOfBeta_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (H.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_pOfBeta_eventually_eq scale hfk hEq).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact
    RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      C hpred hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      (H.certificate scale Ising3DModel) hpred hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    scale hpred hfk hEq).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((H.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq

theorem certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((H.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((H.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    scale hfk hEq).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq

theorem certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)

theorem certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq

theorem
    certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
      pDelta hpDelta hpref_pos hlogpref hscaling hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq

theorem certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((H.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := H.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq

theorem
    certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (H.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  H.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (H.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (H.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (H.certificate scale Ising3DModel).predictedExponent :=
  (H.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_fkTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkTarget scale T)

theorem certificate_hasCriticalNu_of_fkTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassPowerLawTarget
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    ((P.certificate scale Ising3DModel).rgToExponentBridge_of_fk_pOfBeta_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq scale hfk hEq).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      C hpred hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      (P.certificate scale Ising3DModel) hpred hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    scale hpred hfk hEq).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq

theorem certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    scale hfk hEq).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq

theorem certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)

theorem certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq

theorem
    certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
      pDelta hpDelta hpref_pos hlogpref hscaling hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq

theorem certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq

theorem
    certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}



theorem certificate_rgToExponentBridge_of_fkTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkTarget scale T)

theorem certificate_hasCriticalNu_of_fkTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  T.rgToExponentBridge

theorem certificate_valid_of_fkMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel
    T.isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fkMassPowerLawTarget scale T)

theorem certificate_hasCriticalNu_of_fkMassPowerLawTarget
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (T :
      FKMassPowerLawToIsingAnalyticRGToExponentTarget
        (P.certificate scale Ising3DModel)) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget scale T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength :=
  P.certificate_valid_of_bridge_congr_predictedExponent
    scale Ising3DModel hpred T.rgToExponentBridge

theorem
    certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α) (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    scale hpred T).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    ((P.certificate scale Ising3DModel).rgToExponentBridge_of_fk_pOfBeta_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength
        (P.certificate scale Ising3DModel).predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq scale hfk hEq).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      C hpred hfk hEq

theorem certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      (P.certificate scale Ising3DModel) hpred hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    scale hpred hfk hEq).hasCriticalNu

theorem certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq

theorem certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)

theorem certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      ((P.certificate scale Ising3DModel).retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    scale hfk hEq).hasCriticalNu



theorem certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq

theorem certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)

theorem certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-(P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq

theorem
    certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
      pDelta hpDelta hpref_pos hlogpref hscaling hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p =
          fkPrefactor p *
            Real.exp
              (-D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu




theorem certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq

theorem certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              ((P.certificate scale Ising3DModel).predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu




theorem
    certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).RGToExponentBridge
      isingCorrelationLength := by
  let C := P.certificate scale Ising3DModel
  exact
    C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq

theorem
    certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    (P.certificate scale Ising3DModel).Valid isingCorrelationLength :=
  P.certificate_valid_of_bridge scale Ising3DModel isingCorrelationLength
    (P.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)

theorem
    certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred :
      (P.certificate scale Ising3DModel).predictedExponent =
        D.predictedExponent)
    (pDelta : ℝ) (hpDelta : 0 < pDelta)
    (hpref_pos :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
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
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkMass p =
          fkMassPrefactor p *
            Real.exp
              (D.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hfk_length_eq_inv_mass :
      ∀ p, p ∈ Set.Ioo
          (IsingFK.pOfBeta (Ising.betaC 3) - pDelta)
          (IsingFK.pOfBeta (Ising.betaC 3)) →
        fkCorrelationLength p = (fkMass p)⁻¹)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      (P.certificate scale Ising3DModel).predictedExponent :=
  (P.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq).hasCriticalNu

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
