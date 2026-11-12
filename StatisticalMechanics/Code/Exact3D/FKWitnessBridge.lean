/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKAnalyticBridgeTarget
import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailTableWitnessPackage











namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {α : Type*} [DecidableEq α]



theorem rgToExponentBridge_of_fkTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkTarget T)


theorem hasCriticalNu_of_fkTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkPowerLawTarget T)


theorem hasCriticalNu_of_fkPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassTarget T)


theorem hasCriticalNu_of_fkMassTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassPowerLawTarget T)


theorem hasCriticalNu_of_fkMassPowerLawTarget
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget T).hasCriticalNu

theorem valid_of_fkTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge



theorem rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem hasCriticalNu_of_fkTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem
    rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    W.certificate hpred hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      W.certificate hpred hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    hpred hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    hfk hEq



theorem valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
      hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {α : Type*} [DecidableEq α]



theorem rgToExponentBridge_of_fkTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkTarget T)



theorem hasCriticalNu_of_fkTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkPowerLawTarget T)



theorem hasCriticalNu_of_fkPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassTarget T)


theorem hasCriticalNu_of_fkMassTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassPowerLawTarget T)



theorem hasCriticalNu_of_fkMassPowerLawTarget
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget T).hasCriticalNu

theorem valid_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge



theorem rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem hasCriticalNu_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget_congr_predictedExponent hpred T).hasCriticalNu




theorem rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget_congr_predictedExponent hpred T).hasCriticalNu




theorem
    rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    W.certificate hpred hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      W.certificate hpred hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    hpred hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    hfk hEq



theorem valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
      hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {Case α : Type*} [DecidableEq Case] [DecidableEq α]



theorem rgToExponentBridge_of_fkTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkTarget T)



theorem hasCriticalNu_of_fkTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkPowerLawTarget T)



theorem hasCriticalNu_of_fkPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassTarget T)


theorem hasCriticalNu_of_fkMassTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  T.rgToExponentBridge


theorem valid_of_fkMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge (W.rgToExponentBridge_of_fkMassPowerLawTarget T)



theorem hasCriticalNu_of_fkMassPowerLawTarget
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget T).hasCriticalNu

theorem valid_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge



theorem rgToExponentBridge_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem hasCriticalNu_of_fkTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkTarget_congr_predictedExponent hpred T).hasCriticalNu




theorem rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkPowerLawTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassTarget_congr_predictedExponent hpred T).hasCriticalNu



theorem
    rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.RGToExponentBridge T.isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    T.rgToExponentBridge hpred

theorem valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    W.certificate.Valid T.isingCorrelationLength :=
  W.valid_of_bridge_congr_predictedExponent hpred T.rgToExponentBridge

theorem hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fkMassPowerLawTarget_congr_predictedExponent
    hpred T).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength W.certificate.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    W.certificate hpred hfk hEq



theorem valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      W.certificate hpred hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    hpred hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    hfk hEq



theorem valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (W.certificate.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
      hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (-W.certificate.predictedExponent *
                Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
    (hEq :
      ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength beta =
          fkCorrelationLength (IsingFK.pOfBeta beta)) :
    HasCriticalNu Ising3DModel isingCorrelationLength
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta
    hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
      hpDelta hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta
    hpDelta hpref_pos hlogpref hscaling hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
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
              (W.certificate.predictedExponent *
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge isingCorrelationLength :=
  W.certificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
    hfk_length_eq_inv_mass hEq



theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid isingCorrelationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)



theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage
      (Case := Case) (α := α) Ising3DModel)
    {D : RGCertificate Ising3DModel}
    (isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor :
      ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
      W.certificate.predictedExponent :=
  (W.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred
    pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq).hasCriticalNu

end InfiniteTailTableWitnessPackage

end Exact3D
end StatMech
