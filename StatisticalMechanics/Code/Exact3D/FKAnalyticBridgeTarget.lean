/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKReparameterization
import Code.Exact3D.IsingBridgeTargets














namespace StatMech
namespace Exact3D



theorem eventually_mem_fkBetaLeftCriticalIoo {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - δ < Ising.betaC 3 by
      linarith)] with β hβ
  exact hβ


theorem betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < δ := by
  linarith [hβ.1]



theorem beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC
    {δ β : ℝ} (hδle : δ ≤ Ising.betaC 3)
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < β := by
  have hnonneg : 0 ≤ Ising.betaC 3 - δ := sub_nonneg.mpr hδle
  linarith [hβ.1, hnonneg]


theorem eventually_betaC_sub_pos_fkBetaLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [eventually_mem_fkBetaLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ



theorem eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < δ := by
  filter_upwards [eventually_mem_fkBetaLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ



theorem eventually_mem_fkPLeftCriticalIoo {pδ : ℝ} (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) := by
  filter_upwards
    [Ioo_mem_nhdsLT
      (show IsingFK.pOfBeta (Ising.betaC 3) - pδ <
          IsingFK.pOfBeta (Ising.betaC 3) by
        linarith)] with p hp
  exact hp

set_option linter.style.longLine false in

theorem eventually_pOfBeta_mem_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  FKReparameterization.eventually_pOfBeta_mem_Ioo_left
    (βc := Ising.betaC 3) hpδ


theorem pCritical_sub_pos_of_mem_fkPLeftCriticalIoo
    {pδ p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  sub_pos.mpr hp.2


theorem pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo
    {pδ p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
  linarith [hp.1]


theorem eventually_pCritical_sub_pos_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
  filter_upwards [eventually_mem_fkPLeftCriticalIoo hpδ] with p hp
  exact pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp



theorem eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo {pδ : ℝ}
    (hpδ : 0 < pδ) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
  filter_upwards [eventually_mem_fkPLeftCriticalIoo hpδ] with p hp
  exact pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp



theorem hasCriticalNu_comp_pOfBeta_congr_eventually
    {βc ν : ℝ} {fkCorrelationLength comparisonLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        fkCorrelationLength ν)
    (hEq :
      ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
        comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu (ParameterModel βc) comparisonLength ν :=
  FKReparameterization.hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq

namespace RGCertificate




theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_hasCriticalNu isingCorrelationLength
    ((hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq).congr_betaC (by rfl))



theorem rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (by simpa [RGToExponentBridge] using hfk) hEq



theorem
    rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
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
  have hfkC :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength :=
    RGCertificate.rgToExponentBridge_congr_predictedExponent hfk (by
      simpa using hpred)
  exact
    C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfkC hEq




theorem valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
      hfk hEq)



theorem
    valid_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
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
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
      hpred hfk hEq)



theorem valid_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq



theorem rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
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
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq
    (by simpa [hpred] using hfk) hEq



theorem valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (C : RGCertificate Ising3DModel)
    {D : RGCertificate Ising3DModel}
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength D.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
      hpred hfk hEq)



theorem hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    hpred hfk hEq




theorem hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq
    (C : RGCertificate Ising3DModel)
    {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
    (hfk :
      (C.retarget
        (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge
        fkCorrelationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq hfk hEq



theorem
    hasCriticalNu_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent
    hpred hfk hEq



theorem rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
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
    C.RGToExponentBridge isingCorrelationLength := by
  have hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent := by
    refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength fkPrefactor C.predictedExponent pδ hpδ ?_ ?_ ?_
    · intro p hp
      exact hpref_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using hlogpref
    · intro p hp
      exact hscaling p (by simpa [ParameterModel] using hp)
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq



theorem valid_of_fk_exact_power_variable_prefactor_on_Ioo
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
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
      hpref_pos hlogpref hscaling hEq)



theorem hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref hscaling hEq



theorem
    rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ
    hpref_pos hlogpref
    (fun p hp => by simpa [hpred] using hscaling p hp)
    hEq



theorem
    valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ
      hpref_pos hlogpref hscaling hEq)



theorem
    hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ
    hpref_pos hlogpref hscaling hEq



theorem rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
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
    C.RGToExponentBridge isingCorrelationLength := by
  have hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent := by
    refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength fkMass fkMassPrefactor C.predictedExponent
      pδ hpδ ?_ ?_ ?_ ?_
    · intro p hp
      exact hpref_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using hlogpref
    · intro p hp
      exact hmass_scaling p (by simpa [ParameterModel] using hp)
    · intro p hp
      exact hfk_length_eq_inv_mass p (by simpa [ParameterModel] using hp)
  exact C.rgToExponentBridge_of_fk_pOfBeta_eventually_eq hfk hEq




theorem valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo
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
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq)




theorem hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq



theorem
    rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
    C.RGToExponentBridge isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    pδ hpδ hpref_pos hlogpref
    (fun p hp => by simpa [hpred] using hmass_scaling p hp)
    hfk_length_eq_inv_mass hEq



theorem
    valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
        isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid isingCorrelationLength :=
  C.valid_of_bridge isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
      hpred pδ hpδ hpref_pos hlogpref hmass_scaling
      hfk_length_eq_inv_mass hEq)




theorem
    hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
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
    HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor
    hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass
    hEq

end RGCertificate







structure FKToIsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  δ : ℝ
  δ_pos : 0 < δ
  
  isingCorrelationLength : ℝ → ℝ
  
  fkCorrelationLength : ℝ → ℝ
  
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  
  fk_hasCriticalNu :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength C.predictedExponent
  

  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

namespace FKToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ



theorem eventually_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.δ_pos



theorem eventually_hasCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_ising_fk_length_agree
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree



theorem hasCriticalNu_comp_pOfBeta
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (Ising.betaC 3))
      (fun β => T.fkCorrelationLength (IsingFK.pOfBeta β))
      C.predictedExponent :=
  FKReparameterization.hasCriticalNu_comp_pOfBeta T.fk_hasCriticalNu


theorem hasCriticalNu
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent := by
  have hcomp_param := T.hasCriticalNu_comp_pOfBeta
  have hcomp_ising :
      HasCriticalNu Ising3DModel
        (fun β => T.fkCorrelationLength (IsingFK.pOfBeta β))
        C.predictedExponent :=
    hcomp_param.congr_betaC (by rfl)
  exact hcomp_ising.congr_eventually T.ising_fk_length_agree


theorem rgToExponentBridge
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  C.rgToExponentBridge_of_hasCriticalNu T.isingCorrelationLength
    T.hasCriticalNu



theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [T.eventually_hasCorrelationLength] with β hβ
  exact hβ.liminfCorrelationLength_eq.symm



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  RGCertificate.rgToExponentBridge_congr_eventually
    T.rgToExponentBridge
    ((T.eventually_isingCorrelationLength_eq_liminfCorrelationLength).mono
      fun _ hβ => hβ.symm)



theorem hasCriticalNu_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.rgToExponentBridge_liminfCorrelationLength



theorem valid_of_checks
    (T : FKToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := T.rgToExponentBridge




theorem valid_of_checks_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  C.valid_of_bridge
    (fun β : ℝ =>
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay)
    hfinite htail hfixed hlinear hhyperbolic horbit
    T.rgToExponentBridge_liminfCorrelationLength



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fk_hasCriticalNu := by
    simpa [hpred] using T.fk_hasCriticalNu
  ising_fk_length_agree := T.ising_fk_length_agree



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength := freeSelectedSubcriticalCorrelationLengthFromMass hmass
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
      hagree hmass hβ.2
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength :=
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ.2
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
        hmass
        (beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC hδle hβ)
        hβ.2)
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq



noncomputable def ofFreePositiveCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreePositiveSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength hbridge β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength := freeSelectedPositiveSubcriticalCorrelationLength hbridge
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
      hagree hbridge
      (beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq

end FKToIsingAnalyticRGToExponentTarget



structure FKPowerLawToIsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  betaδ : ℝ
  betaδ_pos : 0 < betaδ
  
  pδ : ℝ
  pδ_pos : 0 < pδ
  isingCorrelationLength : ℝ → ℝ
  fkCorrelationLength : ℝ → ℝ
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - betaδ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  fkPrefactor : ℝ → ℝ
  fkPrefactor_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkPrefactor p
  fkPrefactor_log_negligible :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkPrefactor p) /
          Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
      (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0)
  fk_length_scaling :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p =
        fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
              Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

namespace FKPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ



theorem eventually_mem_betaLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_mem_pLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_mem_fkPLeftCriticalIoo T.pδ_pos

set_option linter.style.longLine false in


theorem eventually_pOfBeta_mem_pLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_pOfBeta_mem_fkPLeftCriticalIoo T.pδ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.betaδ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem pCritical_sub_pos_of_mem_pLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp


theorem pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp


theorem eventually_betaC_sub_pos
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.betaδ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_pCritical_sub_pos
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  eventually_pCritical_sub_pos_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_pCritical_sub_lt_delta
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_hasCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_fkPrefactor_pos
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkPrefactor p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkPrefactor_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkPrefactor_pos_comp_pOfBeta
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkPrefactor (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkPrefactor_pos (IsingFK.pOfBeta β) hp



theorem eventually_fk_length_scaling
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p =
        T.fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_scaling p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_scaling_comp_pOfBeta
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        T.fkPrefactor (IsingFK.pOfBeta β) *
          Real.exp
            (-C.predictedExponent *
              Real.log
                (IsingFK.pOfBeta (Ising.betaC 3) -
                  IsingFK.pOfBeta β)) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_scaling (IsingFK.pOfBeta β) hp



theorem eventually_ising_fk_length_agree
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree


theorem fk_hasCriticalNu
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      T.fkCorrelationLength C.predictedExponent := by
  refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
    T.fkCorrelationLength T.fkPrefactor C.predictedExponent
    T.pδ T.pδ_pos ?_ ?_ ?_
  · intro p hp
    exact T.fkPrefactor_pos p (by simpa [ParameterModel] using hp)
  · simpa [ParameterModel] using T.fkPrefactor_log_negligible
  · intro p hp
    exact T.fk_length_scaling p (by simpa [ParameterModel] using hp)


def toFKTarget
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := T.betaδ
  δ_pos := T.betaδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fk_hasCriticalNu := T.fk_hasCriticalNu
  ising_fk_length_agree := T.ising_fk_length_agree

@[simp] theorem toFKTarget_isingCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKTarget.isingCorrelationLength = T.isingCorrelationLength :=
  rfl


theorem hasCriticalNu
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu



theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toFKTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  T.toFKTarget.rgToExponentBridge



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  T.toFKTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKPowerLawToIsingAnalyticRGToExponentTarget D where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fkPrefactor := T.fkPrefactor
  fkPrefactor_pos := T.fkPrefactor_pos
  fkPrefactor_log_negligible := T.fkPrefactor_log_negligible
  fk_length_scaling := by
    intro p hp
    simpa [hpred] using T.fk_length_scaling p hp
  ising_fk_length_agree := T.ising_fk_length_agree



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit



@[simp] theorem congr_predictedExponent_toFKTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKTarget =
      FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKTarget := by
  rfl

end FKPowerLawToIsingAnalyticRGToExponentTarget





structure FKMassAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  betaδ : ℝ
  betaδ_pos : 0 < betaδ
  
  pδ : ℝ
  pδ_pos : 0 < pδ
  isingCorrelationLength : ℝ → ℝ
  fkCorrelationLength : ℝ → ℝ
  fkMass : ℝ → ℝ
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - betaδ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkMass p
  fk_length_eq_inv_mass :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p = (fkMass p)⁻¹
  fkPrefactor : ℝ → ℝ
  fkPrefactor_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkPrefactor p
  fkPrefactor_log_negligible :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkPrefactor p) /
          Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
      (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0)
  fk_length_scaling :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p =
        fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
              Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

namespace FKMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ



theorem eventually_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_mem_fkPLeftCriticalIoo T.pδ_pos

set_option linter.style.longLine false in


theorem eventually_pOfBeta_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_pOfBeta_mem_fkPLeftCriticalIoo T.pδ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.betaδ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem pCritical_sub_pos_of_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp


theorem pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval
    (T : FKMassAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp


theorem eventually_betaC_sub_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.betaδ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_pCritical_sub_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  eventually_pCritical_sub_pos_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_pCritical_sub_lt_delta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_hasCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_fkMass_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkMass p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkMass_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkMass_pos_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkMass (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkMass_pos (IsingFK.pOfBeta β) hp



theorem eventually_fk_length_eq_inv_mass
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p = (T.fkMass p)⁻¹ := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_eq_inv_mass p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_eq_inv_mass_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_eq_inv_mass (IsingFK.pOfBeta β) hp



theorem eventually_fkPrefactor_pos
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkPrefactor p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkPrefactor_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkPrefactor_pos_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkPrefactor (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkPrefactor_pos (IsingFK.pOfBeta β) hp



theorem eventually_fk_length_scaling
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p =
        T.fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_scaling p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_scaling_comp_pOfBeta
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        T.fkPrefactor (IsingFK.pOfBeta β) *
          Real.exp
            (-C.predictedExponent *
              Real.log
                (IsingFK.pOfBeta (Ising.betaC 3) -
                  IsingFK.pOfBeta β)) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_scaling (IsingFK.pOfBeta β) hp



theorem eventually_ising_fk_length_agree
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree


theorem fk_hasCriticalNu
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      T.fkCorrelationLength C.predictedExponent := by
  refine _root_.StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
    T.fkCorrelationLength T.fkPrefactor C.predictedExponent
    T.pδ T.pδ_pos ?_ ?_ ?_
  · intro p hp
    exact T.fkPrefactor_pos p (by simpa [ParameterModel] using hp)
  · simpa [ParameterModel] using T.fkPrefactor_log_negligible
  · intro p hp
    exact T.fk_length_scaling p (by simpa [ParameterModel] using hp)


def toFKPowerLawTarget
    (T : FKMassAnalyticRGToExponentTarget C) :
    FKPowerLawToIsingAnalyticRGToExponentTarget C where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fkPrefactor := T.fkPrefactor
  fkPrefactor_pos := T.fkPrefactor_pos
  fkPrefactor_log_negligible := T.fkPrefactor_log_negligible
  fk_length_scaling := T.fk_length_scaling
  ising_fk_length_agree := T.ising_fk_length_agree


def toFKTarget
    (T : FKMassAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget C :=
  T.toFKPowerLawTarget.toFKTarget



@[simp] theorem toFKPowerLawTarget_toFKTarget
    (T : FKMassAnalyticRGToExponentTarget C) :
    T.toFKPowerLawTarget.toFKTarget = T.toFKTarget := by
  rfl


theorem hasCriticalNu
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu



theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toFKTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge
    (T : FKMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  T.toFKTarget.rgToExponentBridge



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FKMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  T.toFKTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : FKMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    FKMassAnalyticRGToExponentTarget D where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMass_pos := T.fkMass_pos
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  fkPrefactor := T.fkPrefactor
  fkPrefactor_pos := T.fkPrefactor_pos
  fkPrefactor_log_negligible := T.fkPrefactor_log_negligible
  fk_length_scaling := by
    intro p hp
    simpa [hpred] using T.fk_length_scaling p hp
  ising_fk_length_agree := T.ising_fk_length_agree



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit



@[simp] theorem congr_predictedExponent_toFKPowerLawTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKPowerLawTarget =
      FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKPowerLawTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toFKTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKTarget =
      FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKTarget := by
  rfl

end FKMassAnalyticRGToExponentTarget




structure FKMassPowerLawToIsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  betaδ : ℝ
  betaδ_pos : 0 < betaδ
  
  pδ : ℝ
  pδ_pos : 0 < pδ
  isingCorrelationLength : ℝ → ℝ
  fkCorrelationLength : ℝ → ℝ
  fkMass : ℝ → ℝ
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - betaδ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  fkMassPrefactor : ℝ → ℝ
  fkMassPrefactor_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkMassPrefactor p
  fkMassPrefactor_log_negligible :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkMassPrefactor p) /
          Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
      (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0)
  fk_mass_scaling :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkMass p =
        fkMassPrefactor p *
          Real.exp
            (C.predictedExponent *
              Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
  fk_length_eq_inv_mass :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p = (fkMass p)⁻¹
  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ



theorem fkMass_pos
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < T.fkMass p := by
  rw [T.fk_mass_scaling p hp]
  exact mul_pos (T.fkMassPrefactor_pos p hp) (Real.exp_pos _)



theorem eventually_mem_betaLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_mem_pLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_mem_fkPLeftCriticalIoo T.pδ_pos

set_option linter.style.longLine false in


theorem eventually_pOfBeta_mem_pLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
          (IsingFK.pOfBeta (Ising.betaC 3)) :=
  eventually_pOfBeta_mem_fkPLeftCriticalIoo T.pδ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.betaδ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem pCritical_sub_pos_of_mem_pLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp


theorem pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
      (IsingFK.pOfBeta (Ising.betaC 3))) :
    IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp


theorem eventually_betaC_sub_pos
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.betaδ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.betaδ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.betaδ_pos


theorem eventually_pCritical_sub_pos
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < IsingFK.pOfBeta (Ising.betaC 3) - p :=
  eventually_pCritical_sub_pos_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_pCritical_sub_lt_delta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ :=
  eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo T.pδ_pos



theorem eventually_hasCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_fkMass_pos
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkMass p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkMass_pos hp

set_option linter.style.longLine false in


theorem eventually_fkMass_pos_comp_pOfBeta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkMass (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkMass_pos hp



theorem eventually_fkMassPrefactor_pos
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      0 < T.fkMassPrefactor p := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fkMassPrefactor_pos p hp

set_option linter.style.longLine false in


theorem eventually_fkMassPrefactor_pos_comp_pOfBeta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.fkMassPrefactor (IsingFK.pOfBeta β) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fkMassPrefactor_pos (IsingFK.pOfBeta β) hp



theorem eventually_fk_mass_scaling
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkMass p =
        T.fkMassPrefactor p *
          Real.exp
            (C.predictedExponent *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_mass_scaling p hp

set_option linter.style.longLine false in


theorem eventually_fk_mass_scaling_comp_pOfBeta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkMass (IsingFK.pOfBeta β) =
        T.fkMassPrefactor (IsingFK.pOfBeta β) *
          Real.exp
            (C.predictedExponent *
              Real.log
                (IsingFK.pOfBeta (Ising.betaC 3) -
                  IsingFK.pOfBeta β)) := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_mass_scaling (IsingFK.pOfBeta β) hp



theorem eventually_fk_length_eq_inv_mass
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      T.fkCorrelationLength p = (T.fkMass p)⁻¹ := by
  filter_upwards [T.eventually_mem_pLeftCriticalInterval] with p hp
  exact T.fk_length_eq_inv_mass p hp

set_option linter.style.longLine false in


theorem eventually_fk_length_eq_inv_mass_comp_pOfBeta
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.fkCorrelationLength (IsingFK.pOfBeta β) =
        (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
  filter_upwards [T.eventually_pOfBeta_mem_pLeftCriticalInterval] with β hp
  exact T.fk_length_eq_inv_mass (IsingFK.pOfBeta β) hp



theorem eventually_ising_fk_length_agree
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree


theorem fkLengthScalingFromMass
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      T.fkCorrelationLength p =
        (T.fkMassPrefactor p)⁻¹ *
          Real.exp
            (-C.predictedExponent *
              Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
  intro p hp
  rw [T.fk_length_eq_inv_mass p hp, T.fk_mass_scaling p hp]
  have hBne : T.fkMassPrefactor p ≠ 0 := (T.fkMassPrefactor_pos p hp).ne'
  have hexpne :
      Real.exp
          (C.predictedExponent *
            Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) ≠ 0 :=
    Real.exp_ne_zero _
  rw [show -C.predictedExponent *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p) =
        -(C.predictedExponent *
          Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) by ring,
    Real.exp_neg]
  field_simp [hBne, hexpne]



noncomputable def toFKMassTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKMassAnalyticRGToExponentTarget C where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMass_pos := fun p hp => T.fkMass_pos hp
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  fkPrefactor := fun p => (T.fkMassPrefactor p)⁻¹
  fkPrefactor_pos := fun p hp => inv_pos.mpr (T.fkMassPrefactor_pos p hp)
  fkPrefactor_log_negligible := by
    refine tendsto_log_inv_prefactor_div_log_betaC_sub
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) ?_ ?_
    · filter_upwards
        [Ioo_mem_nhdsLT
          (show (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC -
              T.pδ <
            (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC by
            rw [ParameterModel]
            linarith [T.pδ_pos])] with p hp
      exact T.fkMassPrefactor_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using T.fkMassPrefactor_log_negligible
  fk_length_scaling := T.fkLengthScalingFromMass
  ising_fk_length_agree := T.ising_fk_length_agree


noncomputable def toFKPowerLawTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKPowerLawToIsingAnalyticRGToExponentTarget C :=
  T.toFKMassTarget.toFKPowerLawTarget



@[simp] theorem toFKMassTarget_toFKPowerLawTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKMassTarget.toFKPowerLawTarget = T.toFKPowerLawTarget := by
  rfl



theorem fk_hasCriticalNu
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      T.fkCorrelationLength C.predictedExponent :=
  T.toFKMassTarget.fk_hasCriticalNu


noncomputable def toFKTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget C :=
  T.toFKMassTarget.toFKTarget



@[simp] theorem toFKMassTarget_toFKTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKMassTarget.toFKTarget = T.toFKTarget := by
  rfl



@[simp] theorem toFKPowerLawTarget_toFKTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKPowerLawTarget.toFKTarget = T.toFKTarget := by
  rfl


theorem hasCriticalNu
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu



theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toFKTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  T.toFKTarget.rgToExponentBridge




theorem rgToExponentBridge_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    T.isingCorrelationLength T.fkCorrelationLength T.fkMass
    T.fkMassPrefactor T.pδ T.pδ_pos T.fkMassPrefactor_pos
    T.fkMassPrefactor_log_negligible T.fk_mass_scaling
    T.fk_length_eq_inv_mass T.ising_fk_length_agree



theorem hasCriticalNu_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent := by
  simpa [RGCertificate.RGToExponentBridge] using T.rgToExponentBridge_direct



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  T.toFKTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic horbit



theorem valid_of_checks_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  C.valid_of_bridge T.isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit T.rgToExponentBridge_direct




theorem valid_of_checks_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKMassPowerLawToIsingAnalyticRGToExponentTarget D where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMassPrefactor := T.fkMassPrefactor
  fkMassPrefactor_pos := T.fkMassPrefactor_pos
  fkMassPrefactor_log_negligible := T.fkMassPrefactor_log_negligible
  fk_mass_scaling := by
    intro p hp
    simpa [hpred] using T.fk_mass_scaling p hp
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  ising_fk_length_agree := T.ising_fk_length_agree



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit



@[simp] theorem congr_predictedExponent_toFKMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKMassTarget =
      FKMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKMassTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toFKPowerLawTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKPowerLawTarget =
      FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKPowerLawTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toFKTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKTarget =
      FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKTarget := by
  rfl

end FKMassPowerLawToIsingAnalyticRGToExponentTarget

end Exact3D
end StatMech
