/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.AnalyticBridgeTarget
import Code.Exact3D.IsingBridgeTargets
import Code.Exact3D.PowerLawBridge














namespace StatMech
namespace Exact3D



theorem eventually_mem_isingLeftCriticalIoo {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - δ < Ising.betaC 3 by
      linarith)] with β hβ
  exact hβ


theorem betaC_sub_pos_of_mem_isingLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < δ := by
  linarith [hβ.1]



theorem beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC
    {δ β : ℝ} (hδle : δ ≤ Ising.betaC 3)
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < β := by
  have hnonneg : 0 ≤ Ising.betaC 3 - δ := sub_nonneg.mpr hδle
  linarith [hβ.1, hnonneg]


theorem eventually_betaC_sub_pos_isingLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [eventually_mem_isingLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ



theorem eventually_betaC_sub_lt_delta_isingLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < δ := by
  filter_upwards [eventually_mem_isingLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ



structure IsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  

  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (correlationLength β)
  
  prefactor : ℝ → ℝ
  prefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < prefactor β
  
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  
  length_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  T.realizesXAxisLength β hβ



theorem eventually_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos



theorem eventually_hasCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_prefactor_pos
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ



theorem eventually_length_scaling
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ


theorem rgToExponentBridge
    (T : IsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength := by
  refine C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    T.correlationLength T.prefactor T.δ T.δ_pos ?_ ?_ ?_
  · intro β hβ
    exact T.prefactor_pos β (by simpa [Ising3DModel] using hβ)
  · simpa [Ising3DModel] using T.prefactor_log_negligible
  · intro β hβ
    exact T.length_scaling β (by simpa [Ising3DModel] using hβ)


theorem hasCriticalNu
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [T.eventually_hasCorrelationLength] with β hβ
  exact hβ.liminfCorrelationLength_eq.symm



theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) := by
  exact
    RGCertificate.rgToExponentBridge_congr_eventually
      T.rgToExponentBridge
      ((T.eventually_correlationLength_eq_liminfCorrelationLength).mono
        fun _ hβ => hβ.symm)



theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.rgToExponentBridge_liminfCorrelationLength



theorem valid_of_checks
    (T : IsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := T.rgToExponentBridge




theorem valid_of_checks_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C)
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
    (T : IsingAnalyticRGToExponentTarget C) :
    IsingAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  realizesXAxisLength := T.realizesXAxisLength
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofPlusCorrelationLengthBridge
    (hbridge : PlusSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLength hbridge
  realizesXAxisLength := fun _ hβ =>
    plusSelectedSubcriticalCorrelationLength_hasCorrelationLength hbridge hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling



noncomputable def ofPlusPositiveCorrelationLengthBridge
    (hbridge : PlusPositiveSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedPositiveSubcriticalCorrelationLength hbridge
  realizesXAxisLength := fun _ hβ =>
    plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      hbridge
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end IsingAnalyticRGToExponentTarget




structure IsingMassAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  mass : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < mass β
  mass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (mass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (mass β)⁻¹
  prefactor : ℝ → ℝ
  prefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  length_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



theorem hasCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.mass β)⁻¹ :=
    (T.mass_realizes_inverse_length β hβ).hasCorrelationLength_inv
      (T.mass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ


theorem hasInverseCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (T.mass β) :=
  T.mass_realizes_inverse_length β hβ



theorem eventually_mem_leftCriticalInterval
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : IsingMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : IsingMassAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos


theorem eventually_mass_pos
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_pos β hβ



theorem eventually_hasInverseCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.mass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasInverseCorrelationLength hβ



theorem eventually_correlationLength_eq_inv_mass
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β = (T.mass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ



theorem eventually_hasCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_prefactor_pos
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ



theorem eventually_length_scaling
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ


def toLengthTarget
    (T : IsingMassAnalyticRGToExponentTarget C) :
    IsingAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  realizesXAxisLength := fun _ hβ => T.hasCorrelationLength hβ
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling


theorem rgToExponentBridge
    (T : IsingMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength :=
  T.toLengthTarget.rgToExponentBridge


theorem hasCriticalNu
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toLengthTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : IsingMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toLengthTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.mass
  mass_pos := T.mass_pos
  mass_realizes_inverse_length := T.mass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ



@[simp] theorem congr_predictedExponent_toLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toLengthTarget := by
  rfl



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofPlusMassBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedSubcriticalMass hmass
  mass_pos := fun _ hβ => plusSelectedSubcriticalMass_pos hmass hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling




noncomputable def ofPlusPositiveMassBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedPositiveSubcriticalMass hmass
  mass_pos := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end IsingMassAnalyticRGToExponentTarget




structure IsingMassPowerLawAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  mass : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < mass β
  mass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (mass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (mass β)⁻¹
  
  massPrefactor : ℝ → ℝ
  massPrefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (massPrefactor β) /
        Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  
  mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      mass β =
        massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



theorem hasCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.mass β)⁻¹ :=
    (T.mass_realizes_inverse_length β hβ).hasCorrelationLength_inv
      (T.mass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ


theorem hasInverseCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (T.mass β) :=
  T.mass_realizes_inverse_length β hβ



theorem eventually_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos


theorem eventually_mass_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_pos β hβ



theorem eventually_hasInverseCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.mass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasInverseCorrelationLength hβ



theorem eventually_correlationLength_eq_inv_mass
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β = (T.mass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ



theorem eventually_hasCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


theorem eventually_massPrefactor_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.massPrefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.massPrefactor_pos β hβ



theorem eventually_mass_scaling
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.mass β =
        T.massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_scaling β hβ


theorem lengthScalingFromMass
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    T.correlationLength β =
      (T.massPrefactor β)⁻¹ *
        Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  rw [T.correlationLength_eq_inv_mass β hβ, T.mass_scaling β hβ]
  have hBne : T.massPrefactor β ≠ 0 := (T.massPrefactor_pos β hβ).ne'
  have hexpne :
      Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) ≠ 0 :=
    Real.exp_ne_zero _
  rw [show -C.predictedExponent * Real.log (Ising.betaC 3 - β) =
      -(C.predictedExponent * Real.log (Ising.betaC 3 - β)) by ring,
    Real.exp_neg]
  field_simp [hBne, hexpne]



noncomputable def toMassTarget
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.mass
  mass_pos := T.mass_pos
  mass_realizes_inverse_length := T.mass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := fun β => (T.massPrefactor β)⁻¹
  prefactor_pos := fun β hβ => inv_pos.mpr (T.massPrefactor_pos β hβ)
  prefactor_log_negligible := by
    refine tendsto_log_inv_prefactor_div_log_betaC_sub Ising3DModel ?_ ?_
    · filter_upwards
        [Ioo_mem_nhdsLT
          (show Ising3DModel.betaC - T.δ < Ising3DModel.betaC by
            rw [Ising3DModel]
            linarith [T.δ_pos])] with β hβ
      exact T.massPrefactor_pos β (by simpa [Ising3DModel] using hβ)
    · simpa [Ising3DModel] using T.massPrefactor_log_negligible
  length_scaling := fun β hβ => T.lengthScalingFromMass hβ


noncomputable def toLengthTarget
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toMassTarget.toLengthTarget

@[simp] theorem toMassTarget_toLengthTarget
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    T.toMassTarget.toLengthTarget = T.toLengthTarget :=
  rfl


theorem rgToExponentBridge
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength := by
  refine C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    T.correlationLength T.mass T.massPrefactor T.δ T.δ_pos ?_ ?_ ?_ ?_
  · intro β hβ
    exact T.massPrefactor_pos β (by simpa [Ising3DModel] using hβ)
  · simpa [Ising3DModel] using T.massPrefactor_log_negligible
  · intro β hβ
    exact T.mass_scaling β (by simpa [Ising3DModel] using hβ)
  · intro β hβ
    exact T.correlationLength_eq_inv_mass β (by simpa [Ising3DModel] using hβ)


theorem hasCriticalNu
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toLengthTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toMassTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    IsingMassPowerLawAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.mass
  mass_pos := T.mass_pos
  mass_realizes_inverse_length := T.mass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  mass_scaling := by
    intro β hβ
    simpa [hpred] using T.mass_scaling β hβ



@[simp] theorem congr_predictedExponent_toMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toMassTarget =
      IsingMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toMassTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toLengthTarget := by
  rfl



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofPlusMassBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedSubcriticalMass hmass
  mass_pos := fun _ hβ => plusSelectedSubcriticalMass_pos hmass hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  mass_scaling := hmass_scaling




noncomputable def ofPlusPositiveMassBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedPositiveSubcriticalMass hmass
  mass_pos := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  mass_scaling := hmass_scaling

end IsingMassPowerLawAnalyticRGToExponentTarget

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofPlusMassBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toLengthTarget



noncomputable def ofPlusPositiveMassBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toLengthTarget


noncomputable def ofPlusMassPowerLawBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toLengthTarget



noncomputable def ofPlusPositiveMassPowerLawBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toLengthTarget

end IsingAnalyticRGToExponentTarget

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofPlusMassPowerLawBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toMassTarget



noncomputable def ofPlusPositiveMassPowerLawBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toMassTarget

end IsingMassAnalyticRGToExponentTarget



structure FreeAnalyticRGToPlusExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  

  plus_free_agree : PlusFreeTwoPointAgreeBelowBetaC
  
  free_realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (correlationLength β)
  
  prefactor : ℝ → ℝ
  prefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < prefactor β
  
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  

  length_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem free_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  T.free_realizesXAxisLength β hβ



theorem plus_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree T.plus_free_agree hβ.2
    (T.free_realizesXAxisLength β hβ)



theorem eventually_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : FreeAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos



theorem eventually_free_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.free_hasCorrelationLength hβ



theorem eventually_hasCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.plus_hasCorrelationLength hβ



theorem eventually_prefactor_pos
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ



theorem eventually_length_scaling
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ



def toPlusLengthTarget
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    IsingAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  realizesXAxisLength := fun _ hβ => T.plus_hasCorrelationLength hβ
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling

@[simp] theorem toPlusLengthTarget_correlationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    T.toPlusLengthTarget.correlationLength = T.correlationLength :=
  rfl



theorem rgToExponentBridge
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    C.RGToExponentBridge T.correlationLength :=
  T.toPlusLengthTarget.rgToExponentBridge



theorem hasCriticalNu
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toPlusLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toPlusLengthTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FreeAnalyticRGToPlusExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toPlusLengthTarget.valid_of_checks hfinite htail hfixed hlinear
    hhyperbolic horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : FreeAnalyticRGToPlusExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  plus_free_agree := T.plus_free_agree
  free_realizesXAxisLength := T.free_realizesXAxisLength
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ



@[simp] theorem congr_predictedExponent_toPlusLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusLengthTarget := by
  rfl



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofFreeCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreeSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedSubcriticalCorrelationLength hbridge
  plus_free_agree := hagree
  free_realizesXAxisLength := fun _ hβ =>
    freeSelectedSubcriticalCorrelationLength_hasCorrelationLength hbridge hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling



noncomputable def ofFreePositiveCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreePositiveSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedPositiveSubcriticalCorrelationLength hbridge
  plus_free_agree := hagree
  free_realizesXAxisLength := fun _ hβ =>
    freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      hbridge
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end FreeAnalyticRGToPlusExponentTarget




structure FreeMassAnalyticRGToPlusExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  freeMass : ℝ → ℝ
  plus_free_agree : PlusFreeTwoPointAgreeBelowBetaC
  freeMass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeMass β
  freeMass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeMass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (freeMass β)⁻¹
  prefactor : ℝ → ℝ
  prefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  length_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace FreeMassAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}



theorem plus_hasInverseCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.freeMass β) :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree T.plus_free_agree
    hβ.2 (T.freeMass_realizes_inverse_length β hβ)



theorem free_hasCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (T.freeMass β)⁻¹ :=
    (T.freeMass_realizes_inverse_length β hβ).hasCorrelationLength_inv
      (T.freeMass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ



theorem hasCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.freeMass β)⁻¹ :=
    (T.plus_hasInverseCorrelationLength hβ).hasCorrelationLength_inv
      (T.freeMass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ



theorem eventually_mem_leftCriticalInterval
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos



theorem eventually_freeMass_pos
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.freeMass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.freeMass_pos β hβ



theorem eventually_free_hasInverseCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.freeMass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.freeMass_realizes_inverse_length β hβ



theorem eventually_plus_hasInverseCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.freeMass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.plus_hasInverseCorrelationLength hβ



theorem eventually_free_hasCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.free_hasCorrelationLength hβ



theorem eventually_hasCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_correlationLength_eq_inv_mass
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β = (T.freeMass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ



theorem eventually_prefactor_pos
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ



theorem eventually_length_scaling
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ



def toFreeLengthTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  plus_free_agree := T.plus_free_agree
  free_realizesXAxisLength := fun _ hβ => T.free_hasCorrelationLength hβ
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling



def toPlusMassTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.freeMass
  mass_pos := T.freeMass_pos
  mass_realizes_inverse_length := fun _ hβ =>
    T.plus_hasInverseCorrelationLength hβ
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling



def toPlusLengthTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toPlusMassTarget.toLengthTarget

@[simp] theorem toPlusMassTarget_toLengthTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    T.toPlusMassTarget.toLengthTarget = T.toPlusLengthTarget :=
  rfl



theorem rgToExponentBridge
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    C.RGToExponentBridge T.correlationLength :=
  T.toPlusMassTarget.rgToExponentBridge



theorem hasCriticalNu
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toPlusLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toPlusLengthTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toPlusMassTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    FreeMassAnalyticRGToPlusExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  freeMass := T.freeMass
  plus_free_agree := T.plus_free_agree
  freeMass_pos := T.freeMass_pos
  freeMass_realizes_inverse_length := T.freeMass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ



@[simp] theorem congr_predictedExponent_toFreeLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    (T.congr_predictedExponent hpred).toFreeLengthTarget =
      FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent
        hpred T.toFreeLengthTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toPlusMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusMassTarget =
      IsingMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusMassTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toPlusLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusLengthTarget := by
  rfl



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ => freeSelectedSubcriticalMass_pos hmass hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling




noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedPositiveSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end FreeMassAnalyticRGToPlusExponentTarget



structure FreeMassPowerLawToPlusAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  freeMass : ℝ → ℝ
  plus_free_agree : PlusFreeTwoPointAgreeBelowBetaC
  freeMass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeMass β
  freeMass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeMass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (freeMass β)⁻¹
  massPrefactor : ℝ → ℝ
  massPrefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (massPrefactor β) /
        Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  freeMass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      freeMass β =
        massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace FreeMassPowerLawToPlusAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



theorem plus_hasInverseCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.freeMass β) :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree T.plus_free_agree
    hβ.2 (T.freeMass_realizes_inverse_length β hβ)



theorem free_hasCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (T.freeMass β)⁻¹ :=
    (T.freeMass_realizes_inverse_length β hβ).hasCorrelationLength_inv
      (T.freeMass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ



theorem hasCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.freeMass β)⁻¹ :=
    (T.plus_hasInverseCorrelationLength hβ).hasCorrelationLength_inv
      (T.freeMass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ



theorem eventually_mem_leftCriticalInterval
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos



theorem eventually_betaC_sub_lt_delta
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos



theorem eventually_freeMass_pos
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.freeMass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.freeMass_pos β hβ



theorem eventually_free_hasInverseCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.freeMass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.freeMass_realizes_inverse_length β hβ



theorem eventually_plus_hasInverseCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.freeMass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.plus_hasInverseCorrelationLength hβ



theorem eventually_free_hasCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.free_hasCorrelationLength hβ



theorem eventually_hasCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



theorem eventually_correlationLength_eq_inv_mass
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β = (T.freeMass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ



theorem eventually_massPrefactor_pos
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.massPrefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.massPrefactor_pos β hβ



theorem eventually_freeMass_scaling
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.freeMass β =
        T.massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.freeMass_scaling β hβ



theorem lengthScalingFromFreeMass
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    T.correlationLength β =
      (T.massPrefactor β)⁻¹ *
        Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  rw [T.correlationLength_eq_inv_mass β hβ, T.freeMass_scaling β hβ]
  have hBne : T.massPrefactor β ≠ 0 := (T.massPrefactor_pos β hβ).ne'
  have hexpne :
      Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) ≠ 0 :=
    Real.exp_ne_zero _
  rw [show -C.predictedExponent * Real.log (Ising.betaC 3 - β) =
      -(C.predictedExponent * Real.log (Ising.betaC 3 - β)) by ring,
    Real.exp_neg]
  field_simp [hBne, hexpne]



theorem eventually_lengthScalingFromFreeMass
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        (T.massPrefactor β)⁻¹ *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.lengthScalingFromFreeMass hβ



noncomputable def toFreeMassTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    FreeMassAnalyticRGToPlusExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  freeMass := T.freeMass
  plus_free_agree := T.plus_free_agree
  freeMass_pos := T.freeMass_pos
  freeMass_realizes_inverse_length := T.freeMass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := fun β => (T.massPrefactor β)⁻¹
  prefactor_pos := fun β hβ => inv_pos.mpr (T.massPrefactor_pos β hβ)
  prefactor_log_negligible := by
    refine tendsto_log_inv_prefactor_div_log_betaC_sub Ising3DModel ?_ ?_
    · filter_upwards
        [Ioo_mem_nhdsLT
          (show Ising3DModel.betaC - T.δ < Ising3DModel.betaC by
            rw [Ising3DModel]
            linarith [T.δ_pos])] with β hβ
      exact T.massPrefactor_pos β (by simpa [Ising3DModel] using hβ)
    · simpa [Ising3DModel] using T.massPrefactor_log_negligible
  length_scaling := fun β hβ => T.lengthScalingFromFreeMass hβ



noncomputable def toFreeLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget C :=
  T.toFreeMassTarget.toFreeLengthTarget



noncomputable def toPlusMassTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget C :=
  T.toFreeMassTarget.toPlusMassTarget



noncomputable def toPlusLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toPlusMassTarget.toLengthTarget



def toPlusMassPowerLawTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.freeMass
  mass_pos := T.freeMass_pos
  mass_realizes_inverse_length := fun _ hβ =>
    T.plus_hasInverseCorrelationLength hβ
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  mass_scaling := T.freeMass_scaling

@[simp] theorem toFreeMassTarget_toFreeLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    T.toFreeMassTarget.toFreeLengthTarget = T.toFreeLengthTarget :=
  rfl

@[simp] theorem toFreeMassTarget_toPlusMassTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    T.toFreeMassTarget.toPlusMassTarget = T.toPlusMassTarget :=
  rfl

@[simp] theorem toPlusMassTarget_toLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    T.toPlusMassTarget.toLengthTarget = T.toPlusLengthTarget :=
  rfl



theorem rgToExponentBridge
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength :=
  T.toFreeMassTarget.rgToExponentBridge



theorem hasCriticalNu
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toPlusLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toPlusLengthTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toFreeMassTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toPlusLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  freeMass := T.freeMass
  plus_free_agree := T.plus_free_agree
  freeMass_pos := T.freeMass_pos
  freeMass_realizes_inverse_length := T.freeMass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  freeMass_scaling := by
    intro β hβ
    simpa [hpred] using T.freeMass_scaling β hβ



@[simp] theorem congr_predictedExponent_toFreeMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFreeMassTarget =
      FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent
        hpred T.toFreeMassTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toFreeLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFreeLengthTarget =
      FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent
        hpred T.toFreeLengthTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toPlusMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusMassTarget =
      IsingMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusMassTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toPlusLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusLengthTarget := by
  rfl



@[simp] theorem congr_predictedExponent_toPlusMassPowerLawTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusMassPowerLawTarget =
      IsingMassPowerLawAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusMassPowerLawTarget := by
  rfl



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit




noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ => freeSelectedSubcriticalMass_pos hmass hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  freeMass_scaling := hmass_scaling



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedPositiveSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  freeMass_scaling := hmass_scaling

end FreeMassPowerLawToPlusAnalyticRGToExponentTarget

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toFreeLengthTarget



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toFreeLengthTarget



noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toFreeLengthTarget



noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toFreeLengthTarget

end FreeAnalyticRGToPlusExponentTarget

namespace FreeMassAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toFreeMassTarget



noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toFreeMassTarget

end FreeMassAnalyticRGToPlusExponentTarget

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreeSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeAnalyticRGToPlusExponentTarget.ofFreeCorrelationLengthBridge
    (C := C) hagree hbridge δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget



noncomputable def ofFreePositiveCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreePositiveSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeAnalyticRGToPlusExponentTarget.ofFreePositiveCorrelationLengthBridge
    (C := C) hagree hbridge δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget



noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget



noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusLengthTarget



noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusLengthTarget

end IsingAnalyticRGToExponentTarget

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusMassTarget



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusMassTarget



noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusMassTarget



noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusMassTarget

end IsingMassAnalyticRGToExponentTarget

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}



noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusMassPowerLawTarget



noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusMassPowerLawTarget

end IsingMassPowerLawAnalyticRGToExponentTarget

end Exact3D
end StatMech
