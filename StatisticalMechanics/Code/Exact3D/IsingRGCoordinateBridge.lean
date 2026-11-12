/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingAnalyticBridgeTarget
import Code.Exact3D.LatticeRG














namespace StatMech
namespace Exact3D



structure IsingRGCoordinateScaffold
    (C : RGCertificate Ising3DModel) where
  
  latticeRG : LatticeRGData 3
  
  scale_match : latticeRG.kernel.scale = C.scale
  

  coordinate : ℝ → C.H.carrier
  
  rgNeighborhood : Set C.H.carrier
  
  renormalizedBeta : ℝ → ℝ
  
  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  
  prefactor : ℝ → ℝ

namespace IsingRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


def leftCriticalInterval (S : IsingRGCoordinateScaffold C) : Set ℝ :=
  Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3)

@[simp] theorem mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ} :
    β ∈ S.leftCriticalInterval ↔
      β ∈ Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3) :=
  Iff.rfl


theorem leftCriticalInterval_subset_Iio
    (S : IsingRGCoordinateScaffold C) :
    S.leftCriticalInterval ⊆ Set.Iio (Ising.betaC 3) := by
  intro β hβ
  exact hβ.2


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    Ising.betaC 3 - β < S.δ := by
  linarith [hβ.1]



theorem eventually_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ S.leftCriticalInterval := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - S.δ < Ising.betaC 3 by
      linarith [S.δ_pos])] with β hβ
  exact hβ



theorem eventually_betaC_sub_pos
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_pos_of_mem_leftCriticalInterval hβ



theorem eventually_betaC_sub_lt_delta
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < S.δ := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_lt_delta_of_mem_leftCriticalInterval hβ

@[simp] theorem latticeRG_kernel_scale_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale = C.scale :=
  S.scale_match

theorem latticeRG_R_scale_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.R.scale = C.scale :=
  S.latticeRG.R_scale_eq_kernel_scale.trans S.scale_match

@[simp] theorem latticeRG_kernel_scale_toReal_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_kernel_scale_eq_certificate

theorem latticeRG_R_scale_toReal_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.R.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_R_scale_eq_certificate



def LengthCovariance (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    S.renormalizedBeta β ∈ S.leftCriticalInterval ∧
      S.correlationLength (S.renormalizedBeta β) =
        S.correlationLength β / S.latticeRG.kernel.scale.toReal


def CoordinateRGCovariance (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β)



def MicroscopicOrbitEntry (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
    S.coordinate β ∈ S.rgNeighborhood


theorem length_covariance_maps_interval
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.renormalizedBeta β ∈ S.leftCriticalInterval :=
  (hcov β hβ).1



theorem length_covariance_lattice_scale
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.correlationLength (S.renormalizedBeta β) =
      S.correlationLength β / S.latticeRG.kernel.scale.toReal :=
  (hcov β hβ).2



theorem length_covariance_certificate_scale
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.correlationLength (S.renormalizedBeta β) =
      S.correlationLength β / C.scale.toReal := by
  have h := (hcov β hβ).2
  rw [S.latticeRG_kernel_scale_toReal_eq_certificate] at h
  exact h



theorem coordinate_rg_covariance
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.CoordinateRGCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) :=
  hcov β hβ

end IsingRGCoordinateScaffold










structure IsingRGCoordinateBridgeInputs
    (C : RGCertificate Ising3DModel) where
  scaffold : IsingRGCoordinateScaffold C
  lengthCovariance : scaffold.LengthCovariance
  coordinateCovariance : scaffold.CoordinateRGCovariance
  microscopicOrbitEntry : scaffold.MicroscopicOrbitEntry
  stableManifoldControlStatement : Prop
  stableManifoldControl : stableManifoldControlStatement
  realizesXAxisLength :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (scaffold.correlationLength β)
  prefactor_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (scaffold.prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  extractsLengthScaling :
    scaffold.LengthCovariance →
      scaffold.CoordinateRGCovariance →
      stableManifoldControlStatement →
      scaffold.MicroscopicOrbitEntry →
        ∀ β, β ∈ scaffold.leftCriticalInterval →
          scaffold.correlationLength β =
            scaffold.prefactor β *
              Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace IsingRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem length_scaling
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength β =
      T.scaffold.prefactor β *
        Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) :=
  T.extractsLengthScaling T.lengthCovariance T.coordinateCovariance
    T.stableManifoldControl T.microscopicOrbitEntry β hβ



theorem renormalizedBeta_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.length_covariance_maps_interval T.lengthCovariance hβ



theorem betaC_sub_renormalizedBeta_pos
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β :=
  T.scaffold.betaC_sub_pos_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)



theorem betaC_sub_renormalizedBeta_lt_delta
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ :=
  T.scaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)



theorem length_covariance_lattice_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
      T.scaffold.correlationLength β /
        T.scaffold.latticeRG.kernel.scale.toReal :=
  T.scaffold.length_covariance_lattice_scale T.lengthCovariance hβ



theorem length_covariance_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
      T.scaffold.correlationLength β / C.scale.toReal :=
  T.scaffold.length_covariance_certificate_scale T.lengthCovariance hβ



theorem renormalizedBeta_iterate_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      (T.scaffold.renormalizedBeta^[k]) β ∈
        T.scaffold.leftCriticalInterval := by
  intro k
  induction k with
  | zero =>
      simpa using hβ
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        T.renormalizedBeta_mem_leftCriticalInterval ih



theorem length_covariance_iterate_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      T.scaffold.correlationLength
          ((T.scaffold.renormalizedBeta^[k]) β) =
        T.scaffold.correlationLength β / (C.scale.toReal ^ k) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      have hstep := T.length_covariance_certificate_scale hmem
      calc
        T.scaffold.correlationLength
            ((T.scaffold.renormalizedBeta^[Nat.succ k]) β)
            =
            T.scaffold.correlationLength
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            T.scaffold.correlationLength
              ((T.scaffold.renormalizedBeta^[k]) β) / C.scale.toReal :=
          hstep
        _ =
            (T.scaffold.correlationLength β / (C.scale.toReal ^ k)) /
              C.scale.toReal := by
          rw [ih]
        _ =
            T.scaffold.correlationLength β /
              (C.scale.toReal ^ Nat.succ k) := by
          simp [pow_succ, div_div]



theorem coordinate_rg_covariance_iterate
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      ((C.R.map)^[k]) (T.scaffold.coordinate β) =
        T.scaffold.coordinate ((T.scaffold.renormalizedBeta^[k]) β) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      calc
        ((C.R.map)^[Nat.succ k]) (T.scaffold.coordinate β)
            =
            C.R.map (((C.R.map)^[k]) (T.scaffold.coordinate β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            C.R.map
              (T.scaffold.coordinate
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [ih]
        _ =
            T.scaffold.coordinate
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) :=
          T.scaffold.coordinate_rg_covariance T.coordinateCovariance hmem
        _ =
            T.scaffold.coordinate
              ((T.scaffold.renormalizedBeta^[Nat.succ k]) β) := by
          rw [Function.iterate_succ_apply']



theorem coordinate_rg_covariance
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    C.R.map (T.scaffold.coordinate β) =
      T.scaffold.coordinate (T.scaffold.renormalizedBeta β) :=
  T.scaffold.coordinate_rg_covariance T.coordinateCovariance hβ



theorem eventually_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.eventually_mem_leftCriticalInterval



theorem eventually_betaC_sub_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  T.scaffold.eventually_betaC_sub_pos



theorem eventually_betaC_sub_lt_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.scaffold.δ :=
  T.scaffold.eventually_betaC_sub_lt_delta



theorem eventually_coordinate_mem_rgNeighborhood
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood :=
  T.microscopicOrbitEntry



theorem eventually_renormalizedBeta_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.renormalizedBeta_mem_leftCriticalInterval hβ



theorem eventually_betaC_sub_renormalizedBeta_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_pos hβ



theorem eventually_betaC_sub_renormalizedBeta_lt_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_lt_delta hβ



theorem eventually_length_covariance_lattice_scale
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
        T.scaffold.correlationLength β /
          T.scaffold.latticeRG.kernel.scale.toReal := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_covariance_lattice_scale hβ



theorem eventually_length_covariance_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
        T.scaffold.correlationLength β / C.scale.toReal := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_covariance_certificate_scale hβ



theorem eventually_prefactor_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ



theorem eventually_length_scaling
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        T.scaffold.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling hβ



theorem eventually_coordinate_rg_covariance
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      C.R.map (T.scaffold.coordinate β) =
        T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.coordinate_rg_covariance hβ


theorem hasCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.scaffold.correlationLength β) :=
  T.realizesXAxisLength β hβ



theorem eventually_hasCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



def toIsingAnalyticTarget
    (T : IsingRGCoordinateBridgeInputs C) :
    IsingAnalyticRGToExponentTarget C where
  δ := T.scaffold.δ
  δ_pos := T.scaffold.δ_pos
  correlationLength := T.scaffold.correlationLength
  realizesXAxisLength := T.realizesXAxisLength
  prefactor := T.scaffold.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := fun _ hβ => T.length_scaling hβ



theorem toAnalyticPrefactorBridgeInputs
    (T : IsingRGCoordinateBridgeInputs C) :
    RGCertificate.AnalyticPrefactorBridgeInputs
      C T.scaffold.correlationLength T.scaffold.prefactor
      (T.scaffold.LengthCovariance ∧
        T.scaffold.CoordinateRGCovariance)
      T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry
      (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
          (T.scaffold.correlationLength β)) where
  rgCovariance := ⟨T.lengthCovariance, T.coordinateCovariance⟩
  stableManifoldControl := T.stableManifoldControl
  microscopicOrbitEntry := T.microscopicOrbitEntry
  subcriticalMassBridge := T.eventually_hasCorrelationLength
  prefactor_pos := by
    simpa [Ising3DModel] using T.eventually_prefactor_pos
  prefactor_log_negligible := by
    simpa [Ising3DModel] using T.prefactor_log_negligible
  extractsPrefactorPowerLaw := by
    intro _ _ _ _
    simpa [Ising3DModel] using T.eventually_length_scaling

@[simp] theorem toIsingAnalyticTarget_correlationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingAnalyticTarget_prefactor
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.prefactor = T.scaffold.prefactor :=
  rfl

@[simp] theorem toIsingAnalyticTarget_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.δ = T.scaffold.δ :=
  rfl


theorem rgToExponentBridge
    (T : IsingRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.rgToExponentBridge


theorem hasCriticalNu
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toIsingAnalyticTarget.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingAnalyticTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toIsingAnalyticTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.valid_of_checks hfinite htail hfixed hlinear
    hhyperbolic horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingAnalyticTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.rgToExponentBridge_congr_predictedExponent hpred



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      D.predictedExponent :=
  T.toIsingAnalyticTarget.hasCriticalNu_congr_predictedExponent hpred



theorem rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      D.predictedExponent :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.valid_of_checks_congr_predictedExponent hpred
    hfinite htail hfixed hlinear hhyperbolic horbit



theorem valid_of_checks_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).valid_of_checks_liminfCorrelationLength
      hfinite htail hfixed hlinear hhyperbolic horbit

end IsingRGCoordinateBridgeInputs




structure IsingMassRGCoordinateScaffold
    (C : RGCertificate Ising3DModel) where
  
  latticeRG : LatticeRGData 3
  
  scale_match : latticeRG.kernel.scale = C.scale
  

  coordinate : ℝ → C.H.carrier
  
  rgNeighborhood : Set C.H.carrier
  
  renormalizedBeta : ℝ → ℝ
  
  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  
  mass : ℝ → ℝ
  
  massPrefactor : ℝ → ℝ

namespace IsingMassRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


def leftCriticalInterval (S : IsingMassRGCoordinateScaffold C) : Set ℝ :=
  Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3)

@[simp] theorem mem_leftCriticalInterval
    (S : IsingMassRGCoordinateScaffold C) {β : ℝ} :
    β ∈ S.leftCriticalInterval ↔
      β ∈ Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3) :=
  Iff.rfl


theorem leftCriticalInterval_subset_Iio
    (S : IsingMassRGCoordinateScaffold C) :
    S.leftCriticalInterval ⊆ Set.Iio (Ising.betaC 3) := by
  intro β hβ
  exact hβ.2


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (S : IsingMassRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (S : IsingMassRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    Ising.betaC 3 - β < S.δ := by
  linarith [hβ.1]



theorem eventually_mem_leftCriticalInterval
    (S : IsingMassRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ S.leftCriticalInterval := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - S.δ < Ising.betaC 3 by
      linarith [S.δ_pos])] with β hβ
  exact hβ



theorem eventually_betaC_sub_pos
    (S : IsingMassRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_pos_of_mem_leftCriticalInterval hβ



theorem eventually_betaC_sub_lt_delta
    (S : IsingMassRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < S.δ := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_lt_delta_of_mem_leftCriticalInterval hβ

@[simp] theorem latticeRG_kernel_scale_eq_certificate
    (S : IsingMassRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale = C.scale :=
  S.scale_match

theorem latticeRG_R_scale_eq_certificate
    (S : IsingMassRGCoordinateScaffold C) :
    S.latticeRG.R.scale = C.scale :=
  S.latticeRG.R_scale_eq_kernel_scale.trans S.scale_match

@[simp] theorem latticeRG_kernel_scale_toReal_eq_certificate
    (S : IsingMassRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_kernel_scale_eq_certificate

theorem latticeRG_R_scale_toReal_eq_certificate
    (S : IsingMassRGCoordinateScaffold C) :
    S.latticeRG.R.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_R_scale_eq_certificate



def MassCovariance (S : IsingMassRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    S.renormalizedBeta β ∈ S.leftCriticalInterval ∧
      S.mass (S.renormalizedBeta β) =
        S.latticeRG.kernel.scale.toReal * S.mass β


def CoordinateRGCovariance (S : IsingMassRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β)



def MicroscopicOrbitEntry (S : IsingMassRGCoordinateScaffold C) : Prop :=
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
    S.coordinate β ∈ S.rgNeighborhood


theorem mass_covariance_maps_interval
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.renormalizedBeta β ∈ S.leftCriticalInterval :=
  (hcov β hβ).1



theorem mass_covariance_lattice_scale
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.mass (S.renormalizedBeta β) =
      S.latticeRG.kernel.scale.toReal * S.mass β :=
  (hcov β hβ).2



theorem mass_covariance_certificate_scale
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.mass (S.renormalizedBeta β) = C.scale.toReal * S.mass β := by
  have h := (hcov β hβ).2
  rw [S.latticeRG_kernel_scale_toReal_eq_certificate] at h
  exact h



theorem coordinate_rg_covariance
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.CoordinateRGCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) :=
  hcov β hβ

end IsingMassRGCoordinateScaffold







structure IsingMassRGCoordinateBridgeInputs
    (C : RGCertificate Ising3DModel) where
  scaffold : IsingMassRGCoordinateScaffold C
  massCovariance : scaffold.MassCovariance
  coordinateCovariance : scaffold.CoordinateRGCovariance
  microscopicOrbitEntry : scaffold.MicroscopicOrbitEntry
  stableManifoldControlStatement : Prop
  stableManifoldControl : stableManifoldControlStatement
  mass_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.mass β
  realizesInverseXAxisLength :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (scaffold.mass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      scaffold.correlationLength β = (scaffold.mass β)⁻¹
  massPrefactor_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (scaffold.massPrefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  extractsMassScaling :
    scaffold.MassCovariance →
      scaffold.CoordinateRGCovariance →
      stableManifoldControlStatement →
      scaffold.MicroscopicOrbitEntry →
        ∀ β, β ∈ scaffold.leftCriticalInterval →
          scaffold.mass β =
            scaffold.massPrefactor β *
              Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

namespace IsingMassRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem mass_scaling
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass β =
      T.scaffold.massPrefactor β *
        Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) :=
  T.extractsMassScaling T.massCovariance T.coordinateCovariance
    T.stableManifoldControl T.microscopicOrbitEntry β hβ



theorem renormalizedBeta_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.mass_covariance_maps_interval T.massCovariance hβ



theorem betaC_sub_renormalizedBeta_pos
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β :=
  T.scaffold.betaC_sub_pos_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)



theorem betaC_sub_renormalizedBeta_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ :=
  T.scaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)



theorem mass_covariance_lattice_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass (T.scaffold.renormalizedBeta β) =
      T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β :=
  T.scaffold.mass_covariance_lattice_scale T.massCovariance hβ



theorem mass_covariance_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass (T.scaffold.renormalizedBeta β) =
      C.scale.toReal * T.scaffold.mass β :=
  T.scaffold.mass_covariance_certificate_scale T.massCovariance hβ




theorem renormalizedBeta_iterate_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      (T.scaffold.renormalizedBeta^[k]) β ∈
        T.scaffold.leftCriticalInterval := by
  intro k
  induction k with
  | zero =>
      simpa using hβ
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        T.renormalizedBeta_mem_leftCriticalInterval ih



theorem mass_covariance_iterate_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      T.scaffold.mass ((T.scaffold.renormalizedBeta^[k]) β) =
        (C.scale.toReal ^ k) * T.scaffold.mass β := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      have hstep := T.mass_covariance_certificate_scale hmem
      calc
        T.scaffold.mass
            ((T.scaffold.renormalizedBeta^[Nat.succ k]) β)
            =
            T.scaffold.mass
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            C.scale.toReal *
              T.scaffold.mass
                ((T.scaffold.renormalizedBeta^[k]) β) :=
          hstep
        _ =
            C.scale.toReal *
              ((C.scale.toReal ^ k) * T.scaffold.mass β) := by
          rw [ih]
        _ =
            (C.scale.toReal ^ Nat.succ k) * T.scaffold.mass β := by
          rw [pow_succ]
          ring




theorem coordinate_rg_covariance_iterate
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      ((C.R.map)^[k]) (T.scaffold.coordinate β) =
        T.scaffold.coordinate ((T.scaffold.renormalizedBeta^[k]) β) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      calc
        ((C.R.map)^[Nat.succ k]) (T.scaffold.coordinate β)
            =
            C.R.map (((C.R.map)^[k]) (T.scaffold.coordinate β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            C.R.map
              (T.scaffold.coordinate
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [ih]
        _ =
            T.scaffold.coordinate
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) :=
          T.scaffold.coordinate_rg_covariance T.coordinateCovariance hmem
        _ =
            T.scaffold.coordinate
              ((T.scaffold.renormalizedBeta^[Nat.succ k]) β) := by
          rw [Function.iterate_succ_apply']



theorem coordinate_rg_covariance
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    C.R.map (T.scaffold.coordinate β) =
      T.scaffold.coordinate (T.scaffold.renormalizedBeta β) :=
  T.scaffold.coordinate_rg_covariance T.coordinateCovariance hβ



theorem eventually_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.eventually_mem_leftCriticalInterval



theorem eventually_betaC_sub_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  T.scaffold.eventually_betaC_sub_pos



theorem eventually_betaC_sub_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.scaffold.δ :=
  T.scaffold.eventually_betaC_sub_lt_delta



theorem eventually_coordinate_mem_rgNeighborhood
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood :=
  T.microscopicOrbitEntry



theorem eventually_renormalizedBeta_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.renormalizedBeta_mem_leftCriticalInterval hβ



theorem eventually_betaC_sub_renormalizedBeta_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_pos hβ



theorem eventually_betaC_sub_renormalizedBeta_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_lt_delta hβ



theorem eventually_mass_covariance_lattice_scale
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass (T.scaffold.renormalizedBeta β) =
        T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_covariance_lattice_scale hβ



theorem eventually_mass_covariance_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass (T.scaffold.renormalizedBeta β) =
        C.scale.toReal * T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_covariance_certificate_scale hβ


theorem eventually_mass_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_pos β hβ


theorem eventually_massPrefactor_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.massPrefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.massPrefactor_pos β hβ



theorem eventually_mass_scaling
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass β =
        T.scaffold.massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_scaling hβ



theorem eventually_correlationLength_eq_inv_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β = (T.scaffold.mass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ



theorem eventually_coordinate_rg_covariance
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      C.R.map (T.scaffold.coordinate β) =
        T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.coordinate_rg_covariance hβ



theorem hasInverseCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (T.scaffold.mass β) :=
  T.realizesInverseXAxisLength β hβ



theorem eventually_hasInverseCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.scaffold.mass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasInverseCorrelationLength hβ



theorem hasCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.scaffold.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.mass β)⁻¹ :=
    (T.hasInverseCorrelationLength hβ).hasCorrelationLength_inv
      (T.mass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ



theorem eventually_hasCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ



def toIsingMassPowerLawTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := T.scaffold.δ
  δ_pos := T.scaffold.δ_pos
  correlationLength := T.scaffold.correlationLength
  mass := T.scaffold.mass
  mass_pos := T.mass_pos
  mass_realizes_inverse_length := T.realizesInverseXAxisLength
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.scaffold.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  mass_scaling := fun _ hβ => T.mass_scaling hβ



noncomputable def toIsingMassTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingMassAnalyticRGToExponentTarget C :=
  T.toIsingMassPowerLawTarget.toMassTarget



noncomputable def toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toIsingMassTarget.toLengthTarget



theorem toAnalyticMassBridgeInputs
    (T : IsingMassRGCoordinateBridgeInputs C) :
    RGCertificate.AnalyticMassBridgeInputs
      C T.scaffold.correlationLength T.scaffold.mass
      T.scaffold.massPrefactor
      (T.scaffold.MassCovariance ∧
        T.scaffold.CoordinateRGCovariance)
      T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry
      (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        HasInverseCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay (T.scaffold.mass β)) where
  rgCovariance := ⟨T.massCovariance, T.coordinateCovariance⟩
  stableManifoldControl := T.stableManifoldControl
  microscopicOrbitEntry := T.microscopicOrbitEntry
  subcriticalMassBridge := T.eventually_hasInverseCorrelationLength
  massPrefactor_pos := by
    simpa [Ising3DModel] using T.eventually_massPrefactor_pos
  massPrefactor_log_negligible := by
    simpa [Ising3DModel] using T.massPrefactor_log_negligible
  extractsMassPowerLaw := by
    intro _ _ _ _
    simpa [Ising3DModel] using T.eventually_mass_scaling
  extractsCorrelationLengthReciprocal := by
    intro _ _ _ _
    simpa [Ising3DModel] using
      T.eventually_correlationLength_eq_inv_mass

@[simp] theorem toIsingMassPowerLawTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.mass = T.scaffold.mass :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_massPrefactor
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.massPrefactor =
      T.scaffold.massPrefactor :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.δ = T.scaffold.δ :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_toIsingMassTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.toMassTarget =
      T.toIsingMassTarget :=
  rfl

@[simp] theorem toIsingMassTarget_toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.toLengthTarget =
      T.toIsingAnalyticTarget :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.toLengthTarget =
      T.toIsingAnalyticTarget :=
  rfl

@[simp] theorem toIsingMassTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingMassTarget_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.mass = T.scaffold.mass :=
  rfl

@[simp] theorem toIsingMassTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.δ = T.scaffold.δ :=
  rfl

@[simp] theorem toIsingAnalyticTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingAnalyticTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.δ = T.scaffold.δ :=
  rfl



theorem rgToExponentBridge
    (T : IsingMassRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge



theorem hasCriticalNu
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      C.predictedExponent :=
  T.rgToExponentBridge



theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toIsingMassPowerLawTarget
    |>.eventually_correlationLength_eq_liminfCorrelationLength



theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toIsingMassPowerLawTarget.hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.valid_of_checks hfinite htail hfixed hlinear
    hhyperbolic horbit




theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingMassPowerLawTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit



theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge_congr_predictedExponent hpred



theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      D.predictedExponent :=
  T.toIsingMassPowerLawTarget.hasCriticalNu_congr_predictedExponent hpred



theorem rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).rgToExponentBridge_liminfCorrelationLength



theorem hasCriticalNu_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      D.predictedExponent :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).hasCriticalNu_liminfCorrelationLength



theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.valid_of_checks_congr_predictedExponent hpred
    hfinite htail hfixed hlinear hhyperbolic horbit



theorem valid_of_checks_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).valid_of_checks_liminfCorrelationLength
      hfinite htail hfixed hlinear hhyperbolic horbit

end IsingMassRGCoordinateBridgeInputs

end Exact3D
end StatMech
