/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.Certificate
import Code.Exact3D.FiniteDimensionalRG
import Code.Exact3D.Intervals
import Code.Exact3D.MatrixCertificate
import Code.Exact3D.RGBridgeCriteria










namespace StatMech
namespace Exact3D


def hierarchicalScale : BlockScale where
  L := 2
  one_lt := by norm_num


def hierarchicalThermalEigenvalue : ℝ :=
  3


noncomputable def hierarchicalStableEigenvalue : ℝ :=
  (1 : ℝ) / 2

theorem hierarchical_thermal_gt_one : 1 < hierarchicalThermalEigenvalue := by
  norm_num [hierarchicalThermalEigenvalue]

theorem hierarchical_stable_abs_lt_one : |hierarchicalStableEigenvalue| < 1 := by
  norm_num [hierarchicalStableEigenvalue]



abbrev hierarchicalHamiltonianSpace : EffectiveHamiltonian where
  carrier := ℝ × ℝ


noncomputable def hierarchicalRGMap : BlockSpinMap hierarchicalHamiltonianSpace where
  scale := hierarchicalScale
  map := fun x => (hierarchicalThermalEigenvalue * x.1,
    hierarchicalStableEigenvalue * x.2)


noncomputable def hierarchicalFixedPointData :
    RGFixedPointData hierarchicalHamiltonianSpace hierarchicalRGMap where
  fixedPoint := (0, 0)
  fixedPoint_eq := by simp [hierarchicalRGMap]
  thermalEigenvalue := hierarchicalThermalEigenvalue
  thermal_gt_one := hierarchical_thermal_gt_one




noncomputable def HierarchicalModel : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def hierarchicalCertificate : RGCertificate HierarchicalModel where
  H := hierarchicalHamiltonianSpace
  R := hierarchicalRGMap
  fixedPointData := hierarchicalFixedPointData


noncomputable def hierarchicalNu : ℝ :=
  hierarchicalCertificate.predictedExponent



noncomputable def hierarchicalCorrelationLength (β : ℝ) : ℝ :=
  Real.exp (-hierarchicalNu * Real.log (-β))


noncomputable def hierarchicalLinearization : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => hierarchicalThermalEigenvalue
  | ⟨1, _⟩, ⟨1, _⟩ => hierarchicalStableEigenvalue
  | _, _ => 0


def hierarchicalLinearizationIntervals : RatInterval.IntervalMatrix 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => RatInterval.point 3
  | ⟨1, _⟩, ⟨1, _⟩ => RatInterval.point (1 / 2)
  | _, _ => RatInterval.point 0


noncomputable def hierarchicalStableLinearization : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => hierarchicalStableEigenvalue


def hierarchicalStableLinearizationIntervals : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point (1 / 2)


theorem hierarchicalLinearization_mem_intervals :
    RatInterval.MatrixMem hierarchicalLinearization hierarchicalLinearizationIntervals := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchicalLinearization, hierarchicalLinearizationIntervals,
      hierarchicalThermalEigenvalue, hierarchicalStableEigenvalue,
      RatInterval.point, RatInterval.MemR]


theorem hierarchicalStableLinearization_mem_intervals :
    RatInterval.MatrixMem hierarchicalStableLinearization
      hierarchicalStableLinearizationIntervals := by
  intro i j
  fin_cases i
  fin_cases j
  simp [hierarchicalStableLinearization, hierarchicalStableLinearizationIntervals,
    hierarchicalStableEigenvalue, RatInterval.point, RatInterval.MemR]


def hierarchicalStableRowSumContraction :
    RatInterval.RowSumContraction hierarchicalStableLinearizationIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, hierarchicalStableLinearizationIntervals,
      RatInterval.point, RatInterval.absUpper]


theorem hierarchicalStableLinearization_apply_bound (x : Fin 1 → ℝ) (i : Fin 1) :
    |RatInterval.matVec hierarchicalStableLinearization x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [hierarchicalStableRowSumContraction] using
    hierarchicalStableRowSumContraction.apply_bound
      hierarchicalStableLinearization_mem_intervals x i


structure HierarchicalFiniteCertificate where
  linearization : Fin 2 → Fin 2 → ℝ
  enclosure : RatInterval.IntervalMatrix 2 2
  enclosure_sound : RatInterval.MatrixMem linearization enclosure
  stable_linearization : Fin 1 → Fin 1 → ℝ
  stable_enclosure : RatInterval.IntervalMatrix 1 1
  stable_enclosure_sound : RatInterval.MatrixMem stable_linearization stable_enclosure
  stable_coordinate : |hierarchicalStableEigenvalue| < 1
  stable_row_sum_contraction : RatInterval.RowSumContraction stable_enclosure


noncomputable def hierarchicalFiniteCertificate : HierarchicalFiniteCertificate where
  linearization := hierarchicalLinearization
  enclosure := hierarchicalLinearizationIntervals
  enclosure_sound := hierarchicalLinearization_mem_intervals
  stable_linearization := hierarchicalStableLinearization
  stable_enclosure := hierarchicalStableLinearizationIntervals
  stable_enclosure_sound := hierarchicalStableLinearization_mem_intervals
  stable_coordinate := hierarchical_stable_abs_lt_one
  stable_row_sum_contraction := hierarchicalStableRowSumContraction



noncomputable def hierarchicalStableBlock : StableBlockWithRemainder 1 :=
  StableBlockWithRemainder.ofLinearRowSum hierarchicalStableLinearization
    hierarchicalStableLinearization_mem_intervals
    hierarchicalStableRowSumContraction




noncomputable def hierarchicalFiniteSplitting : FiniteHyperbolicSplitting 1 :=
  FiniteHyperbolicSplitting.ofLinearStableRowSum
    (n := 1) (thermal := hierarchicalThermalEigenvalue)
    hierarchical_thermal_gt_one hierarchicalStableLinearization
    hierarchicalStableLinearization_mem_intervals
    hierarchicalStableRowSumContraction (by
      norm_num [hierarchicalThermalEigenvalue, hierarchicalStableRowSumContraction])


noncomputable def hierarchicalFiniteSplittingCertificate :
    RGCertificate HierarchicalModel :=
  hierarchicalFiniteSplitting.certificate hierarchicalScale HierarchicalModel



theorem hierarchicalFiniteSplitting_predictedExponent_eq :
    hierarchicalFiniteSplittingCertificate.predictedExponent = hierarchicalNu := by
  rfl



theorem hierarchicalFiniteSplitting_fixedPointEnclosure :
    hierarchicalFiniteSplittingCertificate.FixedPointEnclosure :=
  hierarchicalFiniteSplitting.certificate_fixedPointEnclosure hierarchicalScale
    HierarchicalModel



theorem hierarchical_logSlope_eq_nu_of_mem {β : ℝ} (hβ : β ∈ Set.Ioo (-1) 0) :
    logSlope HierarchicalModel hierarchicalCorrelationLength β = hierarchicalNu := by
  have hβ_pos : 0 < -β := by linarith [hβ.2]
  have hβ_lt_one : -β < 1 := by linarith [hβ.1]
  have hlog_ne : Real.log (-β) ≠ 0 :=
    (Real.log_neg hβ_pos hβ_lt_one).ne
  have hlogβ_ne : Real.log β ≠ 0 := by
    simpa [Real.log_neg_eq_log] using hlog_ne
  simp [logSlope, HierarchicalModel, hierarchicalCorrelationLength]
  field_simp [hlogβ_ne]



theorem hierarchical_hasCriticalNu :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength hierarchicalNu := by
  unfold HasCriticalNu
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with β hβ
  exact (hierarchical_logSlope_eq_nu_of_mem hβ).symm



theorem hierarchical_bridge_via_exact_power :
    hierarchicalCertificate.RGToExponentBridge hierarchicalCorrelationLength := by
  refine hierarchicalCertificate.rgToExponentBridge_of_exact_power_on_Ioo
    hierarchicalCorrelationLength 1 (by norm_num) ?_
  intro β hβ
  simp [hierarchicalCorrelationLength, hierarchicalNu, HierarchicalModel]




theorem hierarchicalFiniteSplitting_bridge :
    hierarchicalFiniteSplittingCertificate.RGToExponentBridge
      hierarchicalCorrelationLength := by
  simpa [RGCertificate.RGToExponentBridge,
    hierarchicalFiniteSplitting_predictedExponent_eq] using hierarchical_hasCriticalNu




theorem hierarchicalFiniteSplittingCertificate_valid :
    hierarchicalFiniteSplittingCertificate.Valid hierarchicalCorrelationLength := by
  refine ⟨trivial, trivial, hierarchicalFiniteSplitting_fixedPointEnclosure,
    ?_, ?_, trivial, hierarchicalFiniteSplitting_bridge⟩
  · exact
      hierarchicalFiniteSplittingCertificate.linearizationEnclosure_of_thermal_gt_one
  · exact hierarchicalFiniteSplittingCertificate.hyperbolicSplitting_of_thermal_gt_one


theorem hierarchicalCertificate_valid :
    hierarchicalCertificate.Valid hierarchicalCorrelationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact hierarchicalFixedPointData.fixedPoint_eq
  · exact hierarchicalCertificate.linearizationEnclosure_of_thermal_gt_one
  · exact hierarchicalCertificate.hyperbolicSplitting_of_thermal_gt_one
  · exact hierarchical_bridge_via_exact_power



theorem hierarchical_hasCriticalNu_eq_log_scale_div_log_thermal :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
      (Real.log hierarchicalCertificate.scale.toReal /
        Real.log hierarchicalCertificate.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    hierarchicalCertificate_valid.hasCriticalNu

end Exact3D
end StatMech
