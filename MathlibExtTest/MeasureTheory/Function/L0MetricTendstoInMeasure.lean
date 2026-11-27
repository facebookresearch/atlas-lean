/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.L0MetricTendstoInMeasure

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted
open scoped Topology

private noncomputable def outsideRep : L0UnitInterval :=
  ⟨(Icc (2 : ℝ) 3).indicator (fun _ => 1), measurable_const.indicator measurableSet_Icc⟩

private def zeroRep : L0UnitInterval := ⟨fun _ => 0, measurable_const⟩

-- The representatives differ on a positive-measure interval outside [0,1].
example : Tendsto (fun _ : ℕ => L0PseudoMetric outsideRep zeroRep) atTop (𝓝 0) := by
  apply (tendsto_L0PseudoMetric_zero_iff_tendstoInMeasure (fun _ => outsideRep) zeroRep).2
  let : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  apply tendstoInMeasure_of_tendsto_ae (fun _ => outsideRep.2.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := volume) (s := Icc (0 : ℝ) 1) measurableSet_Icc] with x hx
  have hx' : x ∉ Icc (2 : ℝ) 3 := fun hm => (not_le_of_gt (by norm_num : (1 : ℝ) < 2))
    (hm.1.trans hx.2)
  simpa only [outsideRep, zeroRep, indicator_of_notMem hx'] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
