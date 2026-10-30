/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant.lean` and
`P2M/Sol/S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Inversion invariance of right-invariant Haar measures

A right-invariant Haar measure on a locally compact second countable group
is invariant under inversion: the inverse measure is a left-invariant Haar
measure, hence a scalar multiple of the original, and the scalar is forced
to be `1` by involutivity.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

/-- A right-invariant Haar measure is invariant under inversion. -/
theorem MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  constructor
  set c : ℝ≥0 := Measure.haarScalarFactor μ.inv μ with hc_def
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hc' : μ.inv = (c : ℝ≥0∞) • μ := by rw [hc]; rfl
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = ((c : ℝ≥0∞) ^ 2) • μ := by
    rw [← Measure.inv_def μ, hc',
      Measure.map_smul _ continuous_inv.measurable.aemeasurable, ← Measure.inv_def μ, hc',
      smul_smul, pow_two]
  have μeq : μ = ((c : ℝ≥0∞) ^ 2) • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have h3 : (c : ℝ≥0∞) ^ 2 * μ K₀ = 1 ^ 2 * μ K₀ := by
    conv_rhs => rw [μeq]
    simp
  have hK₀ : 0 < μ (K₀ : Set G) :=
    (isOpen_interior.measure_pos μ K₀.interior_nonempty).trans_le (measure_mono interior_subset)
  have h4 : (c : ℝ≥0∞) ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj hK₀.ne' K₀.isCompact.measure_lt_top.ne).1 h3
  have h5 : (c : ℝ≥0∞) = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc', h5, one_smul]
