/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.EssSupContinuousMap
import Mathlib.MeasureTheory.Measure.Count

/-!
# Tests for the essential supremum of a continuous map

* On an abstract compact space with a measure positive on nonempty opens,
  the essential supremum of a constant map is the enorm of the constant.
* On `Fin 2` with counting measure (which is positive on nonempty opens),
  the essential supremum and the `L^∞` norm of the constant map `1` are both `1`.
* The theorem applies to a non-constant continuous map on `Fin 2`.
-/

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.EssSupContinuousMap

namespace MathlibExtTest.MeasureTheory.Function.EssSupContinuousMapTests

/-- The essential supremum of a constant map is the enorm of the constant. -/
example {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [μ.IsOpenPosMeasure] [Nonempty α]
    {E : Type*} [SeminormedAddCommGroup E] (c : E) :
    eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ := by
  have h := eLpNormEssSup_eq_enorm_continuousMap (μ := μ) (ContinuousMap.const α c)
  simp only [ContinuousMap.enorm_eq_iSup_enorm, ContinuousMap.const_apply,
    iSup_const] at h
  exact h

/-- Counting measure on `Fin 2` is positive on nonempty open sets (a test-local
instance). -/
instance : (Measure.count : Measure (Fin 2)).IsOpenPosMeasure where
  open_pos := by
    intro U _ ⟨x, hx⟩
    have hsub : ({x} : Set (Fin 2)) ⊆ U := Set.singleton_subset_iff.mpr hx
    have h1 : (1 : ℝ≥0∞) ≤ Measure.count U := by
      rw [← Measure.count_singleton x]
      exact measure_mono hsub
    exact ne_of_gt (lt_of_lt_of_le one_pos h1)

/-- On `Fin 2` with counting measure, the essential supremum of the constant `1`
map is `1`. -/
example : eLpNormEssSup (fun _ : Fin 2 => (1 : ℝ)) Measure.count = 1 := by
  have h := eLpNormEssSup_eq_enorm_continuousMap (μ := Measure.count) (ContinuousMap.const (Fin 2) (1 : ℝ))
  simp only [ContinuousMap.enorm_eq_iSup_enorm, ContinuousMap.const_apply,
    iSup_const] at h
  exact h.trans enorm_one

/-- On `Fin 2` with counting measure, the `L^∞` norm of the constant `1` map is `1`. -/
example : eLpNorm (fun _ : Fin 2 => (1 : ℝ)) ⊤ Measure.count = 1 := by
  have h := eLpNorm_top_eq_enorm_continuousMap (μ := Measure.count) (ContinuousMap.const (Fin 2) (1 : ℝ))
  simp only [ContinuousMap.enorm_eq_iSup_enorm, ContinuousMap.const_apply,
    iSup_const] at h
  exact h.trans enorm_one

/-- The theorem applies to a non-constant continuous map on `Fin 2`. -/
example : eLpNormEssSup
    (fun x : Fin 2 => if x = 0 then (2 : ℝ) else (1 : ℝ)) Measure.count =
    ‖(⟨fun x : Fin 2 => if x = 0 then (2 : ℝ) else (1 : ℝ),
      continuous_of_discreteTopology⟩ : C(Fin 2, ℝ))‖ₑ := by
  exact eLpNormEssSup_eq_enorm_continuousMap
    ⟨fun x : Fin 2 => if x = 0 then (2 : ℝ) else (1 : ℝ), continuous_of_discreteTopology⟩

end MathlibExtTest.MeasureTheory.Function.EssSupContinuousMapTests
