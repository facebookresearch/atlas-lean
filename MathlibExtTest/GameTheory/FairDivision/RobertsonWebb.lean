/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.FairDivision.RobertsonWebb
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Set
open MathlibExt.GameTheory.FairDivision.RobertsonWebb

-- Boundary: target `0` returns the start point (leftmost convention).
example (V : RWValuation) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (V.eval x 1)) : V.cut x 0 hx h0 = x := by
  have h := V.cut_spec x 0 hx h0
  refine le_antisymm (h.2 ⟨⟨le_rfl, hx.2⟩, ?_⟩) h.1.1.1
  simp [RWValuation.eval, MeasureTheory.measureReal_empty]

-- Exactness of the admissible range: a target outside `[0, eval x 1]` is
-- never attained on `[x, 1]`.
example (V : RWValuation) {x α : ℝ} (hα : α ∉ Icc (0 : ℝ) (V.eval x 1)) :
    ¬ ∃ z ∈ Icc x 1, V.eval x z = α := by
  rintro ⟨z, hz, rfl⟩
  have := V.probability
  exact hα ⟨MeasureTheory.measureReal_nonneg, MeasureTheory.measureReal_mono (Ioc_subset_Ioc_right hz.2)⟩

-- Non-vacuity: Lebesgue measure on `[0, 1]` is a Robertson–Webb valuation.
noncomputable example : RWValuation where
  measure := volume.restrict (Icc (0 : ℝ) 1)
  probability := ⟨by simp⟩
  supported := by
    rw [Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self, measure_empty]
  nullSingleton := inferInstance

-- Non-vacuity of the normalization hypothesis: one interval `(0, 1]` of
-- height one has mass one on the cake.
example : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
    ((⟨fun _ => 0, fun _ => 1, fun _ => 1⟩ : PiecewiseConstantDensity 1).density t)) = 1 := by
  have h : ∀ t, ENNReal.ofReal
      ((⟨fun _ => 0, fun _ => 1, fun _ => 1⟩ : PiecewiseConstantDensity 1).density t)
      = (Ioc (0 : ℝ) 1).indicator 1 t := by
    intro t
    simp only [PiecewiseConstantDensity.density, Fin.sum_univ_one]
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  simp_rw [h]
  rw [lintegral_indicator_one measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Icc_self, Real.volume_Ioc]
  simp

-- The least cut attains its target and lies in the cake.
example (V : RWValuation) {x α : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hα : α ∈ Icc (0 : ℝ) (V.eval x 1)) :
    V.eval x (V.cut x α hx hα) = α ∧ V.cut x α hx hα ∈ Icc x 1 :=
  ⟨(V.cut_spec x α hx hα).1.2, (V.cut_spec x α hx hα).1.1⟩
