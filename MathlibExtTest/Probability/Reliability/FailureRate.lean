/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.FailureRate
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

private noncomputable def pointTail (s : ℝ) : ℝ :=
  (Measure.dirac (2 : ℝ)).real {x | s < x}

private theorem pointTail_eq (s : ℝ) : pointTail s = if s < 2 then 1 else 0 := by
  classical
  by_cases h : s < 2 <;> simp [pointTail, Measure.real, Measure.dirac_apply, h]

private theorem point_ifr (u : ℝ) (_hu : 0 ≤ u) :
    AntitoneOn (fun s => pointTail (s + u) / pointTail s) {s | 0 ≤ s ∧ 0 < pointTail s} := by
  intro a ha b hb hab
  change 0 ≤ a ∧ 0 < pointTail a at ha
  change 0 ≤ b ∧ 0 < pointTail b at hb
  have pos_age (s : ℝ) (h : 0 < pointTail s) : s < 2 := by
    by_contra! hn
    rw [pointTail_eq, ite_eq_right (not_lt.mpr hn)] at h
    exact (lt_irrefl _) h
  have ha' := pos_age a ha.2
  have hb' := pos_age b hb.2
  change pointTail (b + u) / pointTail b ≤ pointTail (a + u) / pointTail a
  by_cases hbu : b + u < 2
  · have hau := lt_of_le_of_lt (add_le_add hab (le_refl u)) hbu
    simp [pointTail_eq, ha', hb', hau, hbu]
  · by_cases hau : a + u < 2 <;> simp [pointTail_eq, ha', hb', hau, hbu]

private theorem point_nbu : ∀ s ≥ 0, ∀ t ≥ 0,
    pointTail (s + t) ≤ pointTail s * pointTail t := by
  have hpos : ∀ᵐ x ∂Measure.dirac (2 : ℝ), 0 < (fun x : ℝ => x) x :=
    (ae_dirac_iff (measurableSet_lt measurable_const measurable_id)).2 (by norm_num)
  exact increasingFailureRate_implies_newBetterThanUsed _ (fun x : ℝ => x) measurable_id hpos
    point_ifr

-- Positive survival at both ages, but not at their sum.
example : pointTail (1 + 1) < pointTail 1 * pointTail 1 := by
  have h := point_nbu 1 (by norm_num) 1 (by norm_num)
  norm_num [pointTail_eq] at h ⊢

-- At the endpoint the conditioning survival is zero; the conclusion still holds.
example : pointTail (2 + 1) = pointTail 2 * pointTail 1 := by
  exact le_antisymm (point_nbu 2 (by norm_num) 1 (by norm_num)) (by norm_num [pointTail_eq])

private theorem exp_tail {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure r).real {x | t < x} = Real.exp (-(r * t)) := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  change (expMeasure r).real (Set.Ioi t) = _
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq hr]
  simp [ht]

-- The exponential law is the equality case, including age zero.
example {r s t : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expMeasure r).real {x | s + t < x} =
      (expMeasure r).real {x | s < x} * (expMeasure r).real {x | t < x} := by
  rw [exp_tail hr (add_nonneg hs ht), exp_tail hr hs, exp_tail hr ht, ← Real.exp_add]
  congr 1
  ring
