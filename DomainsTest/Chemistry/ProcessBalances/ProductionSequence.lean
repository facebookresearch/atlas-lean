/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.ProcessBalances.ProductionSequence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for a two-stage production sequence -/

open Chemistry.ProcessBalances MeasureTheory Set
open scoped BigOperators

private def times : Fin 3 → ℝ := ![0, 1, 3]

private lemma times_strictMono : StrictMono times := by
  rw [Fin.strictMono_iff_lt_succ]
  intro k
  fin_cases k
  · change (0 : ℝ) < 1
    norm_num
  · change (1 : ℝ) < 3
    norm_num

-- A continuous cumulative amount with a nonzero initial value and a kink at time 1.
private def cumulative (a x : ℝ) : ℝ := 7 + a * x + 3 * max (x - 1) 0

private lemma cumulative_continuous (a : ℝ) : Continuous (cumulative a) :=
  (continuous_const.add (continuous_id.const_mul a)).add
    (((continuous_id.sub continuous_const).max continuous_const).const_mul 3)

private lemma cumulative_deriv_before (a : ℝ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (cumulative a) a x := by
  apply ((hasDerivAt_const_mul a).const_add 7).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp [cumulative, max_eq_right (sub_nonpos.mpr (show y < 1 from hy).le)]

private lemma cumulative_deriv_after (a : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (cumulative a) (a + 3) x := by
  have h : HasDerivAt (fun y : ℝ ↦ 3 * (y - 1)) 3 x := by
    simpa only [mul_one] using ((hasDerivAt_id' x).sub_const 1).const_mul 3
  apply (((hasDerivAt_const_mul a).const_add 7).add h).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp [cumulative, max_eq_left (sub_nonneg.mpr (show 1 < y from hy).le)]

private lemma rates_nonneg (a : ℝ) (ha : 0 ≤ a) : ∀ k : Fin 2, 0 ≤ (![a, a + 3] : Fin 2 → ℝ) k := by
  intro k
  fin_cases k
  · exact ha
  · exact add_nonneg ha (by norm_num)

private lemma cumulative_deriv (a : ℝ) (k : Fin 2) (x : ℝ)
    (hx : x ∈ Ioo (times k.castSucc) (times k.succ)) :
    HasDerivAt (cumulative a) ((![a, a + 3] : Fin 2 → ℝ) k) x := by
  fin_cases k
  · exact cumulative_deriv_before a hx.2
  · exact cumulative_deriv_after a hx.1

-- The article's rates 2 and 5 give 12 units, not the final cumulative reading of 19.
example : cumulative 2 3 - cumulative 2 0 = 12 ∧
    (9 : ℝ) ≤ cumulative 2 3 - cumulative 2 0 ∧
    (3 : ℝ) ≤ cumulative 2 3 - cumulative 2 0 := by
  have h := processedAmount_and_idleEnergy times rfl times_strictMono ![2, 2 + 3]
    (rates_nonneg 2 (by norm_num)) (cumulative 2) (cumulative_continuous 2).continuousOn
    (cumulative_deriv 2)
  have hAmount : cumulative 2 3 - cumulative 2 0 = 12 := by
    calc
      _ = _ := h.1
      _ = 12 := by
        rw [Fin.sum_univ_two]
        change (2 : ℝ) * (1 - 0) + (2 + 3) * (3 - 1) = 12
        norm_num
  refine ⟨hAmount, h.2.1 9 3 (by norm_num) (by norm_num) ?_⟩
  change (9 : ℝ) + 3 = cumulative 2 3 - cumulative 2 0
  rw [hAmount]
  norm_num

-- Only the first stage is idle. The active stage is longer and draws no power.
example : (4 : ℝ) ≤ ∫ x in (0 : ℝ)..3, (Ioo 0 1).indicator (fun _ ↦ (4 : ℝ)) x := by
  let P : ℝ → ℝ := (Ioo 0 1).indicator (fun _ ↦ (4 : ℝ))
  have hInt : IntervalIntegrable P volume 0 3 :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_const (c := (4 : ℝ))).def'.indicator
      measurableSet_Ioo)
  let rate : Fin 2 → ℝ := ![0, 0 + 3]
  have h := processedAmount_and_idleEnergy times rfl times_strictMono rate
    (rates_nonneg 0 le_rfl) (cumulative 0) (cumulative_continuous 0).continuousOn
    (cumulative_deriv 0)
  have hIdle (k : Fin 2) (hk : rate k = 0) (x : ℝ)
      (hx : x ∈ Ioo (times k.castSucc) (times k.succ)) : (4 : ℝ) ≤ P x := by
    fin_cases k
    · rw [show P x = 4 from indicator_of_mem hx _]
    · change (0 : ℝ) + 3 = 0 at hk
      norm_num at hk
  have hActive (k : Fin 2) (_ : 0 < rate k) (x : ℝ)
      (_ : x ∈ Ioo (times k.castSucc) (times k.succ)) : 0 ≤ P x :=
    indicator_nonneg (fun _ _ ↦ by norm_num) _
  have hBound := h.2.2 P 4 hInt (by norm_num) hIdle hActive
  rw [Fin.sum_univ_two] at hBound
  rw [indicator_of_mem (show (0 : Fin 2) ∈ {k | rate k = 0} from rfl),
    indicator_of_notMem (show (1 : Fin 2) ∉ {k | rate k = 0} by
      change ¬ ((0 : ℝ) + 3 = 0)
      norm_num)] at hBound
  change (4 : ℝ) * ((1 - 0) + 0) ≤ ∫ x in (0 : ℝ)..3, P x at hBound
  simpa using hBound

-- With zero production on both stages, the bound still charges the full three time units;
-- the integrable power can drop below idle power at the joining time itself.
example : ((7 : ℝ) - 7 = 0) ∧
    (12 : ℝ) ≤ ∫ x in (0 : ℝ)..3, ({1} : Set ℝ)ᶜ.indicator (fun _ ↦ (4 : ℝ)) x := by
  let P : ℝ → ℝ := ({1} : Set ℝ)ᶜ.indicator (fun _ ↦ (4 : ℝ))
  have hInt : IntervalIntegrable P volume 0 3 :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_const (c := (4 : ℝ))).def'.indicator
      (measurableSet_singleton 1).compl)
  have h := processedAmount_and_idleEnergy times rfl times_strictMono (fun _ ↦ 0)
    (fun _ ↦ le_rfl) (fun _ ↦ 7) continuous_const.continuousOn
    (fun _ x _ ↦ hasDerivAt_const x (7 : ℝ))
  have hIdle (k : Fin 2) (_ : (0 : ℝ) = 0) (x : ℝ)
      (hx : x ∈ Ioo (times k.castSucc) (times k.succ)) : (4 : ℝ) ≤ P x := by
    have hx1 : x ≠ 1 := by
      fin_cases k
      · exact (show x < 1 from hx.2).ne
      · exact (show 1 < x from hx.1).ne'
    rw [show P x = 4 from indicator_of_mem hx1 _]
  refine ⟨h.1.trans ?_, ?_⟩
  · simp
  have hBound := h.2.2 P 4 hInt (by norm_num) hIdle (fun _ hk ↦ False.elim ((lt_irrefl 0) hk))
  have hAll : {j : Fin 2 | (0 : ℝ) = 0} = univ := by simp
  rw [hAll, indicator_univ, Fin.sum_univ_two] at hBound
  change (4 : ℝ) * ((1 - 0) + (3 - 1)) ≤ ∫ x in (0 : ℝ)..3, P x at hBound
  norm_num at hBound
  exact hBound
