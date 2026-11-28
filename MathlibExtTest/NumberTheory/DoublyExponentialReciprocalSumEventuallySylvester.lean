/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEventuallySylvester
import MathlibExt.NumberTheory.GeneralizedSylvester

/-!
# Tests for the eventual Sylvester recurrence

Prepend `4` to the Sylvester sequence. The resulting sequence of positive integers
has rational reciprocal sum `5/4`, its square ratio tends to `1`, and its weighted
defect tends to `0`. The recurrence holds after index zero but fails there. These
facts are checked directly before exercising both alternatives of the criterion.
-/

open Filter Topology MetaMathlibExt

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEventuallySylvester

local notation "s" => Nat.generalizedSylvester 1

private def a : ℕ → ℕ
  | 0 => 4
  | n + 1 => s n

private theorem a_pos : ∀ n, 0 < a n
  | 0 => by decide
  | n + 1 => Nat.generalizedSylvester_pos 1 n

private theorem s_step (n : ℕ) : (s (n + 1) : ℝ) = (s n : ℝ) ^ 2 - s n + 1 := by
  rw [Nat.generalizedSylvester_succ, Nat.cast_add,
    Nat.cast_sub (Nat.le_self_pow two_ne_zero _), Nat.cast_pow, Nat.cast_one]

private theorem s_growth (n : ℕ) : (n : ℝ) + 2 ≤ s n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have htwo : 0 ≤ (s n : ℝ) - 2 := by linarith only [ih, Nat.cast_nonneg (α := ℝ) n]
    rw [Nat.cast_succ, s_step]
    nlinarith only [ih, mul_nonneg htwo (Nat.cast_nonneg (α := ℝ) (s n))]

private theorem s_inv_limit (c : ℝ) : Tendsto (fun n => ((s n : ℝ) - c)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_mono (fun n => sub_le_sub_right (s_growth n) c)
    (by simpa only [add_sub_assoc] using
      tendsto_atTop_add_const_right _ (2 - c) tendsto_natCast_atTop_atTop)

-- The reciprocal sum is computed by telescoping from the recurrence.
private theorem a_sum : HasSum (fun n => 1 / (a n : ℝ)) ((5 / 4 : ℚ) : ℝ) := by
  have hs : HasSum (fun n => 1 / (s n : ℝ)) (1 : ℝ) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) 1).mpr ?_
    have hsum (n : ℕ) : ∑ k ∈ Finset.range n, 1 / (s k : ℝ) = 1 - ((s n : ℝ) - 1)⁻¹ := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        have hpos : (1 : ℝ) < s n := by linarith [s_growth n, Nat.cast_nonneg (α := ℝ) n]
        have hstep : (s (n + 1) : ℝ) - 1 = (s n : ℝ) * ((s n : ℝ) - 1) := by
          rw [s_step]; ring
        rw [Finset.sum_range_succ, ih, hstep]
        field_simp [(sub_pos.mpr hpos).ne', (zero_lt_one.trans hpos).ne']
        ring
    simpa only [hsum, sub_zero] using (s_inv_limit 1).const_sub 1
  apply (hasSum_nat_add_iff' 1).mp
  convert hs using 1 <;> norm_num [a]

private theorem a_ratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hz : Tendsto (fun n => (s n : ℝ)⁻¹) atTop (𝓝 0) := by simpa using s_inv_limit 0
  have h := ((hz.const_sub 1).add (hz.pow 2)).inv₀ (by norm_num)
  simp only [sub_zero, zero_pow two_ne_zero, add_zero, inv_one] at h
  refine h.congr fun n => ?_
  change (1 - (s n : ℝ)⁻¹ + ((s n : ℝ)⁻¹) ^ 2)⁻¹ = (s n : ℝ) ^ 2 / s (n + 1)
  have hs : (0 : ℝ) < s n := by exact_mod_cast Nat.generalizedSylvester_pos 1 n
  have heq : (1 - (s n : ℝ)⁻¹ + ((s n : ℝ)⁻¹) ^ 2) = s (n + 1) / (s n : ℝ) ^ 2 := by
    rw [s_step]
    field_simp [hs.ne']
  rw [heq, inv_div]

local notation "weightedDefect" => fun (n : ℕ) =>
  (∏ k ∈ Finset.range n, (a k : ℝ)) / a n * (1 - (a n : ℝ) ^ 2 / a (n + 1))

-- Independently of the criterion, the prefix product has an exact formula and the
-- weighted defect tends to zero. In particular this verifies the liminf hypothesis.
private theorem a_weighted : Tendsto weightedDefect atTop (𝓝 0) := by
  have hprod (n : ℕ) : (∏ k ∈ Finset.range (n + 1), (a k : ℝ)) = 4 * ((s n : ℝ) - 1) := by
    induction n with
    | zero => norm_num [a]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, s_step]
      change 4 * ((s n : ℝ) - 1) * s n = 4 * ((s n : ℝ) ^ 2 - s n + 1 - 1)
      ring
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hWeight (n : ℕ) : (∏ k ∈ Finset.range (n + 1), (a k : ℝ)) / a (n + 1) =
      4 * (1 - (s n : ℝ)⁻¹) := by
    rw [hprod]
    change 4 * ((s n : ℝ) - 1) / s n = 4 * (1 - (s n : ℝ)⁻¹)
    have hs : (s n : ℝ) ≠ 0 := by exact_mod_cast (Nat.generalizedSylvester_pos 1 n).ne'
    field_simp [hs]
  have hWeightLim : Tendsto (fun n => 4 * (1 - (s n : ℝ)⁻¹)) atTop (𝓝 4) := by
    simpa using ((s_inv_limit 0).const_sub 1).const_mul 4
  rw [show (0 : ℝ) = 4 * (1 - 1) by norm_num]
  exact (hWeightLim.mul ((a_ratio.comp (tendsto_add_atTop_nat 1)).const_sub 1)).congr
    (fun n => by simp only [hWeight, Function.comp_apply])

-- Exact agreement with the recurrence after the extra first term, proved without the criterion.
private theorem a_recurrence : ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1 := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n => exact Nat.generalizedSylvester_succ 1 n

example : a 1 < a 0 ^ 2 - a 0 + 1 := by
  norm_num [a]

example : (weightedDefect) 1 = -(2 / 3 : ℝ) := by
  norm_num [a, Finset.prod_range_succ]

-- Clients exercising the two alternative hypotheses on this concrete sequence.
example : ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1 := by
  refine eventually_sylvester_recurrence_of_rational_sum a_pos a_ratio ⟨5 / 4, a_sum⟩ (.inl ?_)
  intro δ hδ
  exact (a_weighted.eventually (eventually_gt_nhds (neg_neg_of_pos hδ))).mono fun _ hn => hn.le

example : ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1 :=
  eventually_sylvester_recurrence_of_rational_sum a_pos a_ratio ⟨5 / 4, a_sum⟩
    (.inr (a_recurrence.mono fun _ hn => hn.ge))

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEventuallySylvester
