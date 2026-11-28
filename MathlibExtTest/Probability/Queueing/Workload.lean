/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Queueing.Workload
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq

open Filter MetaMathlibExt.Queueing

namespace MetaMathlibExtTest.Queueing

-- Two arrivals at time 1, one at time 9, and zero-demand arrivals from time 14 onward.
private def sampleArrival : ℕ → ℝ
  | 0 | 1 => 1
  | 2 => 9
  | n + 3 => (n : ℝ) + 14

private def sampleDemand : ℕ → ℝ
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | _ + 3 => 0

private def samplePostwork : ℕ → ℝ
  | 0 | 2 => 4
  | 1 => 6
  | _ + 3 => 0

private noncomputable def sampleWorkload (t : ℝ) : ℝ :=
  if t < 1 then max 0 (2 - t)
  else if t < 9 then max 0 (6 - (t - 1))
  else max 0 (4 - (t - 9))

private lemma sampleArrival_mono : Monotone sampleArrival := by
  apply monotone_nat_of_le_succ
  intro n
  rcases n with _ | _ | _ | n
  · norm_num [sampleArrival]
  · norm_num [sampleArrival]
  · norm_num [sampleArrival]
  · simp only [sampleArrival, Nat.cast_succ]
    linarith

-- Check that the independently specified functions satisfy every local workload law.
example : IsWorkConservingTrace sampleArrival sampleDemand 2 samplePostwork sampleWorkload where
  arrival_mono := sampleArrival_mono
  arrival_zero_nonneg := by norm_num [sampleArrival]
  arrival_tendsto := by
    apply tendsto_atTop_atTop.mpr
    intro r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n + 3, fun k hk => ?_⟩
    have h : (n : ℝ) + 14 ≤ sampleArrival k := sampleArrival_mono hk
    linarith
  initial_nonneg := by norm_num
  demand_nonneg := by
    intro n
    rcases n with _ | _ | _ | n <;> norm_num [sampleDemand]
  postwork_zero := by norm_num [sampleArrival, sampleDemand, samplePostwork, max_def]
  postwork_succ := by
    intro n
    rcases n with _ | _ | _ | n
    · norm_num [sampleArrival, sampleDemand, samplePostwork, max_def]
    · norm_num [sampleArrival, sampleDemand, samplePostwork, max_def]
    · norm_num [sampleArrival, sampleDemand, samplePostwork, max_def]
    · simp only [sampleArrival, sampleDemand, samplePostwork, Nat.cast_succ, add_zero]
      exact (max_eq_left (by linarith)).symm
  workload_before_first := by
    intro t _ ht
    exact ite_eq_left ht
  workload_on_gap := by
    intro n t hlo hhi
    rcases n with _ | _ | _ | n
    · exact ((not_lt_of_ge hlo) hhi).elim
    · change (1 : ℝ) ≤ t at hlo
      change t < (9 : ℝ) at hhi
      simp only [sampleArrival, samplePostwork, sampleWorkload,
        ite_eq_right (not_lt_of_ge hlo), ite_eq_left hhi]
    · change (9 : ℝ) ≤ t at hlo
      have h₁ : ¬ t < (1 : ℝ) := by linarith
      simp only [sampleArrival, samplePostwork, sampleWorkload,
        ite_eq_right h₁, ite_eq_right (not_lt_of_ge hlo)]
    · simp only [sampleArrival, samplePostwork] at hlo ⊢
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have h₁ : ¬ t < (1 : ℝ) := by linarith
      have h₉ : ¬ t < (9 : ℝ) := by linarith
      have hleft : (4 : ℝ) - (t - 9) ≤ 0 := by linarith
      have hright : (0 : ℝ) - (t - ((n : ℝ) + 14)) ≤ 0 := by linarith
      simp only [sampleWorkload, ite_eq_right h₁, ite_eq_right h₉,
        max_eq_left hleft, max_eq_left hright]

example : sampleWorkload 0 = 2 := by
  norm_num [sampleWorkload, max_def]

-- The intermediate postwork at the first tie is not the real-time observation.
example : samplePostwork 0 = 4 ∧ samplePostwork 1 = 6 ∧ sampleWorkload 1 = 6 := by
  norm_num [samplePostwork, sampleWorkload, max_def]

-- The work depletes at 7, stays at zero on [7, 9), and jumps to 4 at 9.
example (t : ℝ) (hlo : 7 ≤ t) (hhi : t < 9) : sampleWorkload t = 0 := by
  have h₁ : ¬ t < (1 : ℝ) := by linarith
  have hzero : (6 : ℝ) - (t - 1) ≤ 0 := by linarith
  simp only [sampleWorkload, ite_eq_right h₁, ite_eq_left hhi, max_eq_left hzero]

example : sampleWorkload 9 = 4 ∧ sampleWorkload 10 = 3 := by
  norm_num [sampleWorkload, max_def]

end MetaMathlibExtTest.Queueing
