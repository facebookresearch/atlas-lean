/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.TwoStationThroughput
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Examples for throughput of a two-station serial line -/

open MetaMathlibExt

-- A half-served initial job at each station can finish in a half-unit window.
example : (1 : ℝ) ≤ 1 / 2 + 1 * (1 / 2) := by
  have h := two_station_throughput_bound (t := 1 / 2) (by norm_num)
    (fun _ => 1) (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (by intro i; norm_num) (by intro i; norm_num) (by intro i j; norm_num)
    (by intro i; norm_num [Fin.sum_univ_succ]) (fun _ => le_rfl) (by decide)
  simpa only [Nat.cast_one] using h.1 1

-- The aggregate accounting hypotheses permit equality with the upstream rate.
-- These counts do not describe a realizable serial-line service history.
example : (2 : ℝ) / 2 ≤ min 1 2 := by
  let μ (i : Fin 2) : ℝ := if i = 0 then 1 else 2
  have hp : ∀ i, 0 < μ i := by
    intro i
    fin_cases i <;> norm_num [μ]
  have hb : ∀ i : Fin 2, (∑ j : Fin 2, (if j.val = 0 then 1 - (0 : ℝ) else 1) * (1 / μ i)) ≤ 2 := by
    intro i
    fin_cases i <;> norm_num [μ, Fin.sum_univ_succ]
  have h := two_station_throughput_bound (t := 2) (by norm_num)
    μ (fun _ => 0) (fun _ => 2) (fun _ => 0) (fun _ => 2) (fun i _ => 1 / μ i)
    hp (by intro i; norm_num) (fun _ _ => le_rfl) hb (fun _ => le_rfl) (by decide)
  simpa only [μ, ite_eq_left rfl, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), Nat.cast_ofNat,
    Nat.cast_zero, add_zero, zero_div] using h.2
