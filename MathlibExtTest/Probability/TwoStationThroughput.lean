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

-- The two initial jobs both start at −1/2 and finish at 1/2, so the downstream
-- station uses half a unit of initial credit and half a unit of in-window service.
example : (1 : ℝ) ≤ 1 / 2 + 1 * (1 / 2) := by
  let source : Fin 1 ↪ Fin 1 ⊕ Fin 1 := ⟨Sum.inl, Sum.inl_injective⟩
  have h := two_station_throughput_bound (t := 1 / 2) (by norm_num)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => -(1 / 2)) (fun _ _ => 1 / 2)
    source (by intro i; norm_num) (by intro i j; norm_num) (by intro i j; norm_num)
    (by intro i j k hjk; fin_cases j; fin_cases k; exact absurd hjk (lt_irrefl _))
    (fun _ _ => ⟨0⟩) (by intro j k h; cases h)
  convert h.1 1 using 1 <;> norm_num [Fin.sum_univ_succ]

private noncomputable def transferRate (i : Fin 2) : ℝ := if i = 0 then 1 / 2 else 1

private def transferStart (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then 1 else 4) else (if j = 0 then 3 else 7)

private def transferFinish (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then 3 else 6) else (if j = 0 then 4 else 8)

-- With no initial jobs, the jobs receive upstream service over [1, 3] and [4, 6],
-- then downstream service over [3, 4] and [7, 8]. The second job waits for one unit.
example : (2 : ℝ) / 8 ≤ min (1 / 2) 1 ∧ (2 : ℝ) ≤ (1 / 2) * 4 ∧ (2 : ℝ) ≤ 1 * 2 := by
  let source : Fin 2 ↪ Fin 0 ⊕ Fin 2 := ⟨Sum.inr, Sum.inr_injective⟩
  have h := two_station_throughput_bound (t := 8) (by norm_num)
    transferRate (fun _ => 0) (fun _ => 2) transferStart transferFinish source
    (by intro i; fin_cases i <;> norm_num [transferRate])
    (by intro i j; fin_cases i <;> fin_cases j <;>
        norm_num [transferRate, transferStart, transferFinish])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [transferFinish])
    (by
      intro i j k hjk
      fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hjk <;>
        norm_num [transferStart, transferFinish])
    (by intro j hj; fin_cases j <;> norm_num [transferStart] at hj)
    (by
      intro j k hjk
      change Sum.inr j = Sum.inr k at hjk
      obtain rfl := Sum.inr_injective hjk
      fin_cases j <;> norm_num [transferStart, transferFinish])
  refine ⟨?_, ?_, ?_⟩
  · convert h.2 using 1; norm_num [transferRate, show (1 : Fin 2) ≠ 0 by decide]
  · convert h.1 0 using 1; norm_num [transferRate, transferStart, transferFinish, Fin.sum_univ_succ]
  · convert h.1 1 using 1; norm_num [transferRate, transferStart, transferFinish, Fin.sum_univ_succ]

-- An empty completion list contributes neither busy time nor initial credit.
example : (0 : ℝ) / 1 ≤ min 2 1 := by
  let source : Fin 0 ↪ Fin 0 ⊕ Fin 0 := ⟨Fin.elim0, fun {j} => j.elim0⟩
  have h := two_station_throughput_bound (t := 1) (by norm_num)
    (fun i => if i = 0 then 2 else 1) (fun _ => 0) (fun _ => 0)
    (fun _ => Fin.elim0) (fun _ => Fin.elim0) source
    (by intro i; split <;> norm_num) (fun _ j => j.elim0) (fun _ j => j.elim0)
    (fun _ {j} => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
  convert h.2 using 1 <;> norm_num [show (1 : Fin 2) ≠ 0 by decide]
