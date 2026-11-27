/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Separations.CrosscurrentExtraction
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Domains.Chemistry.Separations.CrosscurrentExtraction

-- Three identical stages each halve the amount; eight units leave one unit.
example : (8 : ℝ) * (1 / 2) ^ (3 : ℕ) = 1 := by
  let q (k : ℕ) : ℝ := 8 * (1 / 2) ^ k
  let cr (k : ℕ) : ℝ := q k / 4
  let cs (k : ℕ) : ℝ := 2 * cr k
  have h := crosscurrent_amounts 3 2 1 2 (by norm_num) (by norm_num) (by norm_num) q cr cs
    (fun _ _ => rfl) (by intro k _; dsimp only [cr, cs]; ring)
    (by intro k _; dsimp only [q, cr]; rw [pow_succ]; ring)
  have hq := h.2.2.1 3 le_rfl
  change q 3 = q 0 * ((1 + 2 * (1 / 2))⁻¹) ^ (3 : ℕ) at hq
  have hfinal : q 0 * ((1 + 2 * (1 / 2))⁻¹) ^ (3 : ℕ) = 1 := by norm_num [q]
  exact hq.trans hfinal

-- With no stages, the remaining fraction of a positive feed is one.
example (q : ℕ → ℝ) (hq : 0 < q 0) : q 0 / q 0 = 1 := by
  have h := crosscurrent_amounts 0 2 1 2 (by norm_num) (by norm_num) (by norm_num) q
    (fun _ => 0) (fun _ => 0) (fun _ hk => (Nat.not_lt_zero _ hk).elim)
    (fun _ hk => (Nat.not_lt_zero _ hk).elim) (fun _ hk => (Nat.not_lt_zero _ hk).elim)
  simpa only [pow_zero] using h.2.2.2.1 hq

-- Zero initial solute needs no ratio, even with a positive number of stages.
example : (fun _ : ℕ => (0 : ℝ)) 2 = 0 := by
  have h := crosscurrent_amounts 2 2 1 2 (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
  exact h.2.2.2.2 rfl
