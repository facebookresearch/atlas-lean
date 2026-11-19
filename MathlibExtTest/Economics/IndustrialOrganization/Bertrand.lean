/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IndustrialOrganization.Bertrand
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace MathlibExtTest.Economics.Bertrand

open MathlibExt.Economics.Bertrand

/-- With unit demand and cost 2, both firms pricing at 2 is an equilibrium. -/
theorem test_marginalCost_unitDemand : IsBertrandNash 2 (fun _ => 1) (fun _ => 2) := by
  exact isBertrandNash_marginalCost (fun _ => zero_le_one)

/-- At a tie at price 3, firm 0 sells half the unit demand: profit 1/2. -/
theorem test_tie_profit : bertrandProfit 2 (fun _ => 1) ![3, 3] 0 = 1 / 2 := by
  unfold bertrandProfit bertrandQuantity
  split_ifs with h1 h2
  · simp_all
  · simp_all
    norm_num
  · simp_all

/-- Undercutting to 11/4 against 3 earns 3/4, more than the tie profit. -/
theorem test_undercut_profit : bertrandProfit 2 (fun _ => 1) ![11 / 4, 3] 0 = 3 / 4 := by
  have hr0 : (0 : Fin 2).rev = 1 := by decide
  unfold bertrandProfit bertrandQuantity
  split_ifs with h1 h2
  · simp_all
    norm_num
  · simp [hr0] at h1
    norm_num at h1
  · simp [hr0] at h1
    norm_num at h1

/-- Both firms pricing at 3 above cost 2 is not an equilibrium. -/
theorem test_above_cost_not_nash : ¬ IsBertrandNash 2 (fun _ => 1) (fun _ => 3) := by
  have hiff := isBertrandNash_iff (c := 2) (D := fun _ => 1)
    (fun _ => one_pos) antitone_const (fun _ => 3)
  rw [hiff]
  intro h
  have h3 := congrFun h (0 : Fin 2)
  norm_num at h3

/-- With zero demand every profile is an equilibrium, so positive demand is needed. -/
theorem test_zero_demand_any_profile : IsBertrandNash 2 (fun _ => 0) ![5, 7] := by
  intro i t
  have hz : ∀ (q : Fin 2 → ℝ) (j : Fin 2), bertrandProfit 2 (fun _ => 0) q j = 0 := by
    intro q j
    unfold bertrandProfit bertrandQuantity
    split_ifs <;> simp
  simp [hz]

end MathlibExtTest.Economics.Bertrand
