/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.OperationsResearch.Inventory.LostSales
import Mathlib.Tactic.NormNum

/-! # Receipt timing, stockouts and terminal inventory in the lost-sales trace -/

namespace Inventory.LostSales

-- One unit on hand, one unit due at time zero. The orders 3 and 1 arrive one
-- period later; demand is 5 and then 2. The second order is still in transit at T = 2.
/-- The one-period lead trace starts with one unit due in period zero. -/
private def due : Fin 1 → NNReal := fun _ => 1

/-- Place three units before demand in period zero and one in each subsequent period. -/
private def orders : ℕ → NNReal := fun t => if t = 0 then 3 else 1

/-- Demand after receipt is five in period zero and two in every subsequent period. -/
private def demands : ℕ → NNReal := fun t => if t = 0 then 5 else 2

local notation "I" => stock 1 1 due orders demands
local notation "A" => available 1 1 due orders demands
local notation "S" => sales 1 1 due orders demands
local notation "U" => lostDemand 1 1 due orders demands
local notation "P" => pipelineTotal 1 due orders

-- Nonnegativity follows from the types even after casting the period quantities to ℝ.
example (initial : NNReal) (L : ℕ) (p : Fin L → NNReal) (q d : ℕ → NNReal) (t : ℕ) :
    0 ≤ (stock initial L p q d (t + 1) : ℝ) ∧ 0 ≤ (available initial L p q d t : ℝ) ∧
      0 ≤ (sales initial L p q d t : ℝ) ∧ 0 ≤ (lostDemand initial L p q d t : ℝ) :=
  ⟨(stock ..).property, (available ..).property, (sales ..).property, (lostDemand ..).property⟩

-- The empty horizon includes the initial pipeline but no orders or sales.
example : (I 0 : ℝ) + P 0 = 2 := by
  norm_num [stock, pipelineTotal, pipeline, receipt, due]

-- Receive 1 and serve only 2. The order for 3 is not yet available.
example : A 0 = 2 ∧ S 0 = 2 ∧ U 0 = 3 ∧ I 1 = 0 := by
  norm_num [tsub_eq_iff_eq_add_of_le, lostDemand, sales, available, stock, receipt, due, orders, demands]

-- The next delivery is available for today's demand, not for yesterday's shortfall.
-- The same inputs in the backlogging trace instead leave net stock -3 and then -2.
example : A 1 = 3 ∧ S 1 = 2 ∧ U 1 = 0 ∧ I 2 = 1 ∧
    stockTrace 1 1 due orders demands 1 = -3 ∧ stockTrace 1 1 due orders demands 2 = -2 := by
  norm_num [tsub_eq_iff_eq_add_of_le, lostDemand, sales, available, stock, stockTrace, receipt, due, orders, demands]

-- The two independent sale pins also account for all stock that actually arrived.
example : (I 2 : ℝ) + ∑ t ∈ Finset.range 2, (S t : ℝ) = 5 := by
  rw [← stock_balance]
  norm_num [Finset.sum_range_succ, receipt, due, orders]

-- At T = 2 the final order is still outstanding; stock alone is short of the
-- conserved total. In the second period stock plus pipeline *decreases* by one.
example : pipeline 1 due orders 2 0 = 1 ∧ P 2 = 1 ∧
    (I 2 : ℝ) + P 2 - ((I 1 : ℝ) + P 1) = -1 := by
  norm_num [pipelineTotal, pipeline, stock, receipt, due, orders, demands]

-- Lead time zero: the current order can be sold immediately, with nothing in transit.
example : sales 0 0 Fin.elim0 (fun _ => 3) (fun _ => 2) 0 = 2 ∧
    stock 0 0 Fin.elim0 (fun _ => 3) (fun _ => 2) 1 = 1 ∧
    pipelineTotal 0 Fin.elim0 (fun _ => 3) 1 = 0 := by
  norm_num [tsub_eq_iff_eq_add_of_le, sales, available, stock, receipt_zero_lead, pipelineTotal_zero]

end Inventory.LostSales
