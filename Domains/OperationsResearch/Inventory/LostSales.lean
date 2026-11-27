/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Domains.OperationsResearch.Inventory.StockFlow
import Mathlib.Tactic.Ring

/-!
# Inventory balance with lost sales

At deterministic lead time `L`, receipts and the outstanding pipeline are those of
`Inventory.receipt` and `Inventory.pipeline` in `StockFlow`. Only the service rule changes:
a customer who cannot be served leaves. The next period starts with unsold stock, not with
a claim on future deliveries. Orders and demands are given streams, not decision variables.

The balances follow from these definitions. In the alternative backlogging model,
`Inventory.stockTrace_succ` deducts all demand, `Inventory.onHand` and `Inventory.backlog`
give the positive and negative parts of net stock, and `Inventory.stockTrace_balance` and
`Inventory.conservation` give the corresponding balances with demand instead of sales.
-/

@[expose] public section

namespace Inventory.LostSales

variable (initial : NNReal) (L : ℕ) (initPipe : Fin L → NNReal) (order demand : ℕ → NNReal)

/-- Unsold stock carried into period `t`, starting from nonnegative `initial`. The scheduled
receipt comes from `initPipe` for `t < L` and from order `t - L` otherwise. The order at `t`
is placed before demand and received immediately if `L = 0`. Of the resulting available
stock, only its minimum with current demand is sold; no unmet demand is carried forward. -/
noncomputable def stock : ℕ → NNReal
  | 0 => initial
  | t + 1 =>
    let a := stock t + receipt L initPipe order t
    a - min a (demand t)

/-- Stock available to serve demand in period `t` of a lost-sales trace: nonnegative opening
stock plus its scheduled receipt. With positive lead time the receipt is a due delivery;
with zero lead time it is the order just placed, before demand is served. -/
noncomputable def available (t : ℕ) : NNReal :=
  stock initial L initPipe order demand t + receipt L initPipe order t

/-- Actual sales in period `t` are the minimum of the nonnegative demand and the stock
available after receiving the due delivery (the current order for zero lead time).
Only current demand is served; unfilled demand from earlier periods is not served later. -/
noncomputable def sales (t : ℕ) : NNReal :=
  min (available initial L initPipe order demand t) (demand t)

/-- Unfilled demand lost in period `t`: nonnegative current demand minus actual sales
from stock available after receipt, including the immediate order at zero lead time.
Sales are at most demand, so the difference is exact and creates no backlog. -/
noncomputable def lostDemand (t : ℕ) : NNReal :=
  demand t - sales initial L initPipe order demand t

local notation "I" => stock initial L initPipe order demand
local notation "A" => available initial L initPipe order demand
local notation "S" => sales initial L initPipe order demand

/-- Before the first receipt or sale the lost-sales stock equals the given nonnegative
initial stock. Quantities due in the initial pipeline are not yet on hand. -/
@[simp] theorem stock_zero : I 0 = initial := rfl

/-- Opening stock of period `t + 1` is the nonnegative stock available after receipt in
period `t` minus the sales actually served there. This receipt includes the current order
when lead time is zero; demand in excess of available stock does not enter the next state. -/
theorem stock_succ (t : ℕ) : I (t + 1) = A t - S t := rfl

/-- Each period's nonnegative demand splits into actual sales from stock available after
receipt and demand lost for good. At lead time zero the receipt precedes these sales even
though it is the order just placed. -/
theorem sales_add_lostDemand (t : ℕ) :
    S t + lostDemand initial L initPipe order demand t = demand t :=
  add_tsub_cancel_of_le (min_le_right (A t) (demand t))

/-- For nonnegative initial stock, scheduled receipts and demand, the opening lost-sales
stock at `t`, cast to `ℝ`, equals the signed stock trace with *actual sales* supplied as
withdrawals. Sales occur after receipt (immediate for zero lead time); the identity does
not hold in general for the backlogging trace supplied with the original demand. -/
private theorem coe_stock_eq_trace (t : ℕ) :
    (I t : ℝ) = stockTrace initial L initPipe order S t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs : S t ≤ A t := min_le_left _ _
    rw [stock_succ, NNReal.coe_sub hs, stockTrace_succ, available, NNReal.coe_add, ih]

/-- Over periods `0 ≤ t < T`, nonnegative initial stock plus all scheduled receipts equals
stock carried into `T` plus cumulative actual sales, in `ℝ`. Each receipt (the current
order at zero lead time) is available before sales; lost demand is not a withdrawal. -/
theorem stock_balance (T : ℕ) :
    (initial : ℝ) + ∑ t ∈ Finset.range T, (receipt L initPipe order t : ℝ) =
      (I T : ℝ) + ∑ t ∈ Finset.range T, (S t : ℝ) := by
  rw [coe_stock_eq_trace, stockTrace_balance]
  exact (sub_add_cancel _ _).symm

/-- For nonnegative inputs and deterministic lead time `L`, unsold stock plus the total
still outstanding after `T` periods equals initial stock plus the sum of the initial
pipeline plus all orders placed before `T` minus actual sales before `T`. Receipts precede
service (the current order arrives immediately at zero lead time); orders still in transit
are not on hand. All quantities are cast to `ℝ` before subtraction. -/
theorem conservation (T : ℕ) :
    (I T : ℝ) + pipelineTotal L initPipe order T =
      initial + (∑ j, (initPipe j : ℝ)) + (∑ t ∈ Finset.range T, (order t : ℝ)) -
        ∑ t ∈ Finset.range T, (S t : ℝ) := by
  rw [coe_stock_eq_trace]
  exact Inventory.conservation initial L initPipe order S T

/-- From the opening of `t` to the opening of `t + 1`, unsold stock plus outstanding
pipeline changes by the order placed minus the sales actually served after receipt.
At zero lead time the order is received immediately. The difference is signed in `ℝ`,
so sales exceeding the order decrease the total even if some demand is lost. -/
theorem conservation_step (t : ℕ) :
    (I (t + 1) : ℝ) + pipelineTotal L initPipe order (t + 1) =
      (I t : ℝ) + pipelineTotal L initPipe order t + ((order t : ℝ) - (S t : ℝ)) := by
  rw [conservation, conservation, Finset.sum_range_succ, Finset.sum_range_succ]
  ring

end Inventory.LostSales
