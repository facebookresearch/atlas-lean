/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.OperationsResearch.Inventory.MissionLedger
import Mathlib.Tactic.NormNum

/-! # Mission and inventory stock-flow agreement -/

open Finset MissionLedger

/-- The prefix stocks of the schedule `+2, -3, +1` are the zero-lead-time stock-flow trace, and
the final stock `2` is the initial `2` plus gains `3` minus draws `3`. -/
example :
    stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 2 =
        Inventory.stockTrace 2 0 Fin.elim0 (gains (fun _ => listFlow [2, -3, 1]) ())
          (draws (fun _ => listFlow [2, -3, 1]) ()) 2 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 3 = 2 + 3 - 3 := by
  refine ⟨stock_eq_stockTrace _ _ () 2, ?_⟩
  rw [terminal_accounting]
  norm_num [gains, draws, listFlow, Finset.sum_range_succ]
