/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ProcessBalances.WorkInProcess
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Domains.Chemistry.ProcessBalances.WorkInProcess

-- One operation with a nonzero internal rework transfer and no boundary outflow.
example : (∑ _ : PUnit.{1}, (3 : ℝ)) = (∑ _ : PUnit.{1}, (5 : ℝ)) - (∑ _ : PUnit.{1}, (2 : ℝ)) := by
  have h := finite_window_balance (fun _ : PUnit.{1} => PUnit.unit) (fun _ : PUnit.{1} => PUnit.unit)
    (fun _ => 7) (fun _ => 2) (fun _ => 5) (fun _ => 3) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by intro v; cases v; norm_num [Fintype.sum_unique])
  exact h.2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- An edge transfers a positive amount to the second operation, which consumes one unit.
example : (8 : ℝ) + (-1) = 1 + 0 + (6 - 0) := by
  have h := finite_window_balance (fun _ : PUnit.{1} => false) (fun _ : PUnit.{1} => true) (fun _ => 4)
    (fun _ => 0) (fun v => if v then 2 else 4) (fun v => if v then 0 else 8)
    (fun v => if v then 1 else 0) (fun _ => 0) (fun v => if v then -1 else 0)
    (by intro v; cases v <;> norm_num [Fintype.sum_unique])
  convert h.1 using 1 <;> norm_num [Fintype.sum_bool]
