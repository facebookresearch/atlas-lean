/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Urban.DemandRowScaling
import Mathlib.Tactic.NormNum

/-!
# Row-scaling checks

Focused checks for `MathlibExt.Urban.DemandRowScaling`: doubling
the weights `(1, 3)` at origin total `8` leaves the first entry at
`2`, and a zero-weight destination stays at zero.

These are elaboration and non-vacuity checks, not new results.
-/

open UrbanDemand

/-- Nonunit scale `c = 2` leaves the row unchanged. -/
example : normalizedDemand 8 (fun j => 2 * (fun i => if i = 0 then (1:ℝ) else 3) j)
    ({0, 1} : Finset ℕ) 0
    = normalizedDemand 8 (fun i => if i = 0 then (1:ℝ) else 3) ({0, 1} : Finset ℕ) 0 :=
  normalizedDemand_row_scaling 8 (fun i => if i = 0 then (1:ℝ) else 3)
    ({0, 1} : Finset ℕ) 0 (by norm_num)
    (by norm_num [Finset.sum_pair])

/-- The unchanged first entry has value `2`. -/
example : normalizedDemand 8 (fun i => if i = 0 then (1:ℝ) else 3)
    ({0, 1} : Finset ℕ) 0 = 2 := by
  unfold normalizedDemand
  norm_num [Finset.sum_pair]

/-- A zero-weight destination stays at zero, under scaling and
in value. -/
example : normalizedDemand 8 (fun j => 2 * (fun i => if i = 0 then (0:ℝ) else 3) j)
    ({0, 1} : Finset ℕ) 0
    = normalizedDemand 8 (fun i => if i = 0 then (0:ℝ) else 3) ({0, 1} : Finset ℕ) 0 :=
  normalizedDemand_row_scaling 8 (fun i => if i = 0 then (0:ℝ) else 3)
    ({0, 1} : Finset ℕ) 0 (by norm_num)
    (by norm_num [Finset.sum_pair])

/-- The zero-weight entry has value `0`. -/
example : normalizedDemand 8 (fun i => if i = 0 then (0:ℝ) else 3)
    ({0, 1} : Finset ℕ) 0 = 0 := by
  unfold normalizedDemand
  norm_num [Finset.sum_pair]
