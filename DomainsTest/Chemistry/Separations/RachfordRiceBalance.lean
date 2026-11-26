/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Separations.RachfordRiceBalance
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Domains.Chemistry.Separations.RachfordRiceBalance

private noncomputable def ratios (i : Bool) : ℝ := if i then 2 else 1 / 2

-- At a one-half vapour fraction, both phases are normalized and the objective is zero.
example : (∑ i : Bool, (1 / 2 : ℝ) * (ratios i - 1) / (1 + (1 / 2) * (ratios i - 1))) = 0 := by
  let x (i : Bool) : ℝ := if i then 1 / 3 else 2 / 3
  let y (i : Bool) : ℝ := if i then 2 / 3 else 1 / 3
  have h := flash_balance_rachford_rice 2 1 1 (fun _ => 1 / 2) ratios x y
    (by norm_num) (by norm_num) (by norm_num) (by intro; norm_num)
    (by norm_num [Fintype.sum_bool]) (by intro i; cases i <;> norm_num [ratios])
    (by intro i; cases i <;> norm_num [x, y])
    (by intro i; cases i <;> norm_num [ratios, x, y])
  exact h.2.mp (by norm_num [Fintype.sum_bool, x, y])

-- A zero feed component is allowed. At zero vapour fraction the liquid is normalized,
-- but a nonzero objective still excludes simultaneous normalization.
example : ¬ (∑ i : Bool, if i then (2 : ℝ) else 0) = 1 := by
  let z (i : Bool) : ℝ := if i then 1 else 0
  let y (i : Bool) : ℝ := if i then 2 else 0
  have h := flash_balance_rachford_rice 1 1 0 z ratios z y
    (by norm_num) (by norm_num) (by norm_num) (by intro i; cases i <;> norm_num [z])
    (by norm_num [Fintype.sum_bool, z]) (by intro i; cases i <;> norm_num [ratios])
    (by simp) (by intro i; cases i <;> norm_num [ratios, z, y])
  intro hy
  have hzero := h.2.mp ⟨by norm_num [Fintype.sum_bool, z], hy⟩
  norm_num [Fintype.sum_bool, ratios, z] at hzero

-- At the other endpoint, use the converse: a zero objective normalizes both phases,
-- even though the balance by itself fixes only the vapour composition.
example :
    let x : Bool → ℝ := fun i => if i then 1 / 3 else 2 / 3
    let y : Bool → ℝ := fun i => if i then 2 / 3 else 1 / 3
    (∑ i, x i) = 1 ∧ (∑ i, y i) = 1 := by
  intro x y
  have h := flash_balance_rachford_rice 1 0 1 y ratios x y
    (by norm_num) (by norm_num) (by norm_num) (by intro i; cases i <;> norm_num [y])
    (by norm_num [Fintype.sum_bool, y]) (by intro i; cases i <;> norm_num [ratios])
    (by intro i; simp) (by intro i; cases i <;> norm_num [ratios, x, y])
  apply h.2.mpr
  norm_num [Fintype.sum_bool, ratios, y]
