/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ProcessBalances.LinearRecycle
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

open scoped BigOperators Matrix
open Domains.Chemistry.ProcessBalances.LinearRecycle

-- Two return edges at the same unit must both count toward its recycling fraction.
example : ((1 : ℝ) - (1 / 4 + 1 / 4)) * 2 = 1 := by
  let vertex (_ : Bool) : PUnit.{1} := PUnit.unit
  let fraction (_ : Bool) : ℝ := 1 / 4
  have h := linear_recycle_balances vertex vertex fraction (fun _ => 1)
    (by intro e; norm_num [fraction]) (by intro i; norm_num)
    (by intro j; cases j; norm_num [vertex, fraction, Fintype.sum_bool])
  have t := h.2.2 (fun _ => 2) (by intro i; cases i; norm_num [vertex, fraction, Fintype.sum_bool])
  convert t using 1 <;> norm_num [vertex, fraction, Fintype.sum_bool, Fintype.sum_unique]

-- The spectral conclusion applies to zero return fractions, with nonnegative fresh feed.
example : ∀ i : PUnit.{1}, 0 ≤ ((1 : Matrix PUnit.{1} PUnit.{1} ℝ)⁻¹ *ᵥ (fun _ => 3)) i := by
  let vertex (_ : Bool) : PUnit.{1} := PUnit.unit
  let K : Matrix PUnit.{1} PUnit.{1} ℝ := fun i j =>
    ∑ e : Bool, if vertex e = j ∧ vertex e = i then 0 else 0
  have hK : K = 0 := by ext i j; simp [K]
  have hρ : spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < 1 := by
    rw [hK, Matrix.map_zero _ (map_zero _), spectrum.spectralRadius_zero]
    exact zero_lt_one
  have h := linear_recycle_balances vertex vertex (fun _ => 0) (fun _ => 3)
    (by intro e; norm_num) (by intro i; norm_num) (by intro j; simp)
  have hsol := (h.2.1 hρ).2.2
  change ∀ i, 0 ≤ ((1 - K)⁻¹ *ᵥ (fun _ => 3)) i at hsol
  simpa only [hK, sub_zero] using hsol
