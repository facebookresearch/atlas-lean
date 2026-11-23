/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsIdentities
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- At order zero, the identity still applies when 1 + f vanishes.
example (j n : ℕ) :
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) * (-1 : ℝ) ^ ((k : ℤ) + 1 - j) =
      -(1 / (-1 : ℝ) ^ j) := by
  simpa using sum_iteratedDeriv_zpow_one_add (r := 0) (f := fun _ => -1)
    contDiff_const (fun _ => by norm_num) j n 0

-- With n = 1 and j = 2 the two summands have exponents -1 and 0.
example {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : ∀ y, f y ≠ 0) (x : ℝ) :
    2 * deriv (fun y => (f y)⁻¹) x =
      (1 / f x ^ 2) * deriv (fun y => (1 + f y) ^ 2 - 1) x +
        deriv (fun y => 1 / f y ^ 2) x * ((1 + f x) ^ 2 - 1) := by
  have h := sum_iteratedDeriv_zpow_one_add (r := 1) hf hf0 2 1 x
  norm_num [sum_range_succ, Nat.choose, iteratedDeriv_one] at h ⊢
  exact h
