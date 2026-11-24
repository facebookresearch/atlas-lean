/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CatalanTriangleStepFive

open MetaMathlibExt Finset

-- In row zero the sole entry contributes only to the odd-indexed sum.
example :
    let d (k : ℕ) : ℚ := if k ≤ 0 then (k + 1 : ℚ) * (Nat.choose 2 (0 - k) : ℚ) else 0
    d 1 - d 2 = 0 ∧ d 0 - d 3 = 1 := by
  simp

-- Row six is the first in which both sums receive a term from the second block.
example :
    let d (k : ℕ) : ℚ := if k ≤ 6 then (k + 1 : ℚ) / 7 * (Nat.choose 14 (6 - k) : ℚ) else 0
    d 1 - d 2 + d 6 = 144 ∧ d 0 - d 3 + d 5 = 233 := by
  have h := catalanTriangle_stepFive_sub_eq_fib 6
  norm_num [sum_range_succ, Nat.fib_add_two] at h ⊢
  simpa only [sub_add_eq_add_sub] using h
