/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions` -/

namespace MathlibExtTest.OneMeteredParkingFunctions

open MetaMathlibExt

/-- The right-hand side of the Binet formula `meteredParkingCount_one_binet`. -/
private noncomputable def binetRHS (m n : ℕ) : ℝ :=
  (n * (n + Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n + Real.sqrt (n ^ 2 - 4)) - 4) *
      ((n + Real.sqrt (n ^ 2 - 4)) / 2) ^ m +
    (n * (n - Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n - Real.sqrt (n ^ 2 - 4)) - 4) *
      ((n - Real.sqrt (n ^ 2 - 4)) / 2) ^ m

-- For `n ≥ 2` the right-hand side satisfies `x (m + 2) = n * x (m + 1) - x m` for every `m`, since
-- `(n ± √(n ^ 2 - 4)) / 2` are the roots of `x ^ 2 - n * x + 1`.
private theorem binetRHS_add_two {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    binetRHS (m + 2) n = n * binetRHS (m + 1) n - binetRHS m n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : Real.sqrt ((n : ℝ) ^ 2 - 4) ^ 2 = (n : ℝ) ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  unfold binetRHS
  linear_combination
    ((n * (n + Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n + Real.sqrt (n ^ 2 - 4)) - 4) *
        ((n + Real.sqrt (n ^ 2 - 4)) / 2) ^ m +
      (n * (n - Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n - Real.sqrt (n ^ 2 - 4)) - 4) *
        ((n - Real.sqrt (n ^ 2 - 4)) / 2) ^ m) / 4 * hs2

-- The Binet formula in terms of `binetRHS`.
private theorem count_eq_binetRHS {m n : ℕ} (hm : m ≤ n + 1) (hn : 2 < n) :
    (meteredParkingCount 1 m n : ℝ) = binetRHS m n :=
  meteredParkingCount_one_binet hm hn

-- Test section: values. For three spots the formula gives every other Fibonacci number, up to
-- `m = n + 1 = 4`.
example : meteredParkingCount 1 0 3 = 1 ∧ meteredParkingCount 1 1 3 = 3 ∧
    meteredParkingCount 1 2 3 = 8 ∧ meteredParkingCount 1 3 3 = 21 ∧
    meteredParkingCount 1 4 3 = 55 := by
  decide

example : binetRHS 4 3 = 55 := by
  rw [← count_eq_binetRHS (m := 4) (n := 3) (by norm_num) (by norm_num)]
  norm_num [show meteredParkingCount 1 4 3 = 55 by decide]

-- The three-car count includes the boundary `n = 2`, which the Binet formula excludes.
example : meteredParkingCount 1 3 2 = 4 :=
  meteredParkingCount_one_three (n := 2) (by decide)

-- The three-spot count agrees with the preceding finite enumeration.
example : meteredParkingCount 1 3 3 = 21 :=
  meteredParkingCount_one_three (n := 3) (by decide)

-- Test section: the bound `m ≤ n + 1` is sharp. For `n = 3` the right-hand side at `m = 5` is
-- `3 * 55 - 21 = 144`, but there are 145 1-metered `(5, 3)`-parking functions.
example : binetRHS 5 3 = 144 ∧ meteredParkingCount 1 5 3 = 145 := by
  have h := binetRHS_add_two (n := 3) (by norm_num) 3
  have h4 : binetRHS 4 3 = 55 := by
    rw [← count_eq_binetRHS (m := 4) (n := 3) (by norm_num) (by norm_num)]
    norm_num [show meteredParkingCount 1 4 3 = 55 by decide]
  have h3 : binetRHS 3 3 = 21 := by
    rw [← count_eq_binetRHS (m := 3) (n := 3) (by norm_num) (by norm_num)]
    norm_num [show meteredParkingCount 1 3 3 = 21 by decide]
  rw [show (3 + 2 : ℕ) = 5 from rfl, show (3 + 1 : ℕ) = 4 from rfl, h4, h3] at h
  refine ⟨?_, by decide +kernel⟩
  norm_num at h
  exact h

-- Test section: the hypothesis `2 < n` is needed. For `n = 2` both denominators vanish, so the
-- right-hand side is `0` for every `m`, while the empty preference list is a 1-metered parking
-- function.
example (m : ℕ) : binetRHS m 2 = 0 := by
  norm_num [binetRHS]

example : (meteredParkingCount 1 0 2 : ℝ) ≠ binetRHS 0 2 := by
  rw [show meteredParkingCount 1 0 2 = 1 by decide]
  norm_num [binetRHS]

end MathlibExtTest.OneMeteredParkingFunctions
