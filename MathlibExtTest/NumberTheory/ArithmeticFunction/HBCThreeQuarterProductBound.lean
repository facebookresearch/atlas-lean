/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.HBCThreeQuarterProductBound

/-! # Tests for Stone's three-quarter product bound -/

open Finset MetaMathlibExt

namespace HBCThreeQuarterProductBoundTest

private def triple (i : ℕ) : ℕ := ([0, 3, 4, 31] : List ℕ).getD i 0

-- For `(5, 6)` at `2/3`, the strict prefix becomes an equality at the last term.
-- The floor is 4, and the full prefix satisfies both estimates with `α = 3`.
example : (1 - 1 / (5 : ℝ)) * (1 - 1 / 6) = 2 / 3 ∧
    (2 : ℝ) / 3 < 1 - 1 / 5 ∧ ⌊(1 : ℝ) + 3⌋₊ = 4 ∧
    (2 : ℝ) * (5 * 6) + 1 ≤ 3 ^ (2 ^ 2 : ℕ) ∧
    (2 : ℝ) * (5 * 6) ≤ 3 ^ (2 ^ 2 : ℕ) - 3 ^ (2 ^ 1 : ℕ) := by
  norm_num [Nat.floor_eq_iff]

-- For `(3, 4, 31)` at `15/31`, the first two terms give a strict prefix and the
-- full reciprocal product gives equality. Only length two meets the prefix estimate.
example : (1 - 1 / (3 : ℝ)) * (1 - 1 / 4) * (1 - 1 / 31) = 15 / 31 ∧
    (15 : ℝ) / 31 < (1 - 1 / 3) * (1 - 1 / 4) ∧ ⌊(1 : ℝ) + 31 / 16⌋₊ = 2 ∧
    (16 : ℝ) * (31 / 16) ^ (2 ^ 1 : ℕ) < 15 * 3 + 16 ∧
    (15 : ℝ) * (3 * 4) + 16 ≤ 16 * (31 / 16) ^ (2 ^ 2 : ℕ) ∧
    (16 : ℝ) * (31 / 16) ^ (2 ^ 3 : ℕ) < 15 * (3 * 4 * 31) + 16 ∧
    (15 : ℝ) * (3 * 4 * 31) ≤
      (16 * (31 / 16) ^ (2 ^ 2 : ℕ)) ^ 2 - 16 * (31 / 16) ^ (2 ^ 2 : ℕ) := by
  norm_num [Nat.floor_eq_iff]

private theorem sixteen_rpow_three_quarters : (16 : ℝ) ^ ((3 : ℝ) / 4) = 8 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num),
    show ((4 : ℕ) : ℝ) * ((3 : ℝ) / 4) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num

-- Compute the product bound independently for the same triple with nontrivial `d^(3/4)`.
example : 15 * ∏ i ∈ Icc 1 3, (triple i : ℝ) ≤
    (31 / (16 : ℝ) ^ ((3 : ℝ) / 4)) ^ (2 ^ 3 : ℕ) -
      (31 / (16 : ℝ) ^ ((3 : ℝ) / 4)) ^ (2 ^ 2 : ℕ) := by
  rw [sixteen_rpow_three_quarters, show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [triple]

-- The excluded first term matters: `(2, 31)` is admissible at `15/31` but fails the bound.
example : (1 - 1 / (2 : ℝ)) * (1 - 1 / 31) = 15 / 31 ∧
    (15 : ℝ) / 31 < 1 - 1 / 2 ∧ ⌊(1 : ℝ) + 31 / 16⌋₊ = 2 ∧
    (31 / (16 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 - (31 / (16 : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 <
      15 * (2 * 31) := by
  norm_num [sixteen_rpow_three_quarters, Nat.floor_eq_iff]

-- At `d = 4`, `α = 2`, `c = 3` and `κ = 2`, the new base dominates the prefix bound.
-- The tight full-prefix estimate at `m = 2` and the tight proper-prefix estimate at `m = 3`
-- both fit the corresponding bound at the new base.
example : (4 : ℝ) * 2 ^ (2 ^ 2 : ℕ) ≤ 3 ^ (2 ^ 2 : ℕ) ∧
    (4 : ℝ) * (2 ^ (2 ^ 2 : ℕ) - 2 ^ (2 ^ 1 : ℕ)) ≤ 3 ^ (2 ^ 2 : ℕ) - 3 ^ (2 ^ 1 : ℕ) ∧
    ((4 : ℝ) * 2 ^ (2 ^ 2 : ℕ)) ^ 2 - 4 * 2 ^ (2 ^ 2 : ℕ) ≤
      3 ^ (2 ^ 3 : ℕ) - 3 ^ (2 ^ 2 : ℕ) := by
  norm_num

-- A client of the public bound at the shortest allowed length.
example : (2 : ℝ) * (5 * 6) ≤ 3 ^ 4 - 3 ^ 2 := by
  have h := hbcAdmissible_prod_le_of_ne_floor 2 1 2 (by decide) (by decide) (by decide)
    (by decide) (fun i => i + 4) (by decide) (fun i _ _ => by omega)
    (by norm_num [prod_Icc_succ_top]) (by norm_num) (by norm_num [Nat.floor_eq_iff])
  convert h using 1 <;> norm_num [prod_Icc_succ_top, Real.one_rpow]

end HBCThreeQuarterProductBoundTest
