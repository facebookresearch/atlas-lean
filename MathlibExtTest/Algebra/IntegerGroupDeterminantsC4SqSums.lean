/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqSums
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases

/-!
# Tests for the sums `b_i`, `c_i` and differences `d_i` on `C₄ × C₄`
-/

open MetaMathlibExt

-- For `a (r, s) = r + 4 s`, that is `a_j = j` in the paper's indexing, every difference is `-8`.
example : c4SqD (fun p => (p.1.val + 4 * p.2.val : ℤ)) = fun _ => -8 := by
  funext i
  fin_cases i <;> rfl

-- In the same indexing, the sums are `b_i = 4 i + 24`.
example : c4SqB (fun p => (p.1.val + 4 * p.2.val : ℤ)) = fun i => 4 * (i.val : ℤ) + 24 := by
  funext i
  fin_cases i <;> rfl

-- ... and the alternating sums are `c_i = -8`.
example : c4SqC (fun p => (p.1.val + 4 * p.2.val : ℤ)) = fun _ => -8 := by
  funext i
  fin_cases i <;> rfl

-- Both sides of the identity at that point: all `d_i = -8`, so the sum of squares is `512`, the
-- cross sum is `256` and both sides are `8 · 512 · 256`.
example :
    let d := c4SqD (fun p => (p.1.val + 4 * p.2.val : ℤ))
    ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 -
        ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 =
      1048576 ∧
    8 * (d 0 ^ 2 + d 2 ^ 2 + d 4 ^ 2 + d 6 ^ 2 + d 1 ^ 2 + d 3 ^ 2 + d 5 ^ 2 + d 7 ^ 2) *
        (d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7) = 1048576 := by
  decide

-- A consequence: the two squared sums of squares are congruent modulo `8`.
example (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 ≡
      ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 [ZMOD 8] := by
  intro d
  have h := c4SqD_sum_sq_sq_sub_sq a
  exact Int.modEq_iff_dvd.2 ⟨_, h.trans (mul_assoc _ _ _)⟩
