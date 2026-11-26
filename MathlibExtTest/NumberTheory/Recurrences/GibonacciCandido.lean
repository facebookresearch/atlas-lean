/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.GibonacciCandido

namespace MetaMathlibExt

private def gib (a b : ℝ) (j : ℤ) : ℝ := a * (Int.fib j : ℝ) + b * (Int.fib (j + 1) : ℝ)

private theorem gib_rec (a b : ℝ) (j : ℤ) : gib a b (j + 2) = gib a b (j + 1) + gib a b j := by
  unfold gib
  rw [show j + 2 + 1 = (j + 1) + 2 by omega, Int.fib_add_two (j + 1), Int.fib_add_two j]
  push_cast
  ring

-- The two sequences have distinct seeds and are evaluated at different offsets.
example : (72 : ℝ) =
    (gib 1 1 (-1) ^ 2 + gib 1 1 0 ^ 2 + gib 1 1 1 ^ 2) *
      (gib 2 1 0 * gib 1 1 (-1) + gib 2 1 1 * gib 1 1 0 + gib 2 1 2 * gib 1 1 1) := by
  calc
    (72 : ℝ) = 2 * (gib 2 1 0 * gib 1 1 (-1) ^ 3 + gib 2 1 1 * gib 1 1 0 ^ 3 +
        gib 2 1 2 * gib 1 1 1 ^ 3) := by norm_num [gib, Int.fib]
    _ = _ := by
      convert gibonacci_candido_two_sequence (gib 1 1) (gib 2 1)
        (gib_rec 1 1) (gib_rec 2 1) 0 (-1) using 1 <;> norm_num

-- Four different seed pairs are evaluated at offsets -1, 0, 1, and 2.
example :
    let G := gib 1 1
    let H := gib 2 1
    let M := gib 1 2
    let N := gib (-1) 2
    (3102 : ℝ) =
      (G (-1) * M 1 + G 0 * M 2 + G 1 * M 3) * (H 0 * N 2 + H 1 * N 3 + H 2 * N 4) +
      (G (-1) * H 0 + G 0 * H 1 + G 1 * H 2) * (M 1 * N 2 + M 2 * N 3 + M 3 * N 4) +
      (G (-1) * N 2 + G 0 * N 3 + G 1 * N 4) * (H 0 * M 1 + H 1 * M 2 + H 2 * M 3) := by
  intro G H M N
  have h := gibonacci_candido_four_sequence G H M N
    (gib_rec 1 1) (gib_rec 2 1) (gib_rec 1 2) (gib_rec (-1) 2) (-1) 0 1 2
  have hsum : (6 : ℝ) * (G (-1) * H 0 * M 1 * N 2 + G 0 * H 1 * M 2 * N 3 +
      G 1 * H 2 * M 3 * N 4) = 3102 := by norm_num [G, H, M, N, gib, Int.fib]
  norm_num only [Int.reduceAdd, Int.reduceNeg] at h
  rw [hsum] at h
  exact h

end MetaMathlibExt
