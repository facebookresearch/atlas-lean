/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperLeonardoPSuperLeonardoPEqAddMul
import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for reduction of supergeneralized Leonardo p-numbers

A below-recurrence case where the correction vanishes, a numeric evaluation at `p = 2` and
`n = 6`, and the corollary giving the inhomogeneous part.
-/

namespace MathlibExtTest.NumberTheory.SuperLeonardoPSuperLeonardoPEqAddMul

open MetaMathlibExt

-- Below the recurrence, the correction term vanishes.
example (x : ℕ → ℝ) : superLeonardoP 2 5 x 2 = superLeonardoP 2 0 x 2 := by
  rw [superLeonardoP_eq_add_mul 2 5 (by decide) x 2,
    ite_eq_right (show ¬(2:ℕ) < 2 from by decide)]
  simp

-- At `p = 2` and `n = 6` the correction weight is `𝓛_{2,1,y}(3) = 5`.
example : superLeonardoP 2 3 (fun _ => 1) 6 = 21 := by
  rw [superLeonardoP_eq_add_mul 2 3 (by decide) _ 6,
    ite_eq_left (show (2:ℕ) < 6 from by decide), show 6 - (2 + 1) = 3 from by decide]
  have h0 : superLeonardoP 2 0 (fun _ => (1:ℝ)) 6 = 6 := by
    rw [superLeonardoP_zero_eq 2 (by decide)]
    norm_num [Finset.sum_range_succ, show fibonacciP 2 3 = 1 by decide +kernel,
      show fibonacciP 2 4 = 2 by decide +kernel, show fibonacciP 2 5 = 3 by decide +kernel]
  have h1 : superLeonardoP 2 1 (fun i => (i:ℝ) + 1) 3 = 5 := by
    rw [superLeonardoP_one_succ_eq_sum_choose 2 (by decide)]
    norm_num [Finset.sum_range_succ, Nat.choose]
  rw [h0, h1]
  norm_num

-- The inhomogeneous part is exactly the correction weight times `k`.
example (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) (hn : p < n) :
    superLeonardoP p k x n - superLeonardoP p 0 x n =
      superLeonardoP p 1 (fun i => (i:ℝ) + 1) (n - (p + 1)) * k := by
  rw [superLeonardoP_eq_add_mul p k hp x n, ite_eq_left hn]
  ring

end MathlibExtTest.NumberTheory.SuperLeonardoPSuperLeonardoPEqAddMul
