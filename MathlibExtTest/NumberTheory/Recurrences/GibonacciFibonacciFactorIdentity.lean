/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity` -/

namespace MetaMathlibExt.gibonacci_mul_add_neg_one_pow_eq_fib_mul.Tests

/-- The signed Fibonacci numbers, cast to `ℝ`, form a gibonacci sequence with seeds `0` and `1`,
so the hypotheses of the identity are satisfiable. -/
private theorem fib_add_two (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
  rw [Int.fib_add_two]
  push_cast
  ring

/-- The Lucas numbers `L_j = F_(j-1) + F_(j+1)` form a gibonacci sequence with seeds `2`
and `1`. -/
private theorem lucas_add_two (j : ℤ) :
    (Int.fib (j + 2 - 1) + Int.fib (j + 2 + 1) : ℝ) =
      (Int.fib (j + 1 - 1) + Int.fib (j + 1 + 1) : ℝ) + (Int.fib (j - 1) + Int.fib (j + 1)) := by
  have h1 := fib_add_two (j - 1)
  have h2 := fib_add_two (j + 1)
  have h3 := fib_add_two j
  rw [show j - 1 + 2 = j + 2 - 1 by ring, show j - 1 + 1 = j by ring] at h1
  rw [show j + 1 + 2 = j + 2 + 1 by ring, show j + 1 + 1 = j + 2 by ring] at h2
  rw [show j + 1 - 1 = j by ring, show j + 1 + 1 = j + 2 by ring]
  linarith

-- At shift `k = -2` the addition formula recovers one backward step of the recurrence.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (s : ℤ) :
    G (s + 1) - G s = G (s - 1) := by
  simpa [sub_eq_add_neg, show (-2 : ℤ) + s + 1 = s - 1 by ring] using
    fib_mul_gibonacci_add_eq_gibonacci G hG (-2) s

-- Test section: with `G = H = F` the identity reads
-- `F_s F_(k+r) + (-1)^(r-1) F_(s-r) F_k = F_r F_(k+s)`.
example (r s k : ℤ) :
    (Int.fib s : ℝ) * Int.fib (k + r) + (-1 : ℝ) ^ (r - 1) * Int.fib (s - r) * Int.fib k =
      Int.fib r * Int.fib (k + s) := by
  simpa using gibonacci_mul_add_neg_one_pow_eq_fib_mul (fun j => (Int.fib j : ℝ))
    (fun j => (Int.fib j : ℝ)) fib_add_two fib_add_two r s k

-- Test section: d'Ocagne's identity `F_m F_(n+1) - F_(m+1) F_n = (-1)^n F_(m-n)`, the case
-- `G = H = F`, `k = 1` (the paper's identity generalizes it), for all integers `m` and `n`.
example (m n : ℤ) :
    (Int.fib m : ℝ) * Int.fib (n + 1) - Int.fib (m + 1) * Int.fib n =
      (-1 : ℝ) ^ n * Int.fib (m - n) := by
  have h := gibonacci_mul_add_neg_one_pow_eq_fib_mul (fun j => (Int.fib j : ℝ))
    (fun j => (Int.fib j : ℝ)) fib_add_two fib_add_two n m 1
  simp only [Int.fib_zero, Int.fib_one, Int.cast_zero, Int.cast_one, zero_mul, one_mul,
    zero_add, mul_one] at h
  rw [show (1 : ℤ) + n = n + 1 by ring, show (1 : ℤ) + m = m + 1 by ring] at h
  have hpow : (-1 : ℝ) ^ n = -(-1 : ℝ) ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]
    ring_nf
  rw [hpow]
  linear_combination h

-- Test section: a second sequence with other seeds. With `G = F` and `H = L` the identity reads
-- `L_s F_(k+r) + (-1)^(r-1) L_(s-r) F_k = F_r L_(k+s)`.
example (r s k : ℤ) :
    (Int.fib (s - 1) + Int.fib (s + 1) : ℝ) * Int.fib (k + r) +
        (-1 : ℝ) ^ (r - 1) * (Int.fib (s - r - 1) + Int.fib (s - r + 1) : ℝ) * Int.fib k =
      Int.fib r * (Int.fib (k + s - 1) + Int.fib (k + s + 1) : ℝ) := by
  simpa using gibonacci_mul_add_neg_one_pow_eq_fib_mul (fun j => (Int.fib j : ℝ))
    (fun j => (Int.fib (j - 1) + Int.fib (j + 1) : ℝ)) fib_add_two lucas_add_two r s k

-- Test section: a negative index. At `r = -1`, where `(-1)^(r-1) = 1` and `F_(-1) = 1`, the
-- identity says that `G_(k-1) H_s + G_k H_(s+1)` depends only on `k + s`.
example (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (s k : ℤ) :
    G (k - 1) * H s + G k * H (s + 1) = G 0 * H (k + s - 1) + G 1 * H (k + s) := by
  have h := gibonacci_mul_add_neg_one_pow_eq_fib_mul G H hG hH (-1) s k
  rw [show s - -1 = s + 1 by ring, show k + -1 = k - 1 by ring] at h
  norm_num at h
  linarith

end MetaMathlibExt.gibonacci_mul_add_neg_one_pow_eq_fib_mul.Tests
