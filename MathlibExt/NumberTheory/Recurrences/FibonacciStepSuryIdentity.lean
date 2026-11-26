/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Ring

/-!
# The Fibonacci step extension of Sury's identity

The Fibonacci subsequence of step `j` satisfies a second-order recurrence with coefficients
`L_j` and `-(-1)^j`. The recurrence gives the change in the weighted sum when its upper index
increases by one.
-/

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

private theorem fibAtInt_add_two_mul (j k : ℕ) :
    fibAtInt ↑(k + 2 * j) + (-1 : ℚ) ^ j * fibAtInt k =
      lucasAtInt j * fibAtInt ↑(k + j) := by
  change ((k + 2 * j).fib : ℚ) + (-1 : ℚ) ^ j * k.fib =
    (MetaMathlibExt.lucasNumber j : ℚ) * (k + j).fib
  rw [two_mul j]
  rify
  simp only [← MetaMathlibExt.cb_lucas_binet, Real.coe_fib_eq, ← Real.goldenRatio_mul_goldenConj,
    pow_add, mul_pow]
  ring

private theorem fibAtInt_neg_natCast (j : ℕ) :
    fibAtInt (-(j : ℤ)) = -((-1 : ℚ) ^ j * fibAtInt j) := by
  simp [fibAtInt, Int.fib_neg_natCast, pow_succ, neg_mul]

private theorem fib_step_recurrence (j n : ℕ) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) +
        (-1 : ℚ) ^ j * fibAtInt ((j : ℤ) * ((n : ℤ) - 1)) =
      lucasAtInt j * fibAtInt ((j : ℤ) * (n : ℤ)) := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, mul_one, zero_sub, mul_neg, mul_zero, fibAtInt_neg_natCast,
      show fibAtInt 0 = 0 by rfl]
    rw [← mul_assoc, ← pow_add, show j + j = 2 * j by omega, pow_mul]
    norm_num
  | succ n =>
    simpa only [Nat.cast_succ, add_sub_cancel_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      mul_add, mul_one, two_mul, add_assoc] using fibAtInt_add_two_mul j (j * n)

-- The proof also works at step zero; retain the source's hypothesis and binder name.
set_option linter.unusedVariables false in
/-- **Step extension of Sury's identity for Fibonacci numbers.** Let $F_n$ and $L_n$ be the
Fibonacci and Lucas numbers at integer indices. For all natural numbers $j \ge 1$ and $n$,
$$L_j^{n+1} F_{j(n-1)} + (-1)^{j(n+1)} F_{2j} = \sum_{i=0}^{n} (-1)^{j(n+i)} L_j^i F_{ji}.$$

When $n = 0$ the index $j(n-1) = -j$ is negative, so $F_{-j} = (-1)^{j+1} F_j$ enters.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 3. -/
public theorem fib_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    lucasAtInt (j : ℤ) ^ (n + 1) *
          fibAtInt ((j : ℤ) * ((n : ℤ) - 1)) +
        (-1 : ℚ) ^ (j * (n + 1)) * fibAtInt (2 * (j : ℤ)) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * lucasAtInt (j : ℤ) ^ i *
          fibAtInt ((j : ℤ) * (i : ℤ)) := by
  have hdouble : fibAtInt (2 * (j : ℤ)) = lucasAtInt j * fibAtInt j := by
    simpa only [Nat.cast_zero, zero_add, Nat.cast_mul, Nat.cast_ofNat, mul_zero, add_zero,
      show fibAtInt 0 = 0 by rfl] using fibAtInt_add_two_mul j 0
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_sub, mul_neg, mul_one, fibAtInt_neg_natCast, zero_add,
      pow_one, hdouble, Finset.sum_range_one, mul_zero, show fibAtInt 0 = 0 by rfl]
    ring
  | succ n ih =>
    -- Each summand up to `n` acquires the same factor `(-1)^j`.
    have hterm (i : ℕ) :
        (-1 : ℚ) ^ (j * (n + 1 + i)) * lucasAtInt j ^ i * fibAtInt ((j : ℤ) * (i : ℤ)) =
          (-1 : ℚ) ^ j *
            ((-1 : ℚ) ^ (j * (n + i)) * lucasAtInt j ^ i * fibAtInt ((j : ℤ) * (i : ℤ))) := by
      rw [show n + 1 + i = 1 + (n + i) by omega, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    have hlast : (-1 : ℚ) ^ (j * (n + 1 + (n + 1))) = 1 :=
      Even.neg_one_pow ⟨j * (n + 1), Nat.mul_add ..⟩
    rw [Finset.sum_range_succ, hlast, one_mul]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← ih, Nat.cast_succ, add_sub_cancel_right,
      pow_succ (lucasAtInt (j : ℤ)) (n + 1), Nat.mul_succ j (n + 1), pow_add]
    linear_combination -lucasAtInt (j : ℤ) ^ (n + 1) * fib_step_recurrence j n

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
