/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Sum of squares of a Tetranacci sequence

For a two-sided Tetranacci sequence with arbitrary initial values, the endpoint expression
`3 * Q n * Q (n + 1) - (Q (n + 1) - Q (n - 1)) ^ 2 + Q (n - 2) * (Q n + Q (n - 3))`
increases by `3 * Q (n + 1) ^ 2` from `n` to `n + 1`. Summing these increments gives the identity.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted

/-- **Sum of squares of a Tetranacci sequence.** Let $Q \colon \mathbb{Z} \to \mathbb{Z}$ satisfy
$Q(m+4) = Q(m+3) + Q(m+2) + Q(m+1) + Q(m)$ for every integer $m$. Then for every natural
number $n$,
$$3 \sum_{k=1}^{n} Q(k)^2 = 3\,Q(n)\,Q(n+1) - 3\,Q(0)\,Q(1) - \bigl(Q(n+1) - Q(n-1)\bigr)^2 +
\bigl(Q(1) - Q(-1)\bigr)^2 + Q(n-2)\bigl(Q(n) + Q(n-3)\bigr) - Q(-2)\bigl(Q(0) + Q(-3)\bigr).$$

Inside the boundary terms the sums $Q(n) + Q(n-3)$ and $Q(0) + Q(-3)$ carry a plus sign, as in
Gryszka's Lemma 2; this sign is the one forced by the paper's telescoping calculation.

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Theorem 2. -/
theorem three_mul_sum_tetranacci_sq
    (Q : ℤ → ℤ)
    (hQ : ∀ n : ℤ, Q (n + 4) =
      Q (n + 3) + Q (n + 2) + Q (n + 1) + Q n)
    (n : ℕ) :
    3 * (∑ k ∈ Finset.Icc 1 n, (Q k) ^ 2) =
      3 * Q n * Q ((n : ℤ) + 1) - 3 * Q 0 * Q 1 -
        (Q ((n : ℤ) + 1) - Q ((n : ℤ) - 1)) ^ 2 +
        (Q 1 - Q (-1)) ^ 2 +
        Q ((n : ℤ) - 2) * (Q n + Q ((n : ℤ) - 3)) -
        Q (-2) * (Q 0 + Q (-3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), mul_add, ih, Nat.cast_succ]
    -- Express the two newest terms in terms of the four preceding ones.
    have h₁ := hQ ((n : ℤ) - 3)
    have h₂ := hQ ((n : ℤ) - 2)
    simp only [sub_eq_add_neg, add_assoc, Int.reduceNeg, Int.reduceAdd, add_zero] at h₁ h₂ ⊢
    rw [h₂, h₁]
    ring

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted
