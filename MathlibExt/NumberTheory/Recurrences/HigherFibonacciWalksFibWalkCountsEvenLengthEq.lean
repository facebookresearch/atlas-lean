/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksEvenFibWalkCountEvenLengthEqOddAddFib

/-!
# Halving the Fibonacci self-convolution at even length

`fibWalkCounts_even_length_eq` expresses the even and odd parts of the Fibonacci
self-convolution at even length in terms of the full sum and a Fibonacci number.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of
Higher-Order Fibonacci Numbers", *Journal of Integer Sequences* 29 (2026), Article 26.3.7,
Theorem 6.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

private lemma even_odd_sum (n : ℕ) :
    evenFibWalkCount n + oddFibWalkCount n = fibWalkCount n := by
  simpa only [evenFibWalkCount, oddFibWalkCount, fibWalkCount, Nat.not_even_iff_odd] using
    Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) Even
      (fun j => fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - j + 1))

/-- **Halving the Fibonacci self-convolution at even length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k} = (v_{2k} + F_{2k+2})/2$ and $O_{2k} = (v_{2k} - F_{2k+2})/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem fibWalkCounts_even_length_eq
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)) / 2 ∧
      oddFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) - fibQ (2 * (k : ℤ) + 2)) / 2
    := by
  have hsum := even_odd_sum (2 * k)
  have hparity := evenFibWalkCount_even_length_eq_odd_add_fib k hk
  constructor <;> linarith only [hsum, hparity]

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
