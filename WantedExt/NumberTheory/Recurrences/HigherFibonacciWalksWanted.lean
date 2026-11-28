/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Walks in tiled rectangles and higher-order Fibonacci convolutions

Statements from Jan Sedlák and Antonín Slavík, "Walks in Tiled
Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.3.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Slavik/slavik4.html>).

Sequences are integer-indexed and valued in `ℚ`.  For `m ≥ 1`, an
`m`-step Fibonacci recurrence means
`F n = F (n-1) + ⋯ + F (n-m)` for every integer `n`.  The standard
sequence also has `F 0 = ⋯ = F (m-2) = 0` and `F (m-1) = 1`.

The weighted sums `S` and `S₂` allow an integer upper limit; a
negative upper limit gives the empty sum.  This is the convention
needed at `n = 0` in Theorem 3.

Theorem 4 is stated for `n ≥ 2*m - 2`.  The printed theorem says
all `n ≥ 0`, but its derivation substitutes `n - 2*m + 2` into a
formula for `w` at a nonnegative index.  Under the empty-sum
convention the unrestricted displayed formula already fails at
`(m, n) = (2, 0)`: the self-convolution is `0`, while the formula
gives `9 / 16`.  The restricted range is therefore recorded
explicitly here and in the source-audit table.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksEvenFibWalkCountEvenLengthEqOddAddFib
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksOddLengthHalf
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksFibWalkCountsEvenLengthEq
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksSelfConvolution

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- **Recurrence for the shifted self-convolution of higher-order Fibonacci numbers.** Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$, and for $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$. Then for
every integer $n \ge 0$, $(m+1) w_{n+1} - 2m w_n = (n+m+2) F_{n+m} - (n+m) F_{n+m-1}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 1. -/
theorem_wanted higherFibWalk_recurrence
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    ((m : ℚ) + 1) * higherFibWalk F m (n + 1) -
        2 * (m : ℚ) * higherFibWalk F m n =
      ((n : ℚ) + (m : ℚ) + 2) * F ((n : ℤ) + (m : ℤ)) -
        ((n : ℚ) + (m : ℚ)) * F ((n : ℤ) + (m : ℤ) - 1)

/-- **Explicit formula for the shifted self-convolution of higher-order Fibonacci numbers.** Let
$m \ge 1$ and let $(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $n \ge 0$ let $w_n = \sum_{j=0}^{n} F_{j+m-1} F_{n-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 0$,

$$
w_n = \left(\frac{2m}{m+1}\right)^{n} +
\frac{(2m)^{n-1}}{(m+1)^{n}} \bigl((m+2) S(n-1, m, q) + S_2(n-1, m, q) -
m S(n-1, m-1, q) - S_2(n-1, m-1, q)\bigr).
$$

At $n = 0$ the weighted sums have upper limit $-1$ and are empty.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 3. -/
theorem_wanted higherFibWalk_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) :
    higherFibWalk F m n =
      (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ n +
        ((2 * (m : ℚ)) ^ ((n : ℤ) - 1) / ((m : ℚ) + 1) ^ n) *
          (((m : ℚ) + 2) *
              weightedHigherFibSum F m ((n : ℤ) - 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) +
            weightedHigherFibMomentSum F m ((n : ℤ) - 1) (m : ℤ)
              (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            (m : ℚ) *
              weightedHigherFibSum F m ((n : ℤ) - 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
            weightedHigherFibMomentSum F m ((n : ℤ) - 1)
              ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))))

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
