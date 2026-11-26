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

/-- **Self-convolution of higher-order Fibonacci numbers.** Let $m \ge 1$ and let
$(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $p \ge 0$ let $w_p = \sum_{j=0}^{p} F_{j+m-1} F_{p-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 2m - 2$, writing $p = n - 2m + 2$,

$$
\sum_{i=0}^{n} F_i F_{n-i} = w_p = \left(\frac{2m}{m+1}\right)^{p} +
\frac{(2m)^{p-1}}{(m+1)^{p}} \bigl((m+2) S(p-1, m, q) + S_2(p-1, m, q) -
m S(p-1, m-1, q) - S_2(p-1, m-1, q)\bigr).
$$

The source states the formula for all $n \ge 0$, but for $m \ge 2$ it fails when
$n < 2m - 2$: at $m = 2$ and $n = 0$ the left side is $0$ and the right side is $9/16$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 4. -/
theorem_wanted higherFib_selfConvolution_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) (hn : 2 * m - 2 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        higherFibWalk F m (n - (2 * m - 2)) ∧
      (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ ((n : ℤ) - 2 * (m : ℤ) + 2) +
          ((2 * (m : ℚ)) ^ ((n : ℤ) - 2 * (m : ℤ) + 1) /
              ((m : ℚ) + 1) ^ ((n : ℤ) - 2 * (m : ℤ) + 2)) *
            (((m : ℚ) + 2) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  (m : ℤ) (((m : ℚ) + 1) / (2 * (m : ℚ))) +
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              (m : ℚ) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ))))

/-- **Halving the Fibonacci self-convolution at even length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k} = (v_{2k} + F_{2k+2})/2$ and $O_{2k} = (v_{2k} - F_{2k+2})/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem_wanted fibWalkCounts_even_length_eq
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)) / 2 ∧
      oddFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) - fibQ (2 * (k : ℤ) + 2)) / 2

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
