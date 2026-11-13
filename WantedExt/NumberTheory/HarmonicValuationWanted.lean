/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Weighted binary digit sum.** For a natural number $n$, the weighted binary digit sum of $n$
is $a(n) = \sum_i i \cdot 2^i$, where $i$ runs over the indices of the $1$ bits in the binary
expansion of $n$. Equivalently, if $n = 2^{a_1} + \dots + 2^{a_t}$ with distinct exponents
$a_1, \dots, a_t$, then $a(n) = a_1 2^{a_1} + \dots + a_t 2^{a_t}$; in particular $a(0) = 0$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2 and Theorem 4; the
first values `0, 0, 2, 2, 8, 8, 10, 10, 24, ...` are displayed there. -/
public def weightedBinaryDigitSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log 2 n + 1), if Nat.testBit n i then i * 2 ^ i else 0

/-- **Weighted binary digit sum of 2.** The weighted binary digit sum of $2$ is $a(2) = 2$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4 (displayed values). -/
public theorem weightedBinaryDigitSum_two : weightedBinaryDigitSum 2 = 2 := by
  decide

/-- **Weighted binary digit sum of 4.** The weighted binary digit sum of $4$ is $a(4) = 8$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4 (displayed values). -/
public theorem weightedBinaryDigitSum_four : weightedBinaryDigitSum 4 = 8 := by
  decide

/-- **Kürschák's strengthening of Theisinger's theorem.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the
$k$-th harmonic number (so $H_0 = 0$) and let $\nu_2$ denote the $2$-adic valuation on the
rational numbers. For all natural numbers $m$ and $n$ with $m + 2 \le n$, the $2$-adic valuation
$\nu_2(H_n - H_m)$ is negative; that is, $H_n - H_m$ is not a $2$-adic integer.

In particular $H_n - H_m$ is not an integer.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 2 (`integers-2024-A27-thm-2`). for `0 ≤ m ≤ n - 2` the difference `H_n - H_m` does not lie
in the ring of `2`-adic integers. -/
public theorem_wanted padicValRat_two_harmonic_sub_neg (m n : ℕ)
    (h : m + 2 ≤ n) :
    padicValRat 2 (harmonic n - harmonic m) < 0

/-- **Fiber counts of the 2-adic valuations of $H_n - H_m$.** Let $H_k = \sum_{j=1}^{k} 1/j$ be
the $k$-th harmonic number (so $H_0 = 0$) and let $\nu_2$ denote the $2$-adic valuation on the
rational numbers. Let $n$ and $a$ be natural numbers such that the binary digit of $n$ in
position $a$ is $1$, that is, $2^a$ occurs in the binary expansion of $n$. Then exactly $2^a$ of
the natural numbers $m < n$ satisfy $\nu_2(H_n - H_m) = -a$.

The source theorem also locates these values of $m$ in intervals determined by the partial sums
of the binary expansion of $n$; that refinement is not part of this statement.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 3 (`integers-2024-A27-thm-3`):
writing `n = ∑_{i=1}^{t} 2^{aᵢ}` in binary, among the values
`ν₂(H_n - H_m)` for `m = 0, 1, …, n - 1` exactly `2^{aᵢ}` are equal to
`-aᵢ`, for each exponent `aᵢ` occurring in the expansion. -/
public theorem_wanted card_filter_padicValRat_two_harmonic_sub (n a : ℕ)
    (ha : Nat.testBit n a = true) :
    ((Finset.range n).filter
      (fun m => padicValRat 2 (harmonic n - harmonic m) = -(a : ℤ))).card
      = 2 ^ a

/-- **2-adic valuation of $H_{2n} - H_n$.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th harmonic
number and let $\nu_2$ denote the $2$-adic valuation on the rational numbers. For every natural
number $n \ge 1$, $\nu_2(H_{2n} - H_n) = -\lfloor \log_2(2n) \rfloor$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Lemma 1 (`integers-2024-A27-lem-1`): for `n ≥ 1`,
`ν₂(H_{2n} - H_n) = -⌊log₂(2n)⌋`. -/
public theorem_wanted padicValRat_two_harmonic_two_mul_sub (n : ℕ)
    (hn : 1 ≤ n) :
    padicValRat 2 (harmonic (2 * n) - harmonic n) = -(Nat.log 2 (2 * n) : ℤ)

/-- **2-adic valuation of $H_{2^a} - H_{2^a - m}$.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th
harmonic number (so $H_0 = 0$) and let $\nu_2$ denote the $2$-adic valuation on the rational
numbers. For all natural numbers $a$ and $m$ with $1 \le m \le 2^a$,
$\nu_2(H_{2^a} - H_{2^a - m}) = -a$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Corollary 1 (`integers-2024-A27-cor-1`): if `n = 2^a` is a
power of `2` then `ν₂(H_n - H_{n-m}) = -a` for every `1 ≤ m ≤ n`. -/
public theorem_wanted padicValRat_two_harmonic_pow_sub (a m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ a) :
    padicValRat 2 (harmonic (2 ^ a) - harmonic (2 ^ a - m)) = -(a : ℤ)

/-- **Sum of the 2-adic valuations of $H_n - H_m$.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th
harmonic number (so $H_0 = 0$), let $\nu_2$ denote the $2$-adic valuation on the rational
numbers, and let $a(n)$ be the weighted binary digit sum of $n$. For every natural number $n$,
$\sum_{m=0}^{n-1} \nu_2(H_n - H_m) = -a(n)$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2 (`integers-2024-A27-cor-2`):
`∑_{m=0}^{n-1} ν₂(H_n - H_m) = -a(n)`, where `a(n) = weightedBinaryDigitSum n`. -/
public theorem_wanted sum_padicValRat_two_harmonic_sub (n : ℕ) :
    ∑ m ∈ Finset.range n, padicValRat 2 (harmonic n - harmonic m)
      = -(weightedBinaryDigitSum n : ℤ)

/-- **Recurrence for the weighted binary digit sum.** Let $a(n)$ denote the weighted binary digit
sum of $n$. For every natural number $n$, $a(2n) = 2a(n) + 2n$ and $a(2n + 1) = a(2n)$.

The source theorem also gives a two-variable generating function, which is not part of this
statement.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 4 (`integers-2024-A27-thm-4`): the
weighted binary digit sum satisfies `a(2n) = 2a(n) + 2n` and
`a(2n + 1) = a(2n)`, with `a(0) = a(1) = 0`. -/
public theorem_wanted weightedBinaryDigitSum_recurrence (n : ℕ) :
    weightedBinaryDigitSum (2 * n) = 2 * weightedBinaryDigitSum n + 2 * n ∧
    weightedBinaryDigitSum (2 * n + 1) = weightedBinaryDigitSum (2 * n)

/-- **2-adic valuation of $H_n - H_{n-2^r}$.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th
harmonic number and let $\nu_2$ denote the $2$-adic valuation on the rational numbers. For all
natural numbers $r$ and $n$ with $2^r \le n$,
$\nu_2(H_n - H_{n-2^r}) = -r - \nu_2(\lfloor n / 2^r \rfloor)$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 5 (`integers-2024-A27-thm-5`): for `m = 2^r` with
`1 ≤ m ≤ n`, `ν₂(H_n - H_{n-m}) = -r - ν₂(⌊n / m⌋)`. -/
public theorem_wanted padicValRat_two_harmonic_sub_pow (r n : ℕ)
    (h : 2 ^ r ≤ n) :
    padicValRat 2 (harmonic n - harmonic (n - 2 ^ r))
      = -(r : ℤ) - ((n / 2 ^ r).factorization 2 : ℤ)

/-- **Piecewise formula for the 2-adic valuation of $H_n - H_{n-m}$.** Let
$H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th harmonic number and let $\nu_2$ denote the $2$-adic
valuation on the rational numbers (for a positive integer it is the exponent of $2$ in its
factorization). Let $m$ and $n$ be natural numbers with $1 \le m \le n$, and put
$M = \lceil \log_2(m + 1) \rceil$ and $j = \lfloor (n - m) / 2^M \rfloor$. If
$2^M j + m \le n \le 2^M (j + 1) - 1$, then $\nu_2(H_n - H_{n-m}) = 1 - M$. If
$2^M (j + 1) \le n \le 2^M (j + 1) + m - 1$, then $\nu_2(H_n - H_{n-m}) = -M - \nu_2(j + 1)$.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 6, formula (3.1) (`integers-2024-A27-thm-6`): let
`M = ⌈log₂(m + 1)⌉` and `j = ⌊(n - m) / 2^M⌋`, where `1 ≤ m ≤ n`. Then
`ν₂(H_n - H_{n-m}) = -M + 1` when `2^M * j + m ≤ n ≤ 2^M * (j + 1) - 1`, and
`ν₂(H_n - H_{n-m}) = -M - ν₂(j + 1)` when
`2^M * (j + 1) ≤ n ≤ 2^M * (j + 1) + m - 1`. -/
public theorem_wanted padicValRat_two_harmonic_sub_piecewise (m n : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1))) + m ≤ n ∧
        n + 1 ≤ 2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ) + 1) ∧
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) ≤ n ∧
        n + 1 ≤ 2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) + m →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ)
          - (((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1).factorization 2 : ℤ))

end

end MetaMathlibExt
