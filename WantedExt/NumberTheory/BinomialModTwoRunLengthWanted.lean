/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.BinomialParitySum
public import MathlibExt.NumberTheory.BinomialParitySumFive
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PadovanSequence
public import MathlibExt.NumberTheory.RunLengthTransformLinearRecurrence

/-!
# Sums of products of binomial coefficients mod 2 as run length transforms

Statements from Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2
and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73 (arXiv:2309.04012).

The paper studies `T(n) = ∑_{k=0}^{n} [binom(a₁n + a₂k, a₃n + a₄k) binom(n, k) mod 2]`. Each summand
is written `(binom(·, ·) * binom(n, k)) % 2` in `ℕ`. The run length transform of `S` sends `n` to
the product of `S(ℓ)` over the lengths `ℓ` of the maximal runs of `1`s in the binary expansion of
`n` (the paper's example `T(11) = S(1) S(2)`; its display writes a sum by mistake).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Rampersad–Wiebe Theorem 2.** Let $(F_j)_{j \ge 0}$ be the Fibonacci numbers, $F_0 = 0$,
$F_1 = 1$, and let $T$ be the run length transform of $S(i) = F_{i+1}$, i.e. of
$1, 1, 2, 3, 5, 8, \dots$. Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{n - k}{2k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 2. -/
public theorem_wanted runLengthTransform_choose_sub_two_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 1) : ℤ)) n

/-- **Rampersad–Wiebe Theorem 3.** Let $(F_j)_{j \ge 0}$ be the Fibonacci numbers, $F_0 = 0$,
$F_1 = 1$, and let $T$ be the run length transform of $S(i) = F_{i+2}$, i.e. of
$1, 2, 3, 5, 8, \dots$. Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{3k}{k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 3. -/
public theorem_wanted runLengthTransform_choose_three_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((3 * k).choose k * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 2) : ℤ)) n

/-- **Sum of $\binom{n+2k}{2k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+2k}{2k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S$ with $S(0) = 1$ and
$S(i) = 2$ for $i \ge 1$, that is, $1, 2, 2, 2, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 5. -/
public theorem_wanted runLengthTransform_choose_add_two_mul_one_two (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 2 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i = 0 then 1 else 2) n

/-- **Sum of $\binom{n+k}{n-k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+k}{n-k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S(i) = i + 1$ of positive
integers $1, 2, 3, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 6. -/
public theorem_wanted runLengthTransform_choose_add_sub_succ (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i + 1 : ℤ)) n

/-- **Rampersad–Wiebe Theorem 7.** Let $(N_j)_{j \ge 0}$ be Narayana's cows sequence, $N_0 = 0$,
$N_1 = N_2 = 1$ and $N_j = N_{j-1} + N_{j-3}$ for $j \ge 3$, and let $T$ be the run length
transform of $S(i) = N_{i+1}$, i.e. of $1, 1, 1, 2, 3, 4, 6, 9, \dots$. Then for every natural
number $n$, $\sum_{k=0}^{n} \left(\binom{n - k}{6k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 7. -/
public theorem_wanted runLengthTransform_choose_sub_six_mul_narayanaCows (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (narayanaCowsSequence (i + 1) : ℤ)) n

/-- **Sum of $\binom{n+3k}{6k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+3k}{6k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence
$S(i) = \lfloor i / 2 \rfloor + 1$ of doubled positive integers $1, 1, 2, 2, 3, 3, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 8. -/
public theorem_wanted runLengthTransform_choose_add_three_mul_six_mul_doubled (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 3 * k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i / 2 + 1 : ℤ)) n

/-- **Sum of $\binom{n+2k}{2n-k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+2k}{2n-k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S$ with $S(0) = S(1) = 1$
and $S(i) = L_{i-2}$ for $i \ge 2$, where $L_0 = 2, L_1 = 1, L_2 = 3, \dots$ are the Lucas
numbers; that is, $S$ is $1, 1, 2, 1, 3, 4, 7, 11, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 9. -/
public theorem_wanted runLengthTransform_choose_add_two_mul_two_mul_sub_lucas (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 2 * k).choose (2 * n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i < 2 then 1 else (lucasNumber (i - 2) : ℤ)) n

/-- **Rampersad–Wiebe Theorem 12.** Let $(p_j)_{j \ge 0}$ be the shifted Padovan sequence,
$p_0 = 1$, $p_1 = 0$, $p_2 = 1$ and $p_{j+3} = p_{j+1} + p_j$, and let $T$ be the run length
transform of $S(i) = p_{i+2}$, i.e. of $1, 1, 1, 2, 2, 3, 4, 5, \dots$ (the Padovan numbers,
OEIS A000931, from offset $5$). Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{7k - n}{n + k} \binom{n}{k} \bmod 2\right) = T(n)$, where a binomial
coefficient $\binom{a}{b}$ with $a < 0$ is $0$.

Equivalently, a negative top entry $7k - n$ may be replaced by $0$, since the bottom entry $n + k$
is then positive.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 12. -/
public theorem_wanted runLengthTransform_choose_seven_mul_sub_padovan_five (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((7 * k - n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence (i + 2) : ℤ)) n

/-- **Sum of $\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the shifted Padovan sequence $P$, given by
$P(0) = 1$, $P(1) = 0$, $P(2) = 1$ and $P(i + 3) = P(i + 1) + P(i)$, that is,
$1, 0, 1, 1, 1, 2, 2, 3, \dots$ (the Padovan numbers, OEIS A000931, from offset $3$).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 13. -/
public theorem_wanted runLengthTransform_choose_add_seven_mul_padovan_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 7 * k).choose (3 * n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence i : ℤ)) n

/-- **Rampersad–Wiebe Theorem 14.** Let $T$ be the run length transform of the sequence $S$ with
$S(i) = 1$ for even $i$ and $S(i) = (i + 1)/2$ for odd $i$, i.e. of $1, 1, 1, 2, 1, 3, 1, 4, \dots$.
Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{6k}{n + 3k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 14. -/
public theorem_wanted runLengthTransform_choose_six_mul_alternating (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((6 * k).choose (n + 3 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if Even i then 1 else (i / 2 + 1 : ℤ)) n

/-- **Rampersad–Wiebe Theorem 15.** Let $T$ be the run length transform of the periodic sequence
$S$ with $S(i) = 0$ if $i \equiv 2 \pmod 3$ and $S(i) = 1$ otherwise, i.e. of
$1, 1, 0, 1, 1, 0, \dots$. Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{8k - 2n}{n + k} \binom{n}{k} \bmod 2\right) = T(n)$, where a binomial
coefficient $\binom{a}{b}$ with $a < 0$ is $0$.

Equivalently, a negative top entry $8k - 2n$ may be replaced by $0$, since the bottom entry $n + k$
is then positive.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 15. -/
public theorem_wanted runLengthTransform_choose_eight_mul_sub_period_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((8 * k - 2 * n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i % 3 = 2 then 0 else 1) n

/-- **Sum of $\binom{n+5k}{2k}\binom{n}{k} \bmod 2$ as a run length transform.** Let
$S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$, $S(1) = S(2) = 2$, $S(3) = 3$ and
$S(m) = S(m - 1) + S(m - 2) - S(m - 3) + S(m - 4)$ for every $m \ge 4$. Then for every natural
number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+5k}{2k}\binom{n}{k} \bmod 2\bigr)$ equals the
value at $n$ of the run length transform of $S$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 11. -/
public theorem_wanted runLengthTransform_choose_add_five_mul_two_mul (S : ℕ → ℤ) (h0 : S 0 = 1)
    (h1 : S 1 = 2) (h2 : S 2 = 2)
    (h3 : S 3 = 3) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n

/-- **Binomial parity sums detect run length divisibility.** For all natural numbers $m$ and $n$,
the sum
$$\sum_{k=0}^{n} \left( \binom{2^m k}{n + k} \binom{n}{k} \bmod 2 \right)$$
equals $1$ if every maximal run of $1$s in the binary expansion of $n$ has length divisible by
$m$, and $0$ otherwise.

The paper takes $m \ge 2$; the statement holds for every $m$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 16. -/
public theorem_wanted sum_choose_two_pow_mul_mod_two_eq (m n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((2 ^ m * k).choose (n + k) * n.choose k) % 2 =
      if ∀ ℓ ∈ binaryRunLengths n, m ∣ ℓ then 1 else 0

end

end MetaMathlibExt
