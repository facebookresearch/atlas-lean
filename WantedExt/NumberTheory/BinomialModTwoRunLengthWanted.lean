/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PadovanSequence

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

open Matrix

/-- **Run lengths of a digit list.** Given a list $b_1, \dots, b_k$ of natural numbers (binary
digits) and a natural number $c$, this is the list, in order of occurrence, of the lengths of the
maximal runs of $1$s in the sequence consisting of $c$ ones followed by $b_1, \dots, b_k$, where
every digit other than $1$ ends a run.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def bitRunLengths : List ℕ → ℕ → List ℕ
  | [], c => if c = 0 then [] else [c]
  | b :: bs, c =>
    if b = 1 then bitRunLengths bs (c + 1)
    else if c = 0 then bitRunLengths bs 0 else c :: bitRunLengths bs 0

/-- **Binary run lengths.** For a natural number $n$, the binary run lengths of $n$ form the list
of the lengths of the maximal runs of $1$s in the binary expansion of $n$, in the order in which
the runs occur when the digits are read from the least significant one. This is the paper's list
$\mathcal{L}(n)$, whose order does not matter there; for $n = 0$ the list is empty.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def binaryRunLengths (n : ℕ) : List ℕ :=
  bitRunLengths (Nat.digits 2 n) 0

/-- **Run length transform.** For a sequence $S : \mathbb{N} \to \mathbb{Z}$, the run length
transform of $S$ is the sequence $T : \mathbb{N} \to \mathbb{Z}$ given by
$T(n) = \prod_{\ell \in \mathcal{L}(n)} S(\ell)$, where $\mathcal{L}(n)$ is the list of the
lengths of the maximal runs of $1$s in the binary expansion of $n$, so that each run contributes
one factor.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def runLengthTransform (S : ℕ → ℤ) (n : ℕ) : ℤ :=
  ((binaryRunLengths n).map S).prod

/-- **Run length transform at zero.** For every sequence $S : \mathbb{N} \to \mathbb{Z}$, the run
length transform of $S$ takes the value $1$ at $0$, since $0$ has no runs of $1$s in binary.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public theorem runLengthTransform_zero (S : ℕ → ℤ) : runLengthTransform S 0 = 1 := by
  simp [runLengthTransform, binaryRunLengths, bitRunLengths]

/-- **Run length transform at eleven.** For every sequence $S : \mathbb{N} \to \mathbb{Z}$, the run
length transform $T$ of $S$ satisfies $T(11) = S(1) S(2)$: in binary $11$ is $1011$, whose maximal
runs of $1$s have lengths $2$ and $1$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, example after Definition 1. -/
public theorem runLengthTransform_eleven (S : ℕ → ℤ) : runLengthTransform S 11 = S 1 * S 2 := by
  have hd : Nat.digits 2 11 = [1, 1, 0, 1] := by norm_num
  have h : binaryRunLengths 11 = [2, 1] := by
    rw [binaryRunLengths, hd]
    decide
  rw [runLengthTransform, h]
  simp [mul_comm]

/-- **Linear recurrences via powers of the companion matrix.** Let $r$ be a natural number, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for every $m \ge r$. Let $\gamma(1)$
be the $(r + 1) \times (r + 1)$ integer matrix with rows and columns indexed by $0, \dots, r$
whose row $i < r$ has a $1$ in column $i + 1$ and zeros elsewhere, and whose last row is
$(d_r, d_{r-1}, \dots, d_0)$. With $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^{T}$,
we have $S(n) = v \, \gamma(1)^n \, w$ for every natural number $n$.

The values $S(1), \dots, S(r)$ are arbitrary.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 1. -/
public theorem_wanted linearRecurrence_eq_companion_pow (r : ℕ) (d : Fin (r + 1) → ℤ)
    (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    S n = Pi.single 0 1 ⬝ᵥ
      ((Matrix.of fun i j : Fin (r + 1) =>
          if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)) ^ n *ᵥ
        fun i => S i)

/-- **Run length transform of a linear recurrence (Rampersad–Wiebe Theorem 1).** Let $r \ge 0$, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for all $m \ge r$. Let $T$ be the run
length transform of $S$, let $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^\top$, let
$\gamma(0)$ be the $(r + 1) \times (r + 1)$ matrix with first column $w$ and zeros elsewhere, and
let $\gamma(1)$ be the $(r + 1) \times (r + 1)$ companion matrix with ones on the superdiagonal,
last row $(d_r, \dots, d_0)$ and zeros elsewhere. Then for every natural number $n$ with binary
digits $b_1 b_2 \cdots b_t$, most significant first,
$T(n) = v \, \gamma(b_1) \gamma(b_2) \cdots \gamma(b_t) \, w$, where for $n = 0$ the product of
matrices is empty and equals the identity.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 1. -/
public theorem_wanted runLengthTransform_linearRecurrence_eq_linearRep (r : ℕ)
    (d : Fin (r + 1) → ℤ) (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    runLengthTransform S n = Pi.single 0 1 ⬝ᵥ
      ((((Nat.digits 2 n).reverse.map fun b =>
          if b = 0 then Matrix.of fun i j : Fin (r + 1) => if j = 0 then S i else 0
          else Matrix.of fun i j : Fin (r + 1) =>
            if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)).prod) *ᵥ
        fun i => S i)

/-- **Rampersad–Wiebe Theorem 2.** Let $(F_j)_{j \ge 0}$ be the Fibonacci numbers, $F_0 = 0$,
$F_1 = 1$, and let $T$ be the run length transform of $S(i) = F_{i+1}$, i.e. of
$1, 1, 2, 3, 5, 8, \dots$. Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{n - k}{2k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 2. -/
public theorem_wanted runLengthTransform_choose_sub_two_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 1) : ℤ)) n

/-- **Rampersad–Wiebe Theorem 3.** Let $(F_j)_{j \ge 0}$ be the Fibonacci numbers, $F_0 = 0$,
$F_1 = 1$, and let $T$ be the run length transform of $S(i) = F_{i+2}$, i.e. of
$1, 2, 3, 5, 8, \dots$. Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{3k}{k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 3. -/
public theorem_wanted runLengthTransform_choose_three_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((3 * k).choose k * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 2) : ℤ)) n

/-- **Rampersad–Wiebe Theorem 4.** Let $T$ be the run length transform of the sequence $S$ with
$S(0) = 1$ and $S(i) = 2^{i-1}$ for $i \ge 1$, i.e. of $1, 1, 2, 4, 8, \dots$. Then for every
natural number $n$, $\sum_{k=0}^{n} \left(\binom{n}{2k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 4. -/
public theorem_wanted runLengthTransform_choose_two_mul_pow_two (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), (n.choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i = 0 then 1 else 2 ^ (i - 1)) n

/-- **Sum of $\binom{n+2k}{2k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+2k}{2k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S$ with $S(0) = 1$ and
$S(i) = 2$ for $i \ge 1$, that is, $1, 2, 2, 2, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 5. -/
public theorem_wanted runLengthTransform_choose_add_two_mul_one_two (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 2 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i = 0 then 1 else 2) n

/-- **Sum of $\binom{n+k}{n-k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+k}{n-k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S(i) = i + 1$ of positive
integers $1, 2, 3, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 6. -/
public theorem_wanted runLengthTransform_choose_add_sub_succ (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i + 1 : ℤ)) n

/-- **Rampersad–Wiebe Theorem 7.** Let $(N_j)_{j \ge 0}$ be Narayana's cows sequence, $N_0 = 0$,
$N_1 = N_2 = 1$ and $N_j = N_{j-1} + N_{j-3}$ for $j \ge 3$, and let $T$ be the run length
transform of $S(i) = N_{i+1}$, i.e. of $1, 1, 1, 2, 3, 4, 6, 9, \dots$. Then for every natural
number $n$, $\sum_{k=0}^{n} \left(\binom{n - k}{6k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 7. -/
public theorem_wanted runLengthTransform_choose_sub_six_mul_narayanaCows (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (narayanaCowsSequence (i + 1) : ℤ)) n

/-- **Sum of $\binom{n+3k}{6k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+3k}{6k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence
$S(i) = \lfloor i / 2 \rfloor + 1$ of doubled positive integers $1, 1, 2, 2, 3, 3, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 8. -/
public theorem_wanted runLengthTransform_choose_add_three_mul_six_mul_doubled (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 3 * k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i / 2 + 1 : ℤ)) n

/-- **Sum of $\binom{n+2k}{2n-k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+2k}{2n-k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S$ with $S(0) = S(1) = 1$
and $S(i) = L_{i-2}$ for $i \ge 2$, where $L_0 = 2, L_1 = 1, L_2 = 3, \dots$ are the Lucas
numbers; that is, $S$ is $1, 1, 2, 1, 3, 4, 7, 11, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
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

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 12. -/
public theorem_wanted runLengthTransform_choose_seven_mul_sub_padovan_five (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((7 * k - n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence (i + 2) : ℤ)) n

/-- **Sum of $\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the shifted Padovan sequence $P$, given by
$P(0) = 1$, $P(1) = 0$, $P(2) = 1$ and $P(i + 3) = P(i + 1) + P(i)$, that is,
$1, 0, 1, 1, 1, 2, 2, 3, \dots$ (the Padovan numbers, OEIS A000931, from offset $3$).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 13. -/
public theorem_wanted runLengthTransform_choose_add_seven_mul_padovan_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 7 * k).choose (3 * n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence i : ℤ)) n

/-- **Rampersad–Wiebe Theorem 14.** Let $T$ be the run length transform of the sequence $S$ with
$S(i) = 1$ for even $i$ and $S(i) = (i + 1)/2$ for odd $i$, i.e. of $1, 1, 1, 2, 1, 3, 1, 4, \dots$.
Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{6k}{n + 3k} \binom{n}{k} \bmod 2\right) = T(n)$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
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

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 15. -/
public theorem_wanted runLengthTransform_choose_eight_mul_sub_period_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((8 * k - 2 * n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i % 3 = 2 then 0 else 1) n

/-- **Sum of $\binom{n+5k}{2n+2k}\binom{n}{k} \bmod 2$ as a run length transform.** Let
$S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = S(1) = S(2) = S(3) = 1$ and
$S(m) = S(m - 1) + S(m - 2) - S(m - 3) + S(m - 4)$ for every $m \ge 4$. Then for every natural
number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+5k}{2n+2k}\binom{n}{k} \bmod 2\bigr)$ equals
the value at $n$ of the run length transform of $S$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 10. -/
public theorem_wanted runLengthTransform_choose_add_five_mul_two_mul_add_two_mul (S : ℕ → ℤ)
    (h0 : S 0 = 1) (h1 : S 1 = 1) (h2 : S 2 = 1)
    (h3 : S 3 = 1) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * n + 2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n

/-- **Sum of $\binom{n+5k}{2k}\binom{n}{k} \bmod 2$ as a run length transform.** Let
$S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$, $S(1) = S(2) = 2$, $S(3) = 3$ and
$S(m) = S(m - 1) + S(m - 2) - S(m - 3) + S(m - 4)$ for every $m \ge 4$. Then for every natural
number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+5k}{2k}\binom{n}{k} \bmod 2\bigr)$ equals the
value at $n$ of the run length transform of $S$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 11. -/
public theorem_wanted runLengthTransform_choose_add_five_mul_two_mul (S : ℕ → ℤ) (h0 : S 0 = 1)
    (h1 : S 1 = 2) (h2 : S 2 = 2)
    (h3 : S 3 = 3) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n

/-- **Binomial parity sums at one less than a power of two.** For all natural numbers $m$ and
$\ell$, with $n = 2^\ell - 1$, the sum
$$\sum_{k=0}^{n} \left( \binom{2^m k}{n + k} \binom{n}{k} \bmod 2 \right)$$
equals $1$ if $m$ divides $\ell$, and $0$ otherwise.

The paper takes $m \ge 2$; the statement holds for every $m$, where $0$ divides $\ell$ only
when $\ell = 0$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 2. -/
public theorem_wanted sum_choose_two_pow_mul_mod_two_two_pow_sub_one (m ℓ : ℕ) :
    ∑ k ∈ Finset.range (2 ^ ℓ - 1 + 1), ((2 ^ m * k).choose (2 ^ ℓ - 1 + k) * (2 ^ ℓ -
        1).choose k) % 2 =
      if m ∣ ℓ then 1 else 0

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
