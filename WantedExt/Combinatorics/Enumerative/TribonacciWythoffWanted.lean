/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.InfiniteWord.Tribonacci
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

/-!
# Tribonacci analogues of Wythoff-array facts (statements)

Statement-only targets from Chen, Ge, Kalashnikov, Kim, Liang, Lubashev, Qian, Raghavan,
Taycher, Wang and Khovanova, *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*. Tribonacci numbers are `MetaMathlibExt.tribonacci`
(`T₀ = T₁ = 0`, `T₂ = 1`), the Tribonacci word is `InfiniteWord.tribonacciWord`
(0-indexed), and a Tribonacci representation is a digit list written least significant
digit first, digit `i` carrying weight `T_{i+3}` (so the last printed digit has weight `1`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Tribonacci representation.** Let $T_n$ be the Tribonacci numbers, $T_0 = T_1 = 0$,
$T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$. A list $w = (w_0, \dots, w_{\ell-1})$ of
natural numbers, read least significant digit first, is a Tribonacci representation of a
natural number $n$ when every digit $w_i$ is $0$ or $1$, no three consecutive entries of $w$
are all equal to $1$, and $n = \sum_{i=0}^{\ell-1} w_i T_{i+3}$. Leading zeros (trailing
entries of $w$) are allowed.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3 (Tribonacci representation). -/
public def IsTribonacciRepr (w : List ℕ) (n : ℕ) : Prop :=
  (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w ∧
    ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3) = n

/-- **The empty word represents zero.** The empty digit list is a Tribonacci representation
of $0$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem isTribonacciRepr_nil : IsTribonacciRepr [] 0 := by
  simp [IsTribonacciRepr]

/-- **A Tribonacci representation of nine.** The digit list $(0, 1, 0, 1)$, read least
significant digit first (the word $1010$ written most significant digit first), is a
Tribonacci representation of $9$.

With $T_n$ the Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$), this is
$9 = T_6 + T_4 = 7 + 2$, the paper's example $(9)_T = 1010$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem isTribonacciRepr_nine : IsTribonacciRepr [0, 1, 0, 1] 9 := by
  unfold IsTribonacciRepr
  decide

/-- **Duchêne–Rigo: letters of the Tribonacci word from Tribonacci representations.** Let $w$
be a Tribonacci representation of a natural number $m$, written most significant digit first,
with missing digits read as $0$. The letter of the infinite Tribonacci word at position $m$
(positions counted from $0$) is $a$ if $w$ ends in $0$, $b$ if $w$ ends in $01$, and $c$ if $w$
ends in $11$. In particular the empty representation of $0$ ends in $0$, and the
representation $1$ of $1$ ends in $01$.

This is the paper's statement about the $n$-th letter, with $m = n - 1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Theorem 1
(quoting Duchêne and Rigo 2008) (`jis-2025-25.5.4-thm-1`). -/
public theorem_wanted tribonacciWord_eq_of_isTribonacciRepr (m : ℕ) (w : List ℕ)
    (hw : IsTribonacciRepr w m) :
    InfiniteWord.tribonacciWord m =
      if w.getD 0 0 = 0 then .a else if w.getD 1 0 = 0 then .b else .c

/-- **Tribonacci approximation error bound.** Let $T_0 = T_1 = 0$, $T_2 = 1$,
$T_{m+3} = T_{m+2} + T_{m+1} + T_m$ be the Tribonacci numbers, let $\alpha$ be the real root of
$x^3 = x^2 + x + 1$, and let $\beta$ be a non-real complex root of the same equation, with
$\gamma = \overline{\beta}$ the other non-real root. Then for every natural number $n$,

$$|T_{n+1} - \alpha T_n| < \frac{2 \alpha^{-n/2}}{|\beta - \gamma|}.$$

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Lemma 2
(`jis-2025-25.5.4-lem-2`). -/
public theorem_wanted abs_tribonacci_succ_sub_mul_lt (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1)
    (β : ℂ) (hβ : β ^ 3 = β ^ 2 + β + 1) (hβim : β.im ≠ 0) (n : ℕ) :
    |(tribonacci (n + 1) : ℝ) - α * tribonacci n|
      < 2 * α ^ (-(n : ℝ) / 2) / ‖β - (starRingEnd ℂ) β‖

/-- **Tribonacci differences do not keep one strict sign for three steps.** Let $T_n$ be the
Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let
$\alpha$ be a real number with $\alpha^3 = \alpha^2 + \alpha + 1$. Then for every $n \ge 0$ the
three numbers $T_{k+1} - \alpha T_k$ for $k = n, n + 1, n + 2$ are neither all positive nor all
negative.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 3 (`jis-2025-25.5.4-prop-3`). -/
public theorem_wanted tribonacci_succ_sub_mul_sign_changes (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (n : ℕ) :
    ¬ (∀ i < 3, 0 < (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i)) ∧
      ¬ (∀ i < 3, (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i) < 0)

/-- **Growth of the first column of the Trithoff array.** Let $\alpha$ be a real number with
$\alpha^3 = \alpha^2 + \alpha + 1$, and let $a_0 < a_1 < a_2 < \cdots$ be the positive integers
that have a Tribonacci representation with least significant digit $1$, in increasing order
(the first column of the Trithoff array, OEIS A003265). Then $a_r / (r + 1)$ tends to
$\alpha / (\alpha - 1)$ as $r \to \infty$.

The limit equals $(\alpha^2 + 1) / 2$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 6 (`jis-2025-25.5.4-prop-6`). -/
public theorem_wanted tendsto_trithoff_first_column_div (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) :
    Filter.Tendsto
      (fun r : ℕ => (Nat.nth (fun n => 0 < n ∧ ∃ w, IsTribonacciRepr w n ∧ w.getD 0 0 = 1) r
        : ℝ) / (r + 1))
      Filter.atTop (nhds (α / (α - 1)))

/-- **Sums of Fibternary and Tribternary numbers.** Call a natural number Fibternary if its
base-$3$ digits are all $0$ or $1$ with no two consecutive $1$s, and Tribternary if its
base-$3$ digits are all $0$ or $1$ with no three consecutive $1$s. Every natural number is a
sum of four Fibternary numbers and also a sum of three Tribternary numbers (the summands
may be $0$ and need not be distinct).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 21 (`jis-2025-25.5.4-prop-21`). -/
public theorem_wanted exists_fibternary_sum_four_and_tribternary_sum_three (n : ℕ) :
    (∃ a b c d : ℕ, (∀ x ∈ [a, b, c, d],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c + d) ∧
      ∃ a b c : ℕ, (∀ x ∈ [a, b, c],
        (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 x) ∧ n = a + b + c

/-- **Fibternary multiples.** Every positive integer $n$ has a positive multiple $m$ that is
Fibternary: the base-$3$ digits of $m$ are all $0$ or $1$, and no two consecutive digits
of $m$ are both $1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 22 (`jis-2025-25.5.4-prop-22`). -/
public theorem_wanted exists_fibternary_multiple (n : ℕ) (hn : 0 < n) :
    ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 m

/-- **Tribbinary and Tribternary multiples.** Every positive integer $n$ has a positive
multiple whose binary digits contain no three consecutive $1$s (a Tribbinary number), and a
positive multiple whose base-$3$ digits are all $0$ or $1$ with no three consecutive $1$s (a
Tribternary number).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Corollary 23 (`jis-2025-25.5.4-cor-23`). -/
public theorem_wanted exists_tribbinary_and_tribternary_multiple (n : ℕ) (hn : 0 < n) :
    (∃ m, 0 < m ∧ n ∣ m ∧ ¬ [1, 1, 1] <:+: Nat.digits 2 m) ∧
      ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1, 1] <:+: Nat.digits 3 m

/-! ## Tribonacci successor, Trithoff rows and precolumns -/

/-- **Tribonacci value of a digit word.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers. The Tribonacci value of a finite
word $w$ of natural-number digits $w_0, w_1, \dots, w_{\ell-1}$, listed from the least
significant digit, is $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$, so the digits weigh
$1, 2, 4, 7, 13, \dots$. Digits may exceed $1$ and three consecutive ones are allowed, so this
also evaluates the paper's non-canonical and improper representations.

For a Tribonacci representation $w$ of $n$, the value of $w$ followed by a new least
significant digit $0$ is the Tribonacci successor $\mathrm{out}(n)$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Sections 2.3, 5 and 6.1. -/
public def tribonacciValue (w : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3)

/-- **The empty digit word has Tribonacci value zero.** The Tribonacci value of the empty
digit word is $0$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3. -/
public theorem tribonacciValue_nil : tribonacciValue [] = 0 := by
  simp [tribonacciValue]

/-- **The non-canonical Tribonacci word $1110$ has value $13$.** The digit word $1110$, written
most significant digit first, whose digits weigh the Tribonacci numbers $T_6 = 7$, $T_5 = 4$,
$T_4 = 2$ and $T_3 = 1$, has Tribonacci value $7 + 4 + 2 = 13$. It is the paper's example of a
non-canonical representation: its digits are $0$ and $1$ but it has three consecutive ones.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 5. -/
public theorem tribonacciValue_one_one_one_zero : tribonacciValue [0, 1, 1, 1] = 13 := by
  decide

/-- **The improper Tribonacci word $1030$ has value $13$.** The digit word $1030$, written most
significant digit first, whose digits weigh the Tribonacci numbers $T_6 = 7$, $T_5 = 4$,
$T_4 = 2$ and $T_3 = 1$, has Tribonacci value $1 \cdot 7 + 3 \cdot 2 = 13$. It is the paper's
example of an improper representation, with a digit larger than $1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciValue_one_zero_three_zero : tribonacciValue [0, 3, 0, 1] = 13 := by
  decide

/-- **Indices used by records of the Tribonacci successor.** Let $T_n$ be the Tribonacci numbers
($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let $\alpha$ be a real
number with $\alpha^3 = \alpha^2 + \alpha + 1$. For each $n$ fix a Tribonacci representation
$R(n) = (r_0, r_1, \dots, r_{\ell-1})$ of $n$: digits in $\{0, 1\}$ with no three consecutive
ones and $n = \sum_i r_i T_{i+3}$. Let $\mathrm{out}(n) = \sum_i r_i T_{i+4}$ be the Tribonacci
successor of $n$. Call $n$ a positive record if $n > 0$ and
$\mathrm{out}(m) - \alpha m < \mathrm{out}(n) - \alpha n$ for every $m < n$, and a negative
record if $n > 0$ and $\mathrm{out}(n) - \alpha n < \mathrm{out}(m) - \alpha m$ for every
$m < n$. If the digit $r_i$ of $R(n)$ equals $1$, then $T_{i+4} - \alpha T_{i+3} > 0$ when $n$
is a positive record, and $T_{i+4} - \alpha T_{i+3} < 0$ when $n$ is a negative record.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 1 and its negative analogue (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_indices (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1)
    (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n) (n : ℕ) (i : ℕ)
    (hi : (R n).getD i 0 = 1) :
    ((0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R m) : ℝ) - α * m <
        tribonacciValue (0 :: R n) - α * n) →
      0 < (tribonacci (i + 4) : ℝ) - α * tribonacci (i + 3)) ∧
    ((0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R n) : ℝ) - α * n <
        tribonacciValue (0 :: R m) - α * m) →
      (tribonacci (i + 4) : ℝ) - α * tribonacci (i + 3) < 0)

/-- **Partial sums along the positive and negative indices are records.** Let $T_n$ be the
Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let
$\alpha$ be a real number with $\alpha^3 = \alpha^2 + \alpha + 1$. For each $n$ fix a Tribonacci
representation $R(n) = (r_0, r_1, \dots, r_{\ell-1})$ of $n$: digits in $\{0, 1\}$ with no three
consecutive ones and $n = \sum_i r_i T_{i+3}$. Let $\mathrm{out}(n) = \sum_i r_i T_{i+4}$ be the
Tribonacci successor of $n$. Call $n$ a positive record if $n > 0$ and
$\mathrm{out}(m) - \alpha m < \mathrm{out}(n) - \alpha n$ for every $m < n$, and a negative
record if $n > 0$ and $\mathrm{out}(n) - \alpha n < \mathrm{out}(m) - \alpha m$ for every
$m < n$. Let $P(1) < P(2) < \cdots$ list the indices $i$ with $T_{i+1} - \alpha T_i > 0$, and
$Q(1) < Q(2) < \cdots$ those with $T_{i+1} - \alpha T_i < 0$. Then for every $k \ge 2$ the
number $T_{P(2)} + \cdots + T_{P(k)}$ is a positive record and $T_{Q(2)} + \cdots + T_{Q(k)}$ is
a negative record.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 2 and its negative analogue (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_of_partial_sum (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n)
    (j : ℕ) (hj : 1 ≤ j) :
    (let n := (∑ s ∈ Finset.range j,
        tribonacci (Nat.nth (fun i => 0 < (tribonacci (i + 1) : ℝ) - α * tribonacci i) (s + 1)));
      0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R m) : ℝ) - α * m <
        tribonacciValue (0 :: R n) - α * n) ∧
    (let n := (∑ s ∈ Finset.range j,
        tribonacci (Nat.nth (fun i => (tribonacci (i + 1) : ℝ) - α * tribonacci i < 0) (s + 1)));
      0 < n ∧ ∀ m < n, (tribonacciValue (0 :: R n) : ℝ) - α * n <
        tribonacciValue (0 :: R m) - α * m)

/-- **Late records use $T_{P(t)}$ and $T_{Q(t)}$.** Let $T_n$ be the Tribonacci numbers
($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let $\alpha$ be a real
number with $\alpha^3 = \alpha^2 + \alpha + 1$. For each $n$ fix a Tribonacci representation
$R(n) = (r_0, r_1, \dots, r_{\ell-1})$ of $n$: digits in $\{0, 1\}$ with no three consecutive
ones and $n = \sum_i r_i T_{i+3}$. Let $\mathrm{out}(n) = \sum_i r_i T_{i+4}$ be the Tribonacci
successor of $n$. Call $n$ a positive record if $n > 0$ and
$\mathrm{out}(m) - \alpha m < \mathrm{out}(n) - \alpha n$ for every $m < n$, and a negative
record if $n > 0$ and $\mathrm{out}(n) - \alpha n < \mathrm{out}(m) - \alpha m$ for every
$m < n$. Let $P(1) < P(2) < \cdots$ list the indices $i$ with $T_{i+1} - \alpha T_i > 0$, and
$Q(1) < Q(2) < \cdots$ those with $T_{i+1} - \alpha T_i < 0$. Let $t > 1$. If
$n_0 < n_1 < \cdots$ are the positive records, there is $N_0$ such that for every $N > N_0$ the
representation $R(n_N)$ has digit $1$ at index $P(t) - 3$, that is, it uses $T_{P(t)}$. If
$n'_0 < n'_1 < \cdots$ are the negative records, there is $N_0$ such that for every $N > N_0$
the representation $R(n'_N)$ has digit $1$ at index $Q(t) - 3$, that is, it uses $T_{Q(t)}$.

The paper states part 3 for negative records with $P(t)$; following its remark that similar
statements hold for negative differences, it is read with $Q(t)$, since a negative record uses
only indices $i$ with $T_{i+1} - \alpha T_i < 0$ (Proposition 4, part 1).

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 4, part 3 (`jis-2025-25.5.4-prop-4`). -/
public theorem_wanted tribonacciSucc_record_eventually_contains (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (R : ℕ → List ℕ) (hR : ∀ n, IsTribonacciRepr (R n) n)
    (t : ℕ) (ht : 1 < t) :
    (∃ N₀, ∀ N > N₀, (R (Nat.nth (fun n => 0 < n ∧ ∀ m < n,
        (tribonacciValue (0 :: R m) : ℝ) - α * m < tribonacciValue (0 :: R n) - α * n) N)).getD
      (Nat.nth (fun i => 0 < (tribonacci (i + 1) : ℝ) - α * tribonacci i) (t - 1) - 3) 0 = 1) ∧
    ∃ N₀, ∀ N > N₀, (R (Nat.nth (fun n => 0 < n ∧ ∀ m < n,
        (tribonacciValue (0 :: R n) : ℝ) - α * n < tribonacciValue (0 :: R m) - α * m) N)).getD
      (Nat.nth (fun i => (tribonacci (i + 1) : ℝ) - α * tribonacci i < 0) (t - 1) - 3) 0 = 1

/-- **Row numbers of the Trithoff array.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers, and let $U_i = T_i + T_{i+1}$,
so that $U_0, U_1, U_2, \dots = 0, 1, 2, 3, 6, 11, \dots$. Let $n$ have Tribonacci
representation $a1$, where $a$ is a digit word written most significant digit first, and let
$[a]_T$ be the Tribonacci value of $a$. Then $n$ is the $(n - [a]_T)$-th smallest positive
integer whose Tribonacci representation ends in $1$ (OEIS A003265, the first column of the
Trithoff array), and $n - [a]_T = 1 + [a1]_U$, where $[a1]_U$ is the sum of the digits of $a1$
weighted by $U_0, U_1, U_2, \dots$ starting from the least significant digit.

The paper writes $U_i = T_{2,i-2}$; its alternative formula $T_{i+1} - T_i$ is shifted, and the
displayed values $0, 1, 2, 3, 6, 11, \dots$ are used.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 7 (`jis-2025-25.5.4-lem-7`). -/
public theorem_wanted trithoff_row_number_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr (1 :: a) n) :
    Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (n - tribonacciValue a - 1) = n ∧
      n - tribonacciValue a = 1 + ∑ i ∈ Finset.range (a.length + 1),
        (1 :: a).getD i 0 * (tribonacci i + tribonacci (i + 1))

/-- **Differences along a Trithoff row.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{m+3} = T_{m+2} + T_{m+1} + T_m$ be the Tribonacci numbers, and for a finite word
$w = (w_0, \dots, w_{\ell-1})$ of natural-number digits, listed from the least significant
digit, let $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$ be its Tribonacci value. Let
$a = (a_0, \dots, a_{\ell-1})$ be a Tribonacci representation of a natural number $n$ (all
digits $0$ or $1$, no three consecutive ones, and $[a]_T = n$), and let
$b = (b_0, \dots, b_\ell)$ be the word with $b_i = a_i + a_{i-1}$, where $a_{-1} = a_\ell = 0$
(the product $11 \cdot a$ computed digit-wise without carries). For $k \ge 0$ write $0^k a$ for
the word $(0, \dots, 0, a_0, \dots, a_{\ell-1})$ with $k$ zeros placed before $a_0$, that is, at
the least significant end. Then there is a natural number $k$ with
$[0^{k+1} a]_T - [0^k a]_T = [b]_T$.

The entries of the Trithoff row of $n$ from $n$ onwards are $[0^k a]_T$ for $k \ge 0$, so
$[b]_T$ is the difference of two consecutive entries of that row.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 8 (`jis-2025-25.5.4-prop-8`). -/
public theorem_wanted exists_trithoff_row_difference_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr a n) :
    ∃ k : ℕ, (tribonacciValue (List.replicate (k + 1) 0 ++ a) : ℤ) -
        tribonacciValue (List.replicate k 0 ++ a) =
      tribonacciValue ((List.range (a.length + 1)).map fun i => a.getD i 0 + (0 :: a).getD i 0)

/-- **Appending a zero to a non-canonical Tribonacci representation.** Let $T_0 = T_1 = 0$,
$T_2 = 1$ and $T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers, and for a digit
word $u$, written most significant digit first, let $[u]_T$ be its Tribonacci value, in which
the $i$-th digit from the right (counting from $0$) weighs $T_{i+3}$. Let $w$ be a digit word
with all digits in $\{0, 1\}$ (three consecutive ones are allowed) and $[w]_T = n$, and let $v$
be a Tribonacci representation of $n$. Then $[w0]_T = [v0]_T$, where $w0$ and $v0$ are $w$ and
$v$ followed by the digit $0$; that is, $w0$ evaluates to the Tribonacci successor
$\mathrm{out}(n) = [v0]_T$ of $n$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 12 (`jis-2025-25.5.4-lem-12`). -/
public theorem_wanted tribonacciValue_cons_zero_of_noncanonical (w v : List ℕ) (n : ℕ)
    (hw : ∀ d ∈ w, d ≤ 1) (hwn : tribonacciValue w = n) (hv : IsTribonacciRepr v n) :
    tribonacciValue (0 :: w) = tribonacciValue (0 :: v)

/-- **Precolumns of the Trithoff array.** Write $[u]_T$ for the Tribonacci value of a digit
word $u$, written most significant digit first. Let $n$ have Tribonacci representation $abc1$,
where $a$ is a digit word and $b$, $c$ are digits. Let $\mathrm{out}(n) = [abc10]_T$ and
$\mathrm{out}^2(n) = [abc100]_T$ be the next two entries of the Trithoff row of $n$, and extend
the row to the left by the Tribonacci rule: in the integers, the wall is
$W = \mathrm{out}^2(n) - \mathrm{out}(n) - n$ and the seed is $S = \mathrm{out}(n) - n - W$.
Then $W = [abc]_T + 1$, $S = [ab]_T + c$, and the pre-seed $n - W - S$ equals $[a]_T + b$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 13 (`jis-2025-25.5.4-lem-13`). -/
public theorem_wanted trithoff_precolumns (a : List ℕ) (b c n : ℕ)
    (h : IsTribonacciRepr (1 :: c :: b :: a) n) :
    let g₂ : ℤ := tribonacciValue (0 :: 1 :: c :: b :: a)
    let g₃ : ℤ := tribonacciValue (0 :: 0 :: 1 :: c :: b :: a)
    let wall := g₃ - g₂ - n
    let seed := g₂ - n - wall
    wall = tribonacciValue (c :: b :: a) + 1 ∧ seed = tribonacciValue (b :: a) + c ∧
      (n : ℤ) - wall - seed = tribonacciValue a + b

/-- **Wall, seed and pre-seed of the Trithoff array via the Tribonacci word.** Let
$f_1 < f_2 < \cdots$ be the positive integers whose Tribonacci representation ends in $1$ (the
first column of the Trithoff array). For each row $r \ge 1$ let $\mathrm{out}(f_r)$ and
$\mathrm{out}^2(f_r)$ be the Tribonacci values of the Tribonacci representation of $f_r$,
written most significant digit first, followed by one and by two zeros, that is, with one and
with two new least significant digits $0$. Define, in the integers, the wall
$W_r = \mathrm{out}^2(f_r) - \mathrm{out}(f_r) - f_r$, the seed
$S_r = \mathrm{out}(f_r) - f_r - W_r$ and the pre-seed $P_r = f_r - W_r - S_r$. Count positions
in the infinite Tribonacci word from $1$. Then (i) for every $r \ge 1$, $W_r$ is the $r$-th
position holding $a$ or $b$; (ii) $S_1 = 0$, the seed is non-decreasing in $r$, it takes the
value $0$ exactly once, and it takes each value $m \ge 1$ exactly twice if position $m$ holds
$a$ and exactly once otherwise; and (iii) $P_1 = 0$, the pre-seed is non-decreasing in $r$, it
takes the value $0$ exactly twice, and it takes each value $m \ge 1$ exactly three times if
position $m$ holds $a$ or $b$ and exactly twice if it holds $c$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 14 (`jis-2025-25.5.4-thm-14`). -/
public theorem_wanted trithoff_wall_seed_preseed (R : ℕ → List ℕ)
    (hR : ∀ r, IsTribonacciRepr (R r) (Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r)) :
    let g₁ : ℕ → ℤ := fun r => Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r
    let g₂ : ℕ → ℤ := fun r => tribonacciValue (0 :: R r)
    let g₃ : ℕ → ℤ := fun r => tribonacciValue (0 :: 0 :: R r)
    let wall := fun r => g₃ r - g₂ r - g₁ r
    let seed := fun r => g₂ r - g₁ r - wall r
    let preseed := fun r => g₁ r - wall r - seed r
    (∀ r, wall r = 1 + Nat.nth (fun m => InfiniteWord.tribonacciWord m ≠ .c) r) ∧
    (seed 0 = 0 ∧ Monotone seed ∧ ∀ m : ℕ, {r | seed r = m}.ncard =
      if m ≠ 0 ∧ InfiniteWord.tribonacciWord (m - 1) = .a then 2 else 1) ∧
    (preseed 0 = 0 ∧ Monotone preseed ∧ ∀ m : ℕ, {r | preseed r = m}.ncard =
      if m ≠ 0 ∧ InfiniteWord.tribonacciWord (m - 1) ≠ .c then 3 else 2)

/-- **Gaps in the first column of the Trithoff array.** Let $f_1 < f_2 < \cdots$ be the positive
integers whose Tribonacci representation ends in the digit $1$ (OEIS A003265, the first column
of the Trithoff array). For every $j \ge 1$ the difference $f_{j+1} - f_j$ is $2$ or $3$, and
$f_{j+1} - f_j = 3$ exactly when $j = p_a(k) + p_b(k)$ for some $k \ge 1$, where $p_a(k)$ and
$p_b(k)$ are the positions, counted from $1$, of the $k$-th occurrences of the letters $a$ and
$b$ in the infinite Tribonacci word.

The paper identifies these sums $p_a(k) + p_b(k)$, that is A003144 + A003145, with A305373.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 11 (`jis-2025-25.5.4-prop-11`). -/
public theorem_wanted trithoff_first_column_sub (i : ℕ) :
    (Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
        Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 2 ∨
      Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
          Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 3) ∧
    (Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (i + 1) =
        Nat.nth (fun m => 0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) i + 3 ↔
      ∃ k, i + 1 = (Nat.nth (fun m => InfiniteWord.tribonacciWord m = .a) k + 1) +
        (Nat.nth (fun m => InfiniteWord.tribonacciWord m = .b) k + 1))

/-! ## ExtraTribs -/

/-- **ExtraTribs.** An extraTrib is a two-sided integer sequence
$S \colon \mathbb{Z} \to \mathbb{Z}$ that follows the Tribonacci rule
$S(n+3) = S(n+2) + S(n+1) + S(n)$ for every $n \in \mathbb{Z}$ and whose terms are eventually
positive: there is an integer $N$ with $S(n) > 0$ for all $n \ge N$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 4. -/
public def IsExtraTrib (S : ℤ → ℤ) : Prop :=
  (∀ n, S (n + 3) = S (n + 2) + S (n + 1) + S n) ∧ ∃ N, ∀ n ≥ N, 0 < S n

/-- **The zero sequence is not an extraTrib.** The constant sequence $n \mapsto 0$ on
$\mathbb{Z}$ is not an extraTrib.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 4. -/
public theorem not_isExtraTrib_zero : ¬ IsExtraTrib (fun _ => 0) := by
  rintro ⟨-, N, hN⟩
  exact lt_irrefl 0 (hN N le_rfl)

/-- **Difference-inverses of extraTribs.** Let $S$ be an extraTrib. There is exactly one
sequence $Q \colon \mathbb{Z} \to \mathbb{Q}$ that follows the Tribonacci rule
$Q(n+3) = Q(n+2) + Q(n+1) + Q(n)$ for all $n \in \mathbb{Z}$ and satisfies
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$. Moreover, there is an extraTrib $Q$ with
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$ if and only if $S$ is not of Type EEOO
(parities repeating even, even, odd, odd), that is, there is no integer $k$ such that for
every $n \in \mathbb{Z}$, $S(n)$ is even exactly when $(n - k) \bmod 4$ is $0$ or $1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 9 (`jis-2025-25.5.4-thm-9`). -/
public theorem_wanted extraTrib_difference_inverse (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃! Q : ℤ → ℚ, (∀ n, Q (n + 3) = Q (n + 2) + Q (n + 1) + Q n) ∧
      ∀ n, Q (n + 1) - Q n = S n) ∧
    ((∃ Q : ℤ → ℤ, IsExtraTrib Q ∧ ∀ n, Q (n + 1) - Q n = S n) ↔
      ¬ ∃ k : ℤ, ∀ n, (Even (S n) ↔ (n - k) % 4 < 2))

/-- **ExtraTribs cannot be inverted forever.** Let $S$ be an extraTrib. There is no sequence
$S_0, S_1, S_2, \dots$ of functions $\mathbb{Z} \to \mathbb{Z}$ with $S_0 = S$ such that for
every $k \ge 0$ the function $S_{k+1}$ is an extraTrib and a difference-inverse of $S_k$, that
is, $S_{k+1}(n+1) - S_{k+1}(n) = S_k(n)$ for all $n \in \mathbb{Z}$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 10 (`jis-2025-25.5.4-thm-10`). -/
public theorem_wanted extraTrib_not_infinitely_invertible (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    ¬ ∃ f : ℕ → ℤ → ℤ, f 0 = S ∧
      ∀ k, IsExtraTrib (f (k + 1)) ∧ ∀ n, f (k + 1) (n + 1) - f (k + 1) n = f k n

/-- **Row numbers of divisible extraTribs.** Let $S$ be an extraTrib and let $n$ be a natural
number dividing every term $S(k)$, $k \in \mathbb{Z}$. Let $f_0 < f_1 < f_2 < \dots$ be the
positive integers whose Tribonacci representation has least significant digit $1$ (the first
column of the Trithoff array), let $r$ be a natural number, and let $w$ be a Tribonacci
representation of $f_r$. For a digit list $v$ written least significant digit first, let
$[v]_T$ be its value in the Tribonacci base and $0^j v$ be $v$ preceded by $j$ zeros in the
least significant positions. If there is an integer $k_0$ with $S(k_0 + j) = [0^j w]_T$ for
every natural number $j$, that is, the tail $S(k_0), S(k_0 + 1), \dots$ is row $r + 1$ of the
Trithoff array, then $r + 1 \equiv 1 \pmod{n}$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 18 (`jis-2025-25.5.4-thm-18`). -/
public theorem_wanted extraTrib_row_number_modEq_one (S : ℤ → ℤ) (hS : IsExtraTrib S) (n : ℕ)
    (hn : ∀ k, (n : ℤ) ∣ S k) (r : ℕ) (w : List ℕ) (hw : IsTribonacciRepr w (Nat.nth (fun m => 0 < m
        ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1) r))
    (k₀ : ℤ) (hrow : ∀ j : ℕ, S (k₀ + j) = tribonacciValue (List.replicate j 0 ++ w)) :
    r + 1 ≡ 1 [MOD n]

/-- **Signs of an extraTrib to the left.** Let $S$ be an extraTrib. Then $S(k) < 0$ for some
integer $k$, and whenever $S(k) < 0$, for every integer $n$ with $n + 2 < k$ the three terms
$S(n)$, $S(n+1)$, $S(n+2)$ are neither all positive nor all negative.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 19 (`jis-2025-25.5.4-lem-19`). -/
public theorem_wanted extraTrib_left_extension (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃ k, S k < 0) ∧ ∀ k, S k < 0 → ∀ n, n + 2 < k →
      ¬ (0 < S n ∧ 0 < S (n + 1) ∧ 0 < S (n + 2)) ∧ ¬ (S n < 0 ∧ S (n + 1) < 0 ∧ S (n + 2) < 0)

/-- **The reversal of an extraTrib is not an extraTrib.** If $S : \mathbb{Z} \to \mathbb{Z}$
is an extraTrib, then the sequence $n \mapsto |S(-n)|$ is not an extraTrib.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 20 (`jis-2025-25.5.4-thm-20`). -/
public theorem_wanted not_isExtraTrib_reversal (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    ¬ IsExtraTrib (fun n => |S (-n)|)

/-! ## Canonization of improper representations

Words in this section are written most significant digit first, as in the paper; the
procedure pads a word with a `0` on the left before each step. -/

/-- **Leftmost carrying.** Let $w = w_0 w_1 \cdots w_{\ell-1}$ be a word of natural-number digits,
written most significant digit first with positions numbered from $0$, and let $k$ be the least
index with $k + 3 < \ell$ and $w_{k+1}, w_{k+2}, w_{k+3} > 0$. Leftmost carrying replaces the
block $w_k w_{k+1} w_{k+2} w_{k+3}$ by $(w_k + 1)(w_{k+1} - 1)(w_{k+2} - 1)(w_{k+3} - 1)$ and
leaves the other digits unchanged; it is undefined when there is no such $k$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciLeftmostCarry : List ℕ → Option (List ℕ)
  | [] => none
  | d :: tl =>
    match tl with
    | a :: b :: c :: rest =>
      if 0 < a ∧ 0 < b ∧ 0 < c then some ((d + 1) :: (a - 1) :: (b - 1) :: (c - 1) :: rest)
      else (tribonacciLeftmostCarry tl).map (d :: ·)
    | _ => none

/-- **Leftmost carrying of $0111$.** Leftmost carrying takes the word $0111$, written most
significant digit first, to $1000$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 5. -/
public theorem tribonacciLeftmostCarry_zero_one_one_one :
    tribonacciLeftmostCarry [0, 1, 1, 1] = some [1, 0, 0, 0] := by
  decide

/-- **Weight of an improper word.** Let $w$ be a word of natural-number digits, written most
significant digit first, and let $v = 0w$ be $w$ padded with a $0$ on the left, with positions
numbered from $0$. Let $p$ be the position of the leftmost digit $\ge 2$ of $v$ (the improper
boundary), or the length of $v$ if there is no such digit. The weight of $w$ is the sum of the
digits of $v$ that come after the last $0$ of $v$ before position $p$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciImproperWeight (w : List ℕ) : ℕ :=
  let v := 0 :: w
  let p := v.findIdx (fun d => 2 ≤ d)
  ((v.take p).reverse.takeWhile (fun d => d ≠ 0)).sum + (v.drop p).sum

/-- **Weight of the improper word $010113$.** The word $010113$, written most significant digit
first, has weight $1 + 1 + 3 = 5$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciImproperWeight_example : tribonacciImproperWeight [0, 1, 0, 1, 1,
    3] = 5 := by
  decide

/-- **One step of Tribonacci canonization.** Let $w$ be a word of natural-number digits, written
most significant digit first, and let $v = 0w$ be $w$ padded with a $0$ on the left, with
positions numbered from $0$. If leftmost carrying applies to $v$, the step returns its result
(Step 1). Otherwise let $p$ be the position of the leftmost digit $\ge 2$ of $v$ (the improper
boundary), or the length of $v$ if there is no such digit. If $v$ has no position $p + 3$, the
step is undefined. Otherwise, if $v_{p-1} = 0$, the step (Step 2a) sets $v_{p-1}$ to $1$,
decreases $v_p$ by $2$ and increases $v_{p+3}$ by $1$, as in $0abcd \mapsto 1(a-2)bc(d+1)$; if
$v_{p-1} \ne 0$, the step (Step 2b) sets $v_{p-2}$ to $1$ and $v_{p-1}$ to $0$, decreases $v_p$
by $2$ and increases $v_{p+2}$ and $v_{p+3}$ by $1$, as in
$01a0cd \mapsto 10(a-2)0(c+1)(d+1)$. All other digits of $v$ are unchanged.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciCanonizationStep (w : List ℕ) : Option (List ℕ) :=
  let v := 0 :: w
  match tribonacciLeftmostCarry v with
  | some u => some u
  | none =>
    let p := v.findIdx (fun d => 2 ≤ d)
    if p + 3 < v.length then
      if v.getD (p - 1) 0 = 0 then
        some (((v.set (p - 1) 1).set p (v.getD p 0 - 2)).set (p + 3) (v.getD (p + 3) 0 + 1))
      else
        some (((((v.set (p - 2) 1).set (p - 1) 0).set p (v.getD p 0 - 2)).set (p + 2)
          (v.getD (p + 2) 0 + 1)).set (p + 3) (v.getD (p + 3) 0 + 1))
    else none

/-- **Canonization run.** Words are written most significant digit first. The run of at most
$n$ canonization steps on a word $w$ of natural numbers is defined by recursion on $n$: it
returns $w$ if $n = 0$ or if $w$ is canonical (every digit is $0$ or $1$ and there are no
three consecutive $1$s); otherwise it applies one canonization step to $w$ and returns the
run of at most $n - 1$ steps on the result, and it is undefined when that step is undefined.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public def tribonacciCanonizationRun : ℕ → List ℕ → Option (List ℕ)
  | 0, w => some w
  | n + 1, w =>
    if (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w then some w
    else (tribonacciCanonizationStep w).bind (tribonacciCanonizationRun n)

/-- **Canonizing $2000000$.** Words are written most significant digit first. Running at most
two steps of the canonization procedure on the word $2000000$ yields $10001000$.

Both words have value $88$: with $T_n$ the Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$)
and the digit in position $i$ from the right (starting at $0$) weighted by $T_{i+3}$, they
are $2 T_9 = 2 \cdot 44$ and $T_{10} + T_6 = 81 + 7$. A single Step 2a of the procedure
produces the result.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 6.1. -/
public theorem tribonacciCanonizationRun_example :
    tribonacciCanonizationRun 2 [2, 0, 0, 0, 0, 0, 0] = some [1, 0, 0, 0, 1, 0, 0, 0] := by
  decide

/-- **Leftmost carrying does not move the improper boundary left or raise the weight.** Let $w$ be
a word of natural-number digits, written most significant digit first, with some digit $\ge 2$.
Suppose leftmost carrying applied to the padded word $0w$ gives a word $u$ (of the same length as
$0w$) that still has a digit $\ge 2$. Then the position of the leftmost digit $\ge 2$ in $u$ is at
least its position in $0w$, and the weight of $u$ is at most the weight of $w$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 15 (`jis-2025-25.5.4-lem-15`). -/
public theorem_wanted tribonacciLeftmostCarry_boundary_weight (w u : List ℕ)
    (hw : ∃ d ∈ w, 2 ≤ d) (hu : tribonacciLeftmostCarry (0 :: w) = some u)
    (hu' : ∃ d ∈ u, 2 ≤ d) :
    (0 :: w).findIdx (fun d => 2 ≤ d) ≤ u.findIdx (fun d => 2 ≤ d) ∧
      tribonacciImproperWeight u ≤ tribonacciImproperWeight w

/-- **Termination of the canonization procedure.** Words are written most significant digit
first. Let $w$ be a word of natural numbers with some digit at least $2$, let $m$ be its
improper weight, and let $k \ge 3m$. Then there is an $n$ such that running at most $n$ steps
of the canonization procedure on $w 0^k$ ($w$ followed by $k$ zeros) yields a word whose
digits are all $0$ or $1$ and which has no three consecutive $1$s.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 16 (`jis-2025-25.5.4-thm-16`). -/
public theorem_wanted tribonacciCanonizationRun_terminates (w : List ℕ) (hw : ∃ d ∈ w, 2 ≤ d)
    (k : ℕ) (hk : 3 * tribonacciImproperWeight w ≤ k) :
    ∃ n v, tribonacciCanonizationRun n (w ++ List.replicate k 0) = some v ∧
      (∀ d ∈ v, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: v

/-- **Canonizing a word followed by zeros.** Words are written most significant digit first.
Let $w$ be a word of natural numbers with some digit at least $2$, and suppose that running at
most $n$ steps of the canonization procedure on $w$ yields a word $v$ whose digits are all $0$
or $1$ and which has no three consecutive $1$s. Then for every $k$, running at most $n$ steps
of the canonization procedure on $w 0^k$ ($w$ followed by $k$ zeros) yields $v 0^k$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Corollary 17 (`jis-2025-25.5.4-cor-17`). -/
public theorem_wanted tribonacciCanonizationRun_append_zeros (w v : List ℕ) (n k : ℕ)
    (hw : ∃ d ∈ w, 2 ≤ d) (hv : tribonacciCanonizationRun n w = some v)
    (hcan : (∀ d ∈ v, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: v) :
    tribonacciCanonizationRun n (w ++ List.replicate k 0) = some (v ++ List.replicate k 0)

end

end MetaMathlibExt
