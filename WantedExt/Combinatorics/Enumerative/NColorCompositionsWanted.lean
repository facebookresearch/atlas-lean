/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Allowing or prohibiting two consecutive colors in `n`-color
compositions

Statements from Brian Hopkins and Hua Wang, "Allowing or
Prohibiting Two Consecutive Colors in `n`-Color Compositions",
*Journal of Integer Sequences* 27 (2024), Article 24.7.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Hopkins/hopkins8.tex>).

An `n`-color composition (Agarwal) is a list of parts `k_c`
with `1 ≤ c ≤ k`; below a colored part is a pair `(k, c)`, the
paper's sets `CCo_{b,b+1}(n)` (only colors `b, b+1`),
`CCo_{\widehat{b,b+1}}(n)` (colors `b, b+1` prohibited), and
`CCo_{\hat 2}(n)` (color `2` prohibited) are the subtypes
`ColorCompAllowed`, `ColorCompProhibited`, and
`ColorCompProhibit2`, and their counts `cco` are `Nat.card`s,
extended to `ℤ` by `0` at negative arguments (with the empty
composition giving count `1` at `n = 0`). Ordinary
compositions are Mathlib's `Composition`. The tribonacci
numbers `t(n)` (`t(0) = 1`, `t(1) = 0`, `t(2) = 1`) are `trib`,
extended by `0` to negative integers as in the paper, and
`f` is `Nat.fib`.

Two printed statements need range qualifications that brute
force exposes: the recurrence of Proposition 1 fails at
`n = 1` (it is stated for `2 ≤ n`), and the recurrence of
Proposition 11 fails at `n ≤ 2` (stated for `3 ≤ n`).
Theorem 2's ternary-string conditions are given in the
equivalent zero-split segment form forced by its proof (each
maximal zero-free segment, including end segments, is all-`1`
of length `≥ b-1` or all-`2` of length `≥ b`); with the
conditions read literally without end segments, the string
`0` would be a counterexample at `n = 2`, `b = 3`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- **n-color compositions with two allowed consecutive colors.** For natural numbers $b$ and $n$,
$\mathrm{CCo}_{b,b+1}(n)$ is the set of $n$-color compositions of $n$ that use only the colors $b$
and $b+1$: finite sequences of pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural numbers (part
$k_i$ with color $c_i$) such that $1 \le c_i \le k_i$ and $c_i \in \{b, b+1\}$ for every $i$, and
$k_1 + \dots + k_m = n$. -/
def ColorCompAllowed (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ (pc.2 = b ∨ pc.2 = b + 1)) ∧
      (l.map Prod.fst).sum = n }

/-- **n-color compositions with two prohibited consecutive colors.** For natural numbers $b$ and
$n$, $\mathrm{CCo}_{\widehat{b,b+1}}(n)$ is the set of $n$-color compositions of $n$ in which no
part has color $b$ or $b+1$: finite sequences of pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural
numbers (part $k_i$ with color $c_i$) such that $1 \le c_i \le k_i$, $c_i \ne b$ and
$c_i \ne b+1$ for every $i$, and $k_1 + \dots + k_m = n$. -/
def ColorCompProhibited (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ pc.2 ≠ b ∧ pc.2 ≠ b + 1) ∧
      (l.map Prod.fst).sum = n }

/-- **n-color compositions without color 2.** For a natural number $n$, $\mathrm{CCo}_{\hat 2}(n)$
is the set of $n$-color compositions of $n$ in which no part has color $2$: finite sequences of
pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural numbers (part $k_i$ with color $c_i$) such that
$1 \le c_i \le k_i$ and $c_i \ne 2$ for every $i$, and $k_1 + \dots + k_m = n$. -/
def ColorCompProhibit2 (n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ pc.2 ≠ 2) ∧
      (l.map Prod.fst).sum = n }

/-- **Count of n-color compositions with two consecutive colors.** An $n$-color composition of a
natural number $n$ is a finite sequence of parts, each a positive integer $k$ carrying a color
$c$ with $1 \le c \le k$, whose sizes sum to $n$. For natural numbers $b$ and $n$,
$\operatorname{cco}_{b,b+1}(n)$ is the number of $n$-color compositions of $n$ in which every
part has color $b$ or $b+1$. -/
noncomputable def ccoAllowed (b n : ℕ) : ℕ :=
  Nat.card (ColorCompAllowed b n)

/-- **Number of n-color compositions with two prohibited consecutive colors.** For natural numbers
$b$ and $n$, $\mathrm{cco}_{\widehat{b,b+1}}(n)$ is the number of elements of
$\mathrm{CCo}_{\widehat{b,b+1}}(n)$, that is, the number of $n$-color compositions of $n$ in which
no part has color $b$ or $b+1$. -/
noncomputable def ccoProhibited (b n : ℕ) : ℕ :=
  Nat.card (ColorCompProhibited b n)

/-- **Count of n-color compositions avoiding color 2.** An $n$-color composition of a natural
number $n$ is a finite sequence of parts, each a positive integer $k$ carrying a color $c$ with
$1 \le c \le k$, whose sizes sum to $n$. For a natural number $n$, $\operatorname{cco}_{\hat 2}(n)$
is the number of $n$-color compositions of $n$ in which no part has color $2$. -/
noncomputable def ccoProhibit2 (n : ℕ) : ℕ :=
  Nat.card (ColorCompProhibit2 n)

/-- **Integer extension of the count of n-color compositions with two consecutive colors.** For
a natural number $b$, this is the function from the integers to the integers that sends
$n \ge 0$ to $\operatorname{cco}_{b,b+1}(n)$, the number of $n$-color compositions of $n$ in
which every part has color $b$ or $b+1$, and sends every $n < 0$ to $0$. -/
noncomputable def ccoAllowedZ (b : ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (ccoAllowed b n.toNat : ℤ) else 0

/-- **Integer extension of the count of n-color compositions avoiding two consecutive colors.**
For a natural number $b$, this is the function from the integers to the integers that sends
$n \ge 0$ to $\operatorname{cco}_{\widehat{b,b+1}}(n)$, the number of $n$-color compositions of
$n$ in which no part has color $b$ or $b+1$, and sends every $n < 0$ to $0$. -/
noncomputable def ccoProhibitedZ (b : ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (ccoProhibited b n.toNat : ℤ) else 0

/-- **Splitting a ternary string at its zeros, with a prefix.** For strings $w$ and $a$ over
$\{0, 1, 2\}$, write $w = s_0 \, 0 \, s_1 \, 0 \cdots 0 \, s_m$ where $m$ is the number of $0$s
in $w$ and each $s_i$ is a (possibly empty) string without $0$. The result is the list of strings
$a s_0, s_1, \dots, s_m$, in this order, where $a s_0$ is the concatenation of $a$ and $s_0$. -/
def splitZerosAux : List (Fin 3) → List (Fin 3) → List (List (Fin 3))
  | [], acc => [acc]
  | x :: xs, acc =>
      if x = 0 then acc :: splitZerosAux xs [] else
        splitZerosAux xs (acc ++ [x])

/-- **Splitting a ternary string at its zeros.** For a string $w$ over $\{0, 1, 2\}$, the list of
the segments of $w$ obtained by cutting at every $0$: the part before the first $0$, the parts
between consecutive $0$s and the part after the last $0$, in order and including empty parts.
A string with $m$ zeros gives $m + 1$ segments; the empty string gives one empty segment. -/
def splitZeros (w : List (Fin 3)) : List (List (Fin 3)) :=
  splitZerosAux w []

/-- **Admissible ternary strings.** For natural numbers $b$ and $n$, the strings $w$ over
$\{0, 1, 2\}$ of length $n - 1$ (truncated subtraction, so length $0$ when $n = 0$) such that
every segment of $w$ obtained by cutting at its zeros (before the first zero, between
consecutive zeros and after the last zero, empty segments included) either consists only of
$1$s and has length at least $b - 1$, or consists only of $2$s and has length at least $b$.
In particular an empty segment is allowed exactly when $b \le 1$.

This is the segment form of the conditions in Theorem 2 of Hopkins and Wang (no $12$ or $21$
subwords, run-length bounds, and separation of successive zeros). -/
def TernaryAdmissible (b n : ℕ) : Type :=
  { w : List (Fin 3) // w.length = n - 1 ∧
    ∀ seg ∈ splitZeros w,
      ((∀ x ∈ seg, x = 1) ∧ b - 1 ≤ seg.length) ∨
        ((∀ x ∈ seg, x = 2) ∧ b ≤ seg.length) }

/-- **Compositions with two types of part 1 and no equal adjacent 1s.** For a natural
number $n$, $C^*_{1,2}(n)$ is the set of compositions of $n$ whose parts are $1_1$, $1_2$
(two types of part of size $1$) and $2$, such that no two adjacent parts are parts $1$ of
the same type.

A composition is encoded as a list over the symbols $0$, $1$, $2$, where $0$ and $1$ stand
for $1_1$ and $1_2$ and the symbol $2$ stands for the part $2$. -/
def TwoTypeComp (n : ℕ) : Type :=
  { l : List (Fin 3) //
    (l.map (fun s => if s.val < 2 then 1 else 2)).sum = n ∧
      l.IsChain (fun x y => 2 ≤ x.val ∨ 2 ≤ y.val ∨ x ≠ y) }

/-- **Tribonacci numbers with initial values $1, 0, 1$.** The sequence
$t : \mathbb{N} \to \mathbb{Z}$ with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$. -/
def tribNat : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => tribNat (n + 2) + tribNat (n + 1) + tribNat n

/-- **Hopkins–Wang tribonacci numbers on the integers.** Let $t(0) = 1$, $t(1) = 0$,
$t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for natural numbers $n \ge 3$. This
extends $t$ to an integer-valued function on all integers by setting $t(n) = 0$ for
$n < 0$. -/
def trib (n : ℤ) : ℤ :=
  if 0 ≤ n then tribNat n.toNat else 0

/-- **Recurrence for n-color compositions with two consecutive colors.** Fix a natural number
$b \ge 1$. For an integer $m$, let $c(m)$ be the number of $n$-color compositions of $m$ in
which every part has color $b$ or $b+1$ when $m \ge 0$, and $c(m) = 0$ when $m < 0$. Then for
every integer $n \ge 2$,
$$c(n) = c(n-1) + c(n-b) + c(n-b-1).$$

The source states the recurrence for positive $n$, but it fails at $n = 1$: for $b = 1$ the
left side is $1$ and the right side is $2$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 1. -/
theorem_wanted ccoAllowedZ_recurrence (b : ℕ) (hb : 1 ≤ b)
    (n : ℤ) (hn : 2 ≤ n) :
    ccoAllowedZ b n = ccoAllowedZ b (n - 1) +
      ccoAllowedZ b (n - b) + ccoAllowedZ b (n - b - 1)

/-- **Double-sum formula for n-color compositions with two consecutive colors.** Let $b \ge 1$
and $n \ge 1$ be natural numbers, and let $\operatorname{cco}_{b,b+1}(n)$ be the number of
$n$-color compositions of $n$ in which every part has color $b$ or $b+1$. Then
$$\operatorname{cco}_{b,b+1}(n) = \sum_{m=1}^{n} \sum_{i=0}^{n-bm}
\binom{i+m-1}{m-1} \binom{m}{n-bm-i},$$
where the upper limit $n - bm$ is read as $0$ when $bm > n$, and every term with $bm + i > n$
is $0$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 1. -/
theorem_wanted ccoAllowed_eq_sum (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    ccoAllowed b n =
      ∑ m ∈ Finset.Icc 1 n,
        ∑ i ∈ Finset.Icc 0 (n - b * m),
          if b * m + i ≤ n then
            Nat.choose (i + m - 1) (m - 1) *
              Nat.choose m (n - b * m - i)
          else 0

/-- **Bijection between n-color compositions with colors b, b+1 and ternary strings.** For all
natural numbers $b \ge 1$ and $n \ge 1$, there is a bijection between $\mathrm{CCo}_{b,b+1}(n)$,
the $n$-color compositions of $n$ using only the colors $b$ and $b+1$, and the set of strings of
length $n-1$ over the alphabet $\{0, 1, 2\}$ such that, when the string is cut at each of its
$0$s, every resulting segment (including the possibly empty segments before the first $0$, after
the last $0$, and between adjacent $0$s) either consists only of $1$s and has length at least
$b-1$, or consists only of $2$s and has length at least $b$.

The paper states the condition as: no subword $12$ or $21$, runs of $1$s of length at least
$b-1$, runs of $2$s of length at least $b$, and successive $0$s separated by at least $b-1$
digits. The segment form above also constrains the segments before the first and after the last
$0$; without that, the string $0$ would be a counterexample at $n = 2$, $b = 3$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 2. -/
theorem_wanted nonempty_equiv_colorCompAllowed_ternary
    (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    Nonempty (ColorCompAllowed b n ≃ TernaryAdmissible b n)

/-- **Binomial sum for n-color compositions with colors 1 and 2.** For every natural number
$n \ge 1$, the number $\operatorname{cco}_{1,2}(n)$ of $n$-color compositions of $n$ in which
every part has color $1$ or $2$ satisfies
$$\operatorname{cco}_{1,2}(n) = \sum_{m=0}^{\lfloor n/2 \rfloor} 2^m \binom{n}{2m}.$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 3. -/
theorem_wanted ccoAllowed_one_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    ccoAllowed 1 n =
      ∑ m ∈ Finset.range (n / 2 + 1), 2 ^ m * Nat.choose n (2 * m)

/-- **n-color compositions with colors 2, 3 and compositions with parts not divisible by 3.** For
every natural number $n \ge 1$, there is a bijection between $\mathrm{CCo}_{2,3}(n+1)$, the
$n$-color compositions of $n+1$ using only the colors $2$ and $3$, and the compositions of $n$ all
of whose parts are congruent to $1$ or $2$ modulo $3$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 4. -/
theorem_wanted nonempty_equiv_colorCompAllowed_two_composition_mod_three
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompAllowed 2 (n + 1) ≃
      { c : Composition n // ∀ k ∈ c.blocks, k % 3 = 1 ∨ k % 3 = 2 })

/-- **n-color compositions with colors 2, 3 and compositions with two kinds of 1.** For every
natural number $n$, there is a bijection between $\mathrm{CCo}_{2,3}(n+2)$, the $n$-color
compositions of $n+2$ using only the colors $2$ and $3$, and the compositions of $n$ whose parts
are $2$ or one of two types of part $1$, with no two adjacent parts $1$ of the same type.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 5. -/
theorem_wanted nonempty_equiv_colorCompAllowed_two_twoTypeComp
    (n : ℕ) :
    Nonempty (ColorCompAllowed 2 (n + 2) ≃ TwoTypeComp n)

/-- **Tribonacci numbers from $t(n-2)$ and a partial sum.** Let $t$ be the tribonacci numbers
with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every integer $n \ge 3$,
$$t(n) = t(n-2) + 2 \sum_{i=3}^{n} t(n-i).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 6. -/
theorem_wanted trib_eq_add_sum (n : ℤ) (hn : 3 ≤ n) :
    trib n = trib (n - 2) +
      2 * ∑ i ∈ Finset.Icc 3 n, trib (n - i)

/-- **Tribonacci numbers from $t(n-1)$ and alternate earlier terms.** Let $t$ be the tribonacci
numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for
$n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every integer $n \ge 3$,
$$t(n) = t(n-1) + 1 + 2 \sum_{i=1}^{\lfloor n/2 \rfloor - 1} t(n-2i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 7. -/
theorem_wanted trib_eq_add_one_add_sum (n : ℤ) (hn : 3 ≤ n) :
    trib n = trib (n - 1) + 1 +
      2 * ∑ i ∈ Finset.Icc 1 (n / 2 - 1), trib (n - 2 * i - 1)

/-- **Tribonacci partial-sum identity for $t(3k)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k) = 1 + \sum_{i=0}^{k} \bigl(t(3k-3i-1) + t(3k-3i-2)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul (k : ℕ) :
    trib (3 * (k : ℤ)) = 1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 2))

/-- **Tribonacci partial-sum identity for $t(3k+1)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k+1) = -1 + \sum_{i=0}^{k} \bigl(t(3k-3i) + t(3k-3i-1)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul_add_one (k : ℕ) :
    trib (3 * (k : ℤ) + 1) = -1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 2))

/-- **Tribonacci partial-sum identity for $t(3k+2)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k+2) = \sum_{i=0}^{k} \bigl(t(3k-3i+1) + t(3k-3i)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul_add_two (k : ℕ) :
    trib (3 * (k : ℤ) + 2) =
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 2))

/-- **Identity for $t(n) + t(n-2)$ when $n \ge 3$ and $n \equiv 0, 1 \pmod 3$.** Let $t$ be the
tribonacci numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every
natural number $k \ge 1$, both $n = 3k$ and $n = 3k + 1$ satisfy
$$t(n) + t(n-2) = 2 \sum_{i=0}^{k-1} t(n-3i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem_wanted trib_add_two_sub_three_mul (k : ℕ) (hk : 1 ≤ k) :
    trib (3 * (k : ℤ)) + trib (3 * (k : ℤ) - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) ∧
      trib (3 * (k : ℤ) + 1) + trib (3 * (k : ℤ) + 1 - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1)

/-- **Identity for $t(n) + t(n-2)$ when $n \ge 3$ and $n \equiv 2 \pmod 3$.** Let $t$ be the
tribonacci numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every
natural number $k \ge 1$, with $n = 3k + 2$,
$$t(n) + t(n-2) = 2 + 2 \sum_{i=0}^{k-1} t(n-3i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem_wanted trib_add_two_sub_three_mul_add_two (k : ℕ)
    (hk : 1 ≤ k) :
    trib (3 * (k : ℤ) + 2) + trib (3 * (k : ℤ) + 2 - 2) =
      2 + 2 * ∑ i ∈ Finset.range k,
        trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1)

/-- **Fibonacci identity for n-color compositions with colors 3 and 4.** For a natural number
$m$, let $\operatorname{cco}_{3,4}(m)$ be the number of $n$-color compositions of $m$ in which
every part has color $3$ or $4$, and let $F_k$ be the Fibonacci numbers with $F_0 = 0$ and
$F_1 = 1$. Then for every natural number $n \ge 3$,
$\operatorname{cco}_{3,4}(n) + \operatorname{cco}_{3,4}(n-2) = F_{n-1}$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 10. -/
theorem_wanted ccoAllowed_three_add (n : ℕ) (hn : 3 ≤ n) :
    ccoAllowed 3 n + ccoAllowed 3 (n - 2) = Nat.fib (n - 1)

/-- **Recurrence for n-color compositions avoiding two consecutive colors.** Fix a natural number
$b \ge 1$. For an integer $m$, let $c(m)$ be the number of $n$-color compositions of $m$ in
which no part has color $b$ or $b+1$ when $m \ge 0$, and $c(m) = 0$ when $m < 0$. Then for
every integer $n \ge 3$,
$$c(n) = 3\,c(n-1) - c(n-2) - c(n-b) + c(n-b-2).$$

The source states the recurrence without a range, but it fails at $n = 0$, $1$ and $2$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 11. -/
theorem_wanted ccoProhibitedZ_recurrence (b : ℕ) (hb : 1 ≤ b)
    (n : ℤ) (hn : 3 ≤ n) :
    ccoProhibitedZ b n = 3 * ccoProhibitedZ b (n - 1) -
      ccoProhibitedZ b (n - 2) - ccoProhibitedZ b (n - b) +
      ccoProhibitedZ b (n - b - 2)

/-- **n-color compositions without colors 1, 2 and compositions with parts 1, 2 mod 4.** For
every natural number $n \ge 1$, there is a bijection between $\mathrm{CCo}_{\widehat{1,2}}(n+2)$,
the $n$-color compositions of $n+2$ in which no part has color $1$ or $2$, and the compositions of
$n$ all of whose parts are congruent to $1$ or $2$ modulo $4$.

The hypothesis $n \ge 1$ is needed: at $n = 0$ the two sets have $0$ and $1$ elements.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 12. -/
theorem_wanted nonempty_equiv_colorCompProhibited_one_composition_mod_four
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompProhibited 1 (n + 2) ≃
      { c : Composition n // ∀ k ∈ c.blocks, k % 4 = 1 ∨ k % 4 = 2 })

/-- **n-color compositions without colors 1, 2 and palindromic compositions.** For every natural
number $n \ge 1$, there is a bijection between $\mathrm{CCo}_{\widehat{1,2}}(n)$, the $n$-color
compositions of $n$ in which no part has color $1$ or $2$, and the palindromic compositions of
$\max(2n-5, 0)$ that have no part equal to $2$ and an odd number of parts.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 13. -/
theorem_wanted nonempty_equiv_colorCompProhibited_one_palindromic
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompProhibited 1 n ≃
      { c : Composition (2 * n - 5) //
        (∀ k ∈ c.blocks, k ≠ 2) ∧ c.blocks = c.blocks.reverse ∧
          Odd c.blocks.length })

/-- **n-color compositions avoiding colors 1 and 2 versus avoiding color 2.** For a natural number
$m$, let $\operatorname{cco}_{\widehat{1,2}}(m)$ be the number of $n$-color compositions of $m$ in
which no part has color $1$ or $2$, and let $\operatorname{cco}_{\hat 2}(m)$ be the number in which
no part has color $2$. Then for every natural number $k \ge 1$,
$\operatorname{cco}_{\widehat{1,2}}(3k) = \operatorname{cco}_{\hat 2}(2k-1)$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 14. -/
theorem_wanted ccoProhibited_one_three_mul (k : ℕ) (hk : 1 ≤ k) :
    ccoProhibited 1 (3 * k) = ccoProhibit2 (2 * k - 1)

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
