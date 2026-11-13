/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Combinatorial identities for the bi-periodic Fibonacci numbers squared

Statements from Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the
Bi-Periodic Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article
belaggoun01132024.

The bi-periodic Fibonacci numbers squared `q²_n` are defined by the paper's third-order
recurrence (1.1) (`biPeriodicFibonacciSq`). The weighted tilings of Section 2 are modelled on the
`2n` half-cells `0, …, 2n - 1` of an `n`-board, half-cell `h` lying in cell `⌊h/2⌋ + 1`: a
`(1/2, 1/2)`-fence at position `k` has its posts on half-cells `k` and `k + 2` (gap `k + 1`), a
tiling is a set `F` of fence positions with pairwise disjoint posts, and every half-cell not
covered by a post holds a half-square, of weight `a` in an odd cell and `b` in an even cell. Two
fences at positions `k`, `k + 1` interlock into a bifence; it is a free bifence (a metatile of its
own, covering two whole cells) exactly when `k` is even.

The statements with `a = b = 1` use `Nat.fib`; `ξ(n) = n % 2`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Fib.Basic

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- **Bi-periodic Fibonacci numbers squared.** For elements $a$ and $b$ of a field $K$, the
bi-periodic Fibonacci numbers squared $q^2_n \in K$ ($n \ge 0$) are defined by $q^2_0 = 0$,
$q^2_1 = 1$, $q^2_2 = a^2$ and, for $n \ge 3$,
$$
q^2_n = \frac{a}{b}(ab+1)\,q^2_{n-1} + (ab+1)\,q^2_{n-2} - \frac{a}{b}\,q^2_{n-3}
$$
if $n$ is even, and
$$
q^2_n = \frac{b}{a}(ab+1)\,q^2_{n-1} + (ab+1)\,q^2_{n-2} - \frac{b}{a}\,q^2_{n-3}
$$
if $n$ is odd.

Division by zero gives $0$, so the sequence is defined for all $a$ and $b$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
def biPeriodicFibonacciSq {K : Type*} [Field K] (a b : K) : ℕ → K
  | 0 => 0
  | 1 => 1
  | 2 => a ^ 2
  | n + 3 =>
    if Even (n + 3) then
      a / b * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
        (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - a / b * biPeriodicFibonacciSq a b n
    else
      b / a * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
        (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - b / a * biPeriodicFibonacciSq a b n

/-- **Zeroth bi-periodic Fibonacci number squared.** For elements $a$ and $b$ of a field $K$, the
bi-periodic Fibonacci number squared $q^2_0$ equals $0$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_zero {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 0 = 0 := rfl

/-- **First bi-periodic Fibonacci number squared.** For elements $a$ and $b$ of a field $K$, the
bi-periodic Fibonacci number squared $q^2_1$ equals $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_one {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 1 = 1 := rfl

/-- **Second bi-periodic Fibonacci number squared.** For elements $a$ and $b$ of a field $K$, the
bi-periodic Fibonacci number squared $q^2_2$ equals $a^2$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_two {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 2 = a ^ 2 := rfl

/-- **Recurrence for the bi-periodic Fibonacci numbers squared.** For elements $a$ and $b$ of a
field $K$ and every $n \ge 0$, the bi-periodic Fibonacci numbers squared $q^2_m$ satisfy
$$
q^2_{n+3} = \frac{a}{b}(ab+1)\,q^2_{n+2} + (ab+1)\,q^2_{n+1} - \frac{a}{b}\,q^2_n
$$
if $n + 3$ is even, and
$$
q^2_{n+3} = \frac{b}{a}(ab+1)\,q^2_{n+2} + (ab+1)\,q^2_{n+1} - \frac{b}{a}\,q^2_n
$$
if $n + 3$ is odd.

Division by zero gives $0$, so this holds for all $a$ and $b$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1, (1.1). -/
theorem biPeriodicFibonacciSq_add_three {K : Type*} [Field K] (a b : K) (n : ℕ) :
    biPeriodicFibonacciSq a b (n + 3) =
      if Even (n + 3) then
        a / b * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
          (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - a / b * biPeriodicFibonacciSq a b n
      else
        b / a * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
          (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - b / a * biPeriodicFibonacciSq a b n :=
  rfl

/-- **Fence tilings of a board.** Number the half-cells of an $n$-board $0, \dots, 2n - 1$. The
tilings of the $n$-board by half-squares and $(1/2, 1/2)$-fences are encoded as the sets $F$ of
fence positions $k < 2n - 2$ (the fence at $k$ has posts on half-cells $k$ and $k + 2$) whose
posts are pairwise disjoint, that is, $k + 2 \notin F$ for every $k \in F$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilings (n : ℕ) : Finset (Finset ℕ) :=
  (range (2 * n - 2)).powerset.filter fun F => ∀ k ∈ F, k + 2 ∉ F

/-- **Weight of a fence tiling.** Let $a$, $b$ be elements of a commutative semiring, let $n \ge 0$,
and let $F$ be a finite set of natural numbers (fence positions; the fence at $k$ has posts on
half-cells $k$ and $k + 2$). The weight of $F$ on the $n$-board is the product, over the
half-cells $h \in \{0, \dots, 2n - 1\}$ that neither lie in $F$ nor equal $k + 2$ for some
$k \in F$, of $a$ if $\lfloor h/2 \rfloor$ is even (a half-square in the odd cell
$\lfloor h/2 \rfloor + 1$) and of $b$ otherwise (a half-square in an even cell).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilingWeight {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) (F : Finset ℕ) : R :=
  ∏ h ∈ range (2 * n) \ (F ∪ F.image (· + 2)), if h / 2 % 2 = 0 then a else b

/-- **Weighted count of fence tilings.** Let $a$, $b$ be elements of a commutative semiring and
$n \ge 0$. The weighted number $S_n$ of tilings of an $n$-board by half-squares and
$(1/2, 1/2)$-fences is the sum, over all fence tilings $F$ of the $n$-board, of the weight of $F$,
in which a half-square weighs $a$ in an odd cell and $b$ in an even cell and fences weigh $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2 (before Lemma 2.1). -/
def fenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ fenceTilings n, fenceTilingWeight a b n F

/-- **Weighted fence tilings of the empty board.** For elements $a$ and $b$ of a commutative
semiring $R$, the weighted number $S_0$ of tilings of the $0$-board by half-squares and
$(1/2, 1/2)$-fences equals $1$: the only tiling is the empty one.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
proof of Lemma 2.1. -/
@[simp]
theorem fenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) : fenceTilingSum a b 0 = 1 := by
  simp [fenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- **Weighted fence tilings of the one-cell board.** For elements $a$ and $b$ of a commutative
semiring $R$, the weighted number $S_1$ of tilings of a $1$-board by half-squares and
$(1/2, 1/2)$-fences, a half-square weighing $a$ in an odd cell and $b$ in an even cell, equals
$a^2$: the only tiling has two half-squares in cell $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
proof of Theorem 2.2. -/
@[simp]
theorem fenceTilingSum_one {R : Type*} [CommSemiring R] (a b : R) : fenceTilingSum a b 1 = a ^ 2 := by
  simp [fenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton, prod_range_succ, sq]

/-- **Weighted count of bifence-free fence tilings.** Let $a$, $b$ be elements of a commutative
semiring and $n \ge 0$. Two fences at positions $k$ and $k + 1$ form a bifence. The weighted number
$C_n$ of tilings with no bifence is the sum of the weights, with half-square weights $a$ and $b$,
of the fence tilings $F$ of the $n$-board with no bifence, that is, with $k + 1 \notin F$ for every
$k \in F$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15. -/
def noBifenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ (fenceTilings n).filter (fun F => ∀ k ∈ F, k + 1 ∉ F), fenceTilingWeight a b n F

/-- **Tilings of the empty board with no bifence.** For all elements $a$, $b$ of a commutative
semiring, the weighted number $C_0$ of tilings of the $0$-board with no bifence, with half-square
weights $a$ and $b$, equals $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15. -/
@[simp]
theorem noBifenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) :
    noBifenceTilingSum a b 0 = 1 := by
  simp [noBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- **Weighted tilings with no free bifence.** For elements $a$, $b$ of a commutative semiring
and $n \ge 0$, number the cells of an $n$-board $1, \dots, n$ and its $2n$ half-cells
$0, \dots, 2n - 1$, half-cell $h$ lying in cell $\lfloor h/2 \rfloor + 1$. A
$(1/2, 1/2)$-fence at position $k$ has its posts on half-cells $k$ and $k + 2$. Then $R_n$ is
the sum of the weights of the tilings of the board by half-squares and such fences that contain
no free bifence, that is, no two fences at positions $k$ and $k + 1$ with $k$ even. The weight
of a tiling is the product over its half-squares of $a$ for a half-square in an odd cell and
$b$ for one in an even cell.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
def noFreeBifenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ (fenceTilings n).filter (fun F => ∀ k ∈ F, Even k → k + 1 ∉ F), fenceTilingWeight a b n F

/-- **Tilings of the empty board with no free bifence.** For all elements $a$, $b$ of a
commutative semiring, the weighted number $R_0$ of tilings of the $0$-board by half-squares and
$(1/2, 1/2)$-fences with no free bifence, with half-squares weighted by $a$ and $b$, equals $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
@[simp]
theorem noFreeBifenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) :
    noFreeBifenceTilingSum a b 0 = 1 := by
  simp [noFreeBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- **Tilings of the one-cell board with no free bifence.** For all elements $a$, $b$ of a
commutative semiring, the weighted number $R_1$ of tilings of the $1$-board with no free bifence,
with half-square weights $a$ and $b$, equals $a^2$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
@[simp]
theorem noFreeBifenceTilingSum_one {R : Type*} [CommSemiring R] (a b : R) :
    noFreeBifenceTilingSum a b 1 = a ^ 2 := by
  simp [noFreeBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton, prod_range_succ,
    sq]

/-- **Recurrence for weighted fence tilings of even boards.** Let $a$ and $b$ be elements of a
commutative semiring $R$, and let $S_m$ be the weighted number of tilings of an $m$-board, with
cells numbered $1, \dots, m$, by half-squares and $(1/2, 1/2)$-fences, a half-square weighing $a$
in an odd cell and $b$ in an even cell. Then for every even $n \ge 2$,
$$
S_n = b^2 S_{n-1} + (2ab+1) S_{n-2} +
2ab \sum_{j=2}^{n/2} S_{n-2j} + 2b^2 \sum_{j=1}^{n/2-1} S_{n-2j-1}.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`). -/
public theorem_wanted fenceTilingSum_even {R : Type*} [CommSemiring R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    fenceTilingSum a b n =
      b ^ 2 * fenceTilingSum a b (n - 1) + (2 * a * b + 1) * fenceTilingSum a b (n - 2) +
        2 * a * b * ∑ j ∈ Icc 2 (n / 2), fenceTilingSum a b (n - 2 * j) +
        2 * b ^ 2 * ∑ j ∈ Icc 1 (n / 2 - 1), fenceTilingSum a b (n - 2 * j - 1)

/-- **Recurrence for weighted fence tilings of odd boards.** Let $a$ and $b$ be elements of a
commutative semiring $R$, and let $S_m$ be the weighted number of tilings of an $m$-board, with
cells numbered $1, \dots, m$, by half-squares and $(1/2, 1/2)$-fences, a half-square weighing $a$
in an odd cell and $b$ in an even cell. Then for every odd $n \ge 3$,
$$
S_n = a^2 S_{n-1} + (2ab+1) S_{n-2} +
2ab \sum_{j=2}^{(n-1)/2} S_{n-2j} + 2a^2 \sum_{j=1}^{(n-1)/2} S_{n-2j-1}.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`). -/
public theorem_wanted fenceTilingSum_odd {R : Type*} [CommSemiring R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) (ho : Odd n) :
    fenceTilingSum a b n =
      a ^ 2 * fenceTilingSum a b (n - 1) + (2 * a * b + 1) * fenceTilingSum a b (n - 2) +
        2 * a * b * ∑ j ∈ Icc 2 ((n - 1) / 2), fenceTilingSum a b (n - 2 * j) +
        2 * a ^ 2 * ∑ j ∈ Icc 1 ((n - 1) / 2), fenceTilingSum a b (n - 2 * j - 1)

/-- **Fence tilings and the bi-periodic Fibonacci numbers squared.** Let $a$ and $b$ be nonzero
elements of a field $K$. For every $n \ge 0$, let $S_n$ be the weighted number of tilings of an
$n$-board, with cells numbered $1, \dots, n$, by half-squares and $(1/2, 1/2)$-fences, a
half-square weighing $a$ in an odd cell and $b$ in an even cell. Then $S_n$ equals the
bi-periodic Fibonacci number squared $q^2_{n+1}$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Theorem 2.2 (`fq-2024-belaggoun01132024-thm-2.2`). -/
public theorem_wanted fenceTilingSum_eq_biPeriodicFibonacciSq {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    fenceTilingSum a b n = biPeriodicFibonacciSq a b (n + 1)

/-- **Squared Fibonacci numbers as a double binomial sum.** Let $F_k$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$). For every natural number $n$,
$$
F_{n+1}^2 = \sum_{i=0}^{\lfloor 2n/3 \rfloor} \sum_{j=0}^{i} \binom{i}{j} \binom{2n-3i}{j} 2^j.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.3 (`fq-2024-belaggoun01132024-cor-3.3`). -/
public theorem_wanted fib_succ_sq_eq_sum_choose_mul_choose (n : ℕ) :
    Nat.fib (n + 1) ^ 2 =
      ∑ i ∈ range (2 * n / 3 + 1), ∑ j ∈ range (i + 1),
        i.choose j * (2 * n - 3 * i).choose j * 2 ^ j

/-- **Sum of squared Fibonacci numbers from three consecutive squares.** Let $F_j$ denote the
$j$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every integer $n \ge 3$,
$$2 \sum_{j=1}^{n-2} F_j^2 = F_n^2 - F_{n-1}^2 - F_{n-2}^2.$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.5 (`fq-2024-belaggoun01132024-cor-3.5`). -/
public theorem_wanted two_mul_sum_fib_sq {n : ℕ} (hn : 3 ≤ n) :
    2 * ∑ j ∈ Icc 1 (n - 2), (Nat.fib j : ℤ) ^ 2 =
      (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - 1) : ℤ) ^ 2 - (Nat.fib (n - 2) : ℤ) ^ 2

/-- **Squared Fibonacci numbers as weighted sums of squares.** Let $F_k$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and let $\xi(m) = m \bmod 2$. For every natural number $n \ge 1$,
$$
F_{n+1}^2 - \xi(n+1) = \sum_{k=1}^{n} (n-k+1) F_k^2 = \sum_{k=1}^{n} k F_{n-k+1}^2.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.10 (`fq-2024-belaggoun01132024-cor-3.10`). -/
public theorem_wanted fib_succ_sq_sub_parity_eq_sum {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, ((n - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2 ∧
      (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, (k : ℤ) * (Nat.fib (n - k + 1) : ℤ) ^ 2

/-- **Addition formula for squared Fibonacci numbers.** Let $F_k$ denote the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$). For all natural numbers $m \ge 1$ and $n \ge 2$,
$$
F_{m+n}^2 = F_{m+1}^2 F_n^2 + F_m^2 F_{n-1}^2 +
2 \left(\sum_{i=1}^{m} F_i^2\right) \left(\sum_{j=1}^{n-1} F_j^2\right).
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.12 (`fq-2024-belaggoun01132024-cor-3.12`). -/
public theorem_wanted fib_add_sq_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    Nat.fib (m + n) ^ 2 =
      Nat.fib (m + 1) ^ 2 * Nat.fib n ^ 2 + Nat.fib m ^ 2 * Nat.fib (n - 1) ^ 2 +
        2 * (∑ i ∈ Icc 1 m, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 (n - 1), Nat.fib j ^ 2

/-- **Recurrence for weighted tilings with no free bifence.** Let $a$ and $b$ be nonzero elements
of a field, and let $R_n$ be the weighted number of tilings of an $n$-board by half-squares and
$(1/2, 1/2)$-fences with no free bifence, where a half-square has weight $a$ in an odd cell and
$b$ in an even cell (cells numbered $1, \dots, n$). For every $n \ge 2$,
$$R_n = \frac{b}{a}(ab + 1) R_{n-1} + ab\, R_{n-2}$$
if $n$ is even, and
$$R_n = \frac{a}{b}(ab + 1) R_{n-1} + ab\, R_{n-2}$$
if $n$ is odd.

The initial values are $R_0 = 1$ and $R_1 = a^2$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13 (`fq-2024-belaggoun01132024-lem-3.13`). -/
public theorem_wanted noFreeBifenceTilingSum_rec {K : Type*} [Field K] {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    noFreeBifenceTilingSum a b n =
      (if Even n then b / a else a / b) * (a * b + 1) * noFreeBifenceTilingSum a b (n - 1) +
        a * b * noFreeBifenceTilingSum a b (n - 2)

/-- **Closed formula for bifence-free fence tilings.** Let $a$, $b$ be nonzero elements of a field
and let $\xi(n) = n \bmod 2$. For every natural number $n$, the weighted number $C_n$ of tilings of
the $n$-board by half-squares and $(1/2, 1/2)$-fences with no bifence, with half-square weights
$a$ and $b$, is
$$
C_n = \left(\frac{a}{b}\right)^{\xi(n)}
\sum_{i=0}^{\lfloor 2n/3 \rfloor} \binom{2n-2i}{i} (ab)^{n-i}.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15 (`fq-2024-belaggoun01132024-lem-3.15`). -/
public theorem_wanted noBifenceTilingSum_eq_sum_choose {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    noBifenceTilingSum a b n =
      (a / b) ^ (n % 2) *
        ∑ i ∈ range (2 * n / 3 + 1), ((2 * n - 2 * i).choose i : K) * (a * b) ^ (n - i)

end

end MetaMathlibExt
