/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.NumberTheory.Rayleigh
public import MathlibExt.NumberTheory.BronzeMetallicIdentities
public import MathlibExt.NumberTheory.GreedyOddFibonacciFloor
public import MathlibExt.NumberTheory.OddFibonacciGoldenRatio
public import MathlibExt.NumberTheory.OddFibonacciRepresentation
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.PellSilverRatio
public import MathlibExt.NumberTheory.OlympicGamesNumerationExistsPellHalfCompanionRepresentation
public import MathlibExt.NumberTheory.OlympicGamesNumerationExistsTwoPellHalfCompanionRepresentation
public import MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyBronzeCompanionSumMul
public import MathlibExt.NumberTheory.OlympicGamesBronzePositions

/-!
# Fibonacci and Pell numeration identities from the Olympic games

Statements from Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three
Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3.

The paper's Fibonacci numbers `F_n` are `Nat.fib n`, its Pell numbers `P_n` are `pellNumber n`
(`0, 1, 2, 5, 12, …`), and its half-companion Pell numbers `H_n` are `pellLucasSequence n`
(`1, 1, 3, 7, 17, …`, OEIS A001333). The constant `α = 1 + √2` is fixed in Section 4 of the
paper.

The bronze numbers `B_n` (`0, 1, 3, 10, 33, …`, `B_{n+1} = 3B_n + B_{n-1}`) are
`lucasU bronzeLucasParams n`; the companion bronze numbers of the first and second type are
`C_n = B_{n+1} - 2B_n` (`1, 1, 4, 13, 43, …`) and `D_n = B_{n+1} - B_n` (`1, 2, 7, 23, 76, …`),
i.e. the paper's `C_n = B_n + B_{n-1}` and `D_n = 2B_n + B_{n-1}` with `B_{-1} = 1`.

The floor identities (Theorems 2, 6, 10) concern the representations of Theorems 1, 4, 5, 8, 9
built greedily in their proofs ("choose the largest …"). The greedy digit sequence is
characterized by partial sums: for every `m`, the part of the sum below the `m`-th term is less
than the `m`-th term. The printed digit conditions do not single it out, and the identities fail
for other digit sequences satisfying them (e.g. `26 = F_7 + 2F_5 + F_3 + F_1` satisfies the
conditions of Theorem 1 with nonzero top digit, but `⌊26φ⌋ = 42 ≠ 41 = F_8 + 2F_6 + F_4 + F_2`).
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **P-positions of the gold game.** Let $\varphi$ be the golden ratio and $F_n$ the Fibonacci
numbers ($F_1 = F_2 = 1$). In the gold game a heap of $n$ tokens may be removed entirely when
$n = \lfloor k\varphi \rfloor$ for some integer $k \ge 1$, and $i$ tokens may be removed from a
heap of $n > i$ tokens, leaving $n - i$, when $i = \lfloor k(1 + \varphi) \rfloor$ for some
integer $k \ge 1$ (the Beatty octal moves for $\varphi$ and $1 + \varphi$). Let $S$ be the set of
natural numbers consisting of $0$ and the $F_{2k+1}$ for $k \ge 1$, that is $0, 2, 5, 13, 34, \dots$
Then $S$ is stable: no move leads from a heap size in $S$ to a heap size in $S$. And $S$ is
absorbing: from every heap size outside $S$ some move leads to a heap size in $S$.

Since every move shrinks the heap, a stable and absorbing set is the set of P-positions, so the
P-positions of the gold game are exactly the heap sizes in $S$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 3. -/
theorem_wanted goldGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔ x = 0 ∨ ∃ k, 1 ≤ k ∧ x = Nat.fib (2 * k + 1)) :
    (∀ x y, x ∈ P → beattyOctalMove Real.goldenRatio (1 + Real.goldenRatio) x y → y ∉ P) ∧
      ∀ x, x ∉ P → ∃ y, beattyOctalMove Real.goldenRatio (1 + Real.goldenRatio) x y ∧ y ∈ P

/-- **Floor of greedy Pell sums times $1 + \sqrt 2$.** Let $P_n$ be the Pell numbers ($P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). Let $R_k = P_k$ and $R'_k = H_k$ for odd $k$, and
$R_k = H_k$ and $R'_k = P_k$ for even $k$. Let $n$ be a natural number and $a_1, a_2, \dots$
natural numbers such that $\sum_{k=1}^{m-1} a_k R_k < R_m$ for every $1 \le m \le n + 1$, and let
$t = \sum_{k=1}^{n} a_k R_k$. Then $\lfloor t (1 + \sqrt 2) \rfloor = \sum_{k=1}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 5;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (1). -/
theorem_wanted floor_greedy_pell_halfCompanion_sum_mul_one_add_sqrt_two (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellLucasSequence k else pellNumber k)
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, a k * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, a k * R k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ =
      ∑ k ∈ Icc 1 n, a k * R' (k + 1)

/-- **Floor of greedy sums of $2P_k$ and $H_k$ times $(2 + \sqrt 2)/2$.** Let $P_k$ be the Pell
numbers and $H_k$ the Pell–Lucas numbers ($H_0 = H_1 = 1$, $H_{k+2} = 2H_{k+1} + H_k$). Put
$R_k = 2P_k$ and $R'_k = P_k$ for odd $k$, and $R_k = R'_k = H_k$ for even $k$. Let $n$ be a
natural number and $a_0, a_1, \dots$ natural numbers such that $\sum_{k<m} a_k R_k < R_m$ for
every $m \le n + 1$, and let $t = \sum_{k=0}^{n} a_k R_k$. Then
$\lfloor t(2 + \sqrt 2)/2 \rfloor = \sum_{k=0}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of $t$ by the
$R_k$; $n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (2). -/
theorem_wanted floor_greedy_two_pell_halfCompanion_sum_mul (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), a k * R k : ℕ) : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ =
      ∑ k ∈ range (n + 1), a k * R' (k + 1)

/-- **P-positions of the silver game.** Let $P_n$ be the Pell numbers and $H_n$ the Pell–Lucas
numbers ($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). In the silver game a heap of $n$ tokens
may be removed entirely when $n = \lfloor k(1 + \sqrt 2) \rfloor$ for some integer $k \ge 1$, and
$i$ tokens may be removed from a heap of $n > i$ tokens, leaving $n - i$, when
$i = \lfloor k(2 + \sqrt 2)/2 \rfloor$ for some integer $k \ge 1$ (the Beatty octal moves for
$1 + \sqrt 2$ and $(2 + \sqrt 2)/2$). Let $S$ be the set of natural numbers consisting of $0$ and
the $P_{2k+1}$ and $H_{2k+2}$ for $k \ge 0$, that is $0, 1, 3, 5, 17, 29, 99, \dots$ Then $S$ is
stable: no move leads from a heap size in $S$ to a heap size in $S$. And $S$ is absorbing: from
every heap size outside $S$ some move leads to a heap size in $S$.

Since every move shrinks the heap, a stable and absorbing set is the set of P-positions, so the
P-positions of the silver game are exactly the heap sizes in $S$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 7. -/
theorem_wanted silverGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔
      x = 0 ∨ ∃ k, x = pellNumber (2 * k + 1) ∨ x = pellLucasSequence (2 * k + 2)) :
    (∀ x y, x ∈ P → beattyOctalMove (1 + Real.sqrt 2) ((2 + Real.sqrt 2) / 2) x y → y ∉ P) ∧
      ∀ x, x ∉ P → ∃ y, beattyOctalMove (1 + Real.sqrt 2) ((2 + Real.sqrt 2) / 2) x y ∧ y ∈ P

/-- **Mixed bronze numeration.** Let $B_n$ be the bronze numbers ($B_0 = 0$, $B_1 = 1$,
$B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let $C_n = B_{n+1} - 2B_n$ and
$D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and second type. Let $R$ be
the integer sequence with $R_{3m} = D_{2m}$, $R_{3m+1} = 3B_{2m+1}$ and
$R_{3m+2} = B_{2m+1} + C_{2m+2}$ for all $m \ge 0$. Then for every positive integer $t$ there are
a natural number $n$ and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=0}^{n} a_k R_k$, $a_k = 0$ for every $k > n$, and: (3) $a_0 \le 2$, and
$a_0 \le 1$ if $a_1 = 1$ or $a_2 = 1$; (4) for every $k > 0$, $a_k \le 4$ if $3 \mid k$ and
$a_k \le 1$ otherwise; (5) for every $k$ with $a_k = 4$, $a_{k-1} = a_{k+1} = 0$,
$a_{k-3} < 4$ and $a_{k+3} < 4$; (6) for every $m \ge 0$, if $a_{3m+1} = 1$ then
$a_{3m+2} = 0$, and if $a_{3m+2} = 1$ then $a_{3m+1} = 0$; (7) for every $m \ge 1$ with
$a_{3m} = 3$, if $a_{3m+1} = 1$ or $a_{3m+2} = 1$ then $a_{3m-1} = a_{3m-2} = 0$, and if
$a_{3m-1} = 1$ or $a_{3m-2} = 1$ then $a_{3m+1} = a_{3m+2} = 0$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 8. -/
theorem_wanted exists_mixed_bronze_representation (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2))
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), R n ≤ t ∧ (t : ℤ) < R (n + 1) ∧
      (t : ℤ) = ∑ k ∈ range (n + 1), (a k : ℤ) * R k ∧ (∀ k, n < k → a k = 0) ∧
      a 0 ≤ 2 ∧ ((a 1 = 1 ∨ a 2 = 1) → a 0 ≤ 1) ∧
      (∀ k, 0 < k → (k % 3 = 0 → a k ≤ 4) ∧ (k % 3 ≠ 0 → a k ≤ 1)) ∧
      (∀ k, a k = 4 → a (k - 1) = 0 ∧ a (k + 1) = 0 ∧ a (k - 3) < 4 ∧ a (k + 3) < 4) ∧
      (∀ m, (a (3 * m + 1) = 1 → a (3 * m + 2) = 0) ∧ (a (3 * m + 2) = 1 → a (3 * m + 1) = 0)) ∧
      ∀ m, 1 ≤ m → a (3 * m) = 3 →
        ((a (3 * m + 1) = 1 ∨ a (3 * m + 2) = 1) → a (3 * m - 1) = 0 ∧ a (3 * m - 2) = 0) ∧
        ((a (3 * m - 1) = 1 ∨ a (3 * m - 2) = 1) → a (3 * m + 1) = 0 ∧ a (3 * m + 2) = 0)

/-- **Numeration by bronze and companion bronze numbers.** Let $B_n$ be the bronze numbers
($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ be the integer sequence with $R_{3m+1} = B_{2m+1}$, $R_{3m+2} = C_{2m+2}$
and $R_{3m} = D_{2m}$ for all $m \ge 0$. Then for every positive integer $t$ there are a natural
number $n \ge 1$ and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=1}^{n} a_k R_k$, $a_k = 0$ for every $k > n$, and: (3) $a_1 \le 3$, and
$a_2 = a_3 = 0$ if $a_1 = 3$; (4) for every $k > 1$, $a_k \le 4$ if $k \equiv 1 \pmod 3$ and
$a_k \le 1$ otherwise; (5) for every $k$ with $a_k = 4$, $a_{k-1} = a_{k+1} = 0$, $a_{k-3} < 4$
and $a_{k+3} < 4$, where an index below $0$ is read as $0$.

The paper's conditions (6) and (7) are omitted: no representation of $50$ satisfies (6)
together with (2)–(5), and the greedy representation $410 = 3B_5 + D_4 + D_2$
($327 + 76 + 7$; digits $a_7 = 3$, $a_6 = 1$, $a_3 = 1$) violates (7).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 9 (1)–(5). -/
theorem_wanted exists_bronze_companion_representation (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧ R n ≤ t ∧ (t : ℤ) < R (n + 1) ∧
      (t : ℤ) = ∑ k ∈ Icc 1 n, (a k : ℤ) * R k ∧ (∀ k, n < k → a k = 0) ∧
      a 1 ≤ 3 ∧ (a 1 = 3 → a 2 = 0 ∧ a 3 = 0) ∧
      (∀ k, 1 < k → (k % 3 = 1 → a k ≤ 4) ∧ (k % 3 ≠ 1 → a k ≤ 1)) ∧
      ∀ k, a k = 4 → a (k - 1) = 0 ∧ a (k + 1) = 0 ∧ a (k - 3) < 4 ∧ a (k + 3) < 4

/-- **Floor of greedy mixed bronze sums times $(5 + \sqrt{13})/6$.** Let $B_n$ be the bronze
numbers ($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ and $R'$ be the integer sequences with $R_{3m} = D_{2m}$,
$R_{3m+1} = 3B_{2m+1}$, $R_{3m+2} = B_{2m+1} + C_{2m+2}$ and $R'_{3m} = D_{2m}$,
$R'_{3m+1} = B_{2m+1}$, $R'_{3m+2} = C_{2m+2}$ for all $m \ge 0$. Let $n$ be a natural number
and $a_0, a_1, a_2, \dots$ natural numbers such that $\sum_{k=0}^{m-1} a_k R_k < R_m$ for every
$m \le n + 1$, and let $t = \sum_{k=0}^{n} a_k R_k$. Then
$\lfloor t (5 + \sqrt{13})/6 \rfloor = \sum_{k=0}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 8;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (2). -/
theorem_wanted floor_greedy_mixed_bronze_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2))
    (hR' : ∀ k, R' k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else bronzeCompanionFirst (2 * (k / 3) + 2))
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), (a k : ℤ) * R k : ℤ) : ℝ) * ((5 + Real.sqrt 13) / 6)⌋ =
      ∑ k ∈ range (n + 1), (a k : ℤ) * R' (k + 1)

end

end MetaMathlibExt
