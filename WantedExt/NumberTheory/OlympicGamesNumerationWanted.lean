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
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

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

/-- **Odd-indexed Fibonacci numbers times the golden ratio.** Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and $\varphi = (1 + \sqrt 5)/2$ the golden
ratio. For every natural number $k$,
$F_{2k+1} \varphi = F_{2k+2} + \left((\sqrt 5 - 1)/2\right)^{2k+1}$ and
$F_{2k+1} (1 + \varphi) = F_{2k+3} + \left((\sqrt 5 - 1)/2\right)^{2k+1}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 1. -/
theorem_wanted fib_odd_mul_goldenRatio (k : ℕ) :
    (Nat.fib (2 * k + 1) : ℝ) * Real.goldenRatio =
        Nat.fib (2 * k + 2) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) ∧
      (Nat.fib (2 * k + 1) : ℝ) * (1 + Real.goldenRatio) =
        Nat.fib (2 * k + 3) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1)

/-- **Numeration by odd-indexed Fibonacci numbers.** Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$). For every positive integer $t$ there are a
natural number $n$ and natural numbers $a_0, a_1, a_2, \dots$ such that
$F_{2n+1} \le t < F_{2n+3}$, $t = \sum_{k=0}^{n} a_k F_{2k+1}$, $a_0 \le 1$, $a_k \le 2$ for
every $k \ge 1$, $a_1 = 2$ and $a_0 = 1$ do not both hold, and for no $k$ do $a_{k+1} = 2$ and
$a_k = 2$ both hold.

Here $a_k$ is the coefficient the paper calls $a_{2k+1}$; the last two conditions exclude the
digit patterns $2F_3 + F_1$ and $2F_{2k+3} + 2F_{2k+1}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 1. -/
theorem_wanted exists_odd_fib_representation {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), Nat.fib (2 * n + 1) ≤ t ∧ t < Nat.fib (2 * n + 3) ∧
      t = ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) ∧
      a 0 ≤ 1 ∧ (∀ k, 1 ≤ k → a k ≤ 2) ∧ ¬ (a 1 = 2 ∧ a 0 = 1) ∧
      ∀ k, ¬ (a (k + 1) = 2 ∧ a k = 2)

/-- **Odd Pell and even Pell–Lucas numbers times $1 + \sqrt 2$.** Let $P_n$ be the Pell numbers and
$H_n$ the Pell–Lucas numbers ($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). For every natural
number $k$, $P_{2k+1}(1 + \sqrt 2) = P_{2k+2} + (\sqrt 2 - 1)^{2k+1}$ and
$H_{2k}(1 + \sqrt 2) = H_{2k+1} + \sqrt 2\,(\sqrt 2 - 1)^{2k}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 2 (1), (2). -/
theorem_wanted pellNumber_odd_mul_one_add_sqrt_two (k : ℕ) :
    (pellNumber (2 * k + 1) : ℝ) * (1 + Real.sqrt 2) =
        pellNumber (2 * k + 2) + (Real.sqrt 2 - 1) ^ (2 * k + 1) ∧
      (pellLucasSequence (2 * k) : ℝ) * (1 + Real.sqrt 2) =
        pellLucasSequence (2 * k + 1) + Real.sqrt 2 * (Real.sqrt 2 - 1) ^ (2 * k)

/-- **Numeration by doubled Pell and half-companion Pell numbers.** Let $P_n$ be the Pell numbers
($P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$), and let $R_k = 2P_k$ for odd $k$ and
$R_k = H_k$ for even $k$. Then for every positive integer $t$ there are a natural number $n$ and
natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=0}^{n} a_k R_k$, $a_0 \le 1$, $a_0 = 0$ if $a_1 = 1$, $a_{2k} \le 3$ and
$a_{2k+1} \le 1$ for every $k \ge 0$, $a_{2k+2} < 3$ whenever $a_{2k} = 3$ ($k \ge 0$), and
$a_{2k-1} = a_{2k+1} = 0$ and $a_{2k-2} < 3$ whenever $a_{2k} = 3$ with $k \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 4. -/
theorem_wanted exists_two_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ range (n + 1), a k * R k ∧
      a 0 ≤ 1 ∧ (a 1 = 1 → a 0 = 0) ∧ (∀ k, a (2 * k) ≤ 3 ∧ a (2 * k + 1) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 1) = 0 ∧ a (2 * k + 1) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 2) < 3) ∧
      (∀ k, a (2 * k) = 3 → a (2 * k + 2) < 3)

/-- **Numeration by Pell and half-companion Pell numbers.** Let $P_n$ be the Pell numbers
($P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$), and let $R_k = P_k$ for odd $k$ and
$R_k = H_k$ for even $k$. Then for every positive integer $t$ there are a natural number $n \ge 1$
and natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=1}^{n} a_k R_k$, $a_1 \le 2$, $a_2 = 0$ if $a_1 = 2$, $a_{2k+1} \le 3$ and
$a_{2k} \le 1$ for every $k \ge 0$, and for every $k \ge 1$ with $a_{2k+1} = 3$ we have
$a_{2k} = a_{2k+2} = 0$, $a_{2k-1} < 3$ and $a_{2k+3} < 3$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 5. -/
theorem_wanted exists_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧ R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ Icc 1 n, a k * R k ∧
      a 1 ≤ 2 ∧ (a 1 = 2 → a 2 = 0) ∧ (∀ k, a (2 * k + 1) ≤ 3 ∧ a (2 * k) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k) = 0 ∧ a (2 * k + 2) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k - 1) < 3 ∧ a (2 * k + 3) < 3)

/-- **Bronze Lucas parameters.** The bronze Lucas parameters are the Lucas sequence parameters
$(P, Q) = (3, -1)$. The Lucas sequence $U(3, -1)$ is the sequence of bronze numbers $B_n$, with
$B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
def bronzeLucasParams : LucasSequenceParams where
  p := 3
  q := -1
  q_ne_zero := by decide

/-- **Recurrence of the bronze numbers.** Let $B_n$ be the bronze numbers, the terms of the Lucas
sequence $U(3, -1)$. For every natural number $n$, $B_{n+2} = 3B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_add_two (n : ℕ) :
    lucasU bronzeLucasParams (n + 2) =
      3 * lucasU bronzeLucasParams (n + 1) + lucasU bronzeLucasParams n := by
  simp [lucasU, bronzeLucasParams]

/-- **The first bronze numbers.** Let $B_n$ be the bronze numbers, the terms of the Lucas sequence
$U(3, -1)$. Then $B_0, B_1, B_2, B_3, B_4, B_5$ are $0, 1, 3, 10, 33, 109$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_values :
    (List.range 6).map (lucasU bronzeLucasParams) = [0, 1, 3, 10, 33, 109] := by
  decide

/-- **Companion bronze numbers of the first type.** Let $B_n$ denote the bronze numbers, the
Lucas sequence $U(3, -1)$: $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$. For every
natural number $n$, the $n$-th companion bronze number of the first type is the integer
$C_n = B_{n+1} - 2B_n$.

Thus $C_0 = C_1 = 1$, $C_{n+2} = 3C_{n+1} + C_n$, and $C_n = B_n + B_{n-1}$ for $n \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the first type). -/
def bronzeCompanionFirst (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - 2 * lucasU bronzeLucasParams n

/-- **Companion bronze numbers of the second type.** Let $B_n$ denote the bronze numbers, the
Lucas sequence $U(3, -1)$: $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$. For every
natural number $n$, the $n$-th companion bronze number of the second type is the integer
$D_n = B_{n+1} - B_n$.

Thus $D_0 = 1$, $D_1 = 2$, $D_{n+2} = 3D_{n+1} + D_n$, and $D_n = 2B_n + B_{n-1}$ for $n \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the second type). -/
def bronzeCompanionSecond (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - lucasU bronzeLucasParams n

/-- **Recurrence for the companion bronze numbers of the first type.** For every natural number
$n$, the companion bronze numbers $C_n$ of the first type satisfy $C_{n+2} = 3C_{n+1} + C_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionFirst_add_two (n : ℕ) :
    bronzeCompanionFirst (n + 2) = 3 * bronzeCompanionFirst (n + 1) + bronzeCompanionFirst n := by
  simp only [bronzeCompanionFirst, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Recurrence for the companion bronze numbers of the second type.** For every natural number
$n$, the companion bronze numbers $D_n$ of the second type satisfy $D_{n+2} = 3D_{n+1} + D_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionSecond_add_two (n : ℕ) :
    bronzeCompanionSecond (n + 2) = 3 * bronzeCompanionSecond (n + 1) + bronzeCompanionSecond n := by
  simp only [bronzeCompanionSecond, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Initial companion bronze numbers.** The companion bronze numbers $C_n$ of the first type
satisfy $(C_0, C_1, C_2, C_3, C_4) = (1, 1, 4, 13, 43)$, and the companion bronze numbers $D_n$
of the second type satisfy $(D_0, D_1, D_2, D_3, D_4) = (1, 2, 7, 23, 76)$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanion_values :
    (List.range 5).map bronzeCompanionFirst = [1, 1, 4, 13, 43] ∧
      (List.range 5).map bronzeCompanionSecond = [1, 2, 7, 23, 76] := by
  decide

/-- **Moves of the Beatty octal game.** Let $\alpha$ and $\beta$ be real numbers. In the Beatty
octal game for $\alpha$ and $\beta$, a move takes a heap of $n$ tokens to a heap of $m$ tokens
exactly when one of the following holds: $n \ge 1$, $n = \lfloor k\alpha \rfloor$ for some
integer $k \ge 1$, and $m = 0$ (the whole heap is removed); or $m = n - i$ for some natural
number $i$ with $1 \le i < n$ and $i = \lfloor k\beta \rfloor$ for some integer $k \ge 1$
(removing $i$ tokens leaves a nonempty heap).

When $\alpha$ and $\beta$ are complementary, so that every $i \ge 1$ lies in exactly one of the
Beatty sequences $\{\lfloor k\alpha \rfloor : k \ge 1\}$ and
$\{\lfloor k\beta \rfloor : k \ge 1\}$, this is the octal game with code
$0{\cdot}d_1 d_2 d_3 \ldots$, where $d_i = 1$ if $i$ lies in the first sequence and $d_i = 2$ if
$i$ lies in the second.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1 (octal codes) and
the codes of the gold, silver and bronze games in Sections 2, 3, 4. -/
def beattyOctalMove (α β : ℝ) (n m : ℕ) : Prop :=
  (0 < n ∧ (∃ k : ℤ, 0 < k ∧ beattySeq α k = n) ∧ m = 0) ∨
    ∃ i : ℕ, (∃ k : ℤ, 0 < k ∧ beattySeq β k = i) ∧ 0 < i ∧ i < n ∧ m = n - i

/-- **Moves of a Beatty octal game decrease the heap.** For all real numbers $\alpha$, $\beta$
and all natural numbers $n$, $m$: if a move of the Beatty octal game for $\alpha$ and $\beta$
takes a heap of $n$ tokens to a heap of $m$ tokens, then $m < n$.

Consequently every play of the game terminates.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1. -/
theorem beattyOctalMove_lt {α β : ℝ} {n m : ℕ} (h : beattyOctalMove α β n m) : m < n := by
  rcases h with ⟨hn, -, rfl⟩ | ⟨i, -, hi, hin, rfl⟩ <;> omega

/-- **Floor of greedy odd-Fibonacci sums times $\varphi$ and $1 + \varphi$.** Let $F_n$ be the
Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and
$\varphi = (1 + \sqrt 5)/2$ the golden ratio. Let $n$ be a natural number and $a_0, a_1, \dots$
natural numbers such that $\sum_{k=0}^{m-1} a_k F_{2k+1} < F_{2m+1}$ for every $m \le n + 1$, and
let $t = \sum_{k=0}^{n} a_k F_{2k+1}$. Then
$\lfloor t \varphi \rfloor = \sum_{k=0}^{n} a_k F_{2k+2}$ and
$\lfloor t (1 + \varphi) \rfloor = \sum_{k=0}^{n} a_k F_{2k+3}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 1
(here $a_k$ is the paper's $a_{2k+1}$); $n$ need not be minimal and $t = 0$ is allowed.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 2. -/
theorem_wanted floor_greedy_odd_fib_sum_mul_goldenRatio (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * Nat.fib (2 * k + 1) < Nat.fib (2 * m + 1)) :
    ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * Real.goldenRatio⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 2) ∧
      ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * (1 + Real.goldenRatio)⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 3)

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

/-- **Metallic identities for the bronze numbers.** Let $\alpha = (3 + \sqrt{13})/2$,
$\beta = (5 + \sqrt{13})/6$ and $\gamma = (\sqrt{13} - 3)/2$, let $B_n$ be the bronze numbers,
and let $C_n$ and $D_n$ be the companion bronze numbers of the first and second type. For every
natural number $k$, the following hold in $\mathbb{R}$:
(1) $B_{2k+1}\alpha = B_{2k+2} + \gamma^{2k+1}$;
(2) $C_{2k}\alpha = C_{2k+1} + \frac{13 + \sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(3) $D_{2k}\alpha = D_{2k+1} + \frac{13 - \sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(4) $3B_{2k+1}\beta = C_{2k+2} + \frac{13 - 3\sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(5) $(B_{2k+1} + C_{2k+2})\beta = D_{2k+2} + \frac{65 - 17\sqrt{13}}{6\sqrt{13}}\gamma^{2k}$;
(6) $D_{2k}\beta = B_{2k+1} + \frac{13 - \sqrt{13}}{6\sqrt{13}}\gamma^{2k}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 3. -/
theorem_wanted bronze_mul_metallic_identities (k : ℕ) :
    let α : ℝ := (3 + Real.sqrt 13) / 2
    let β : ℝ := (5 + Real.sqrt 13) / 6
    let γ : ℝ := (Real.sqrt 13 - 3) / 2
    (lucasU bronzeLucasParams (2 * k + 1) : ℝ) * α =
        lucasU bronzeLucasParams (2 * k + 2) + γ ^ (2 * k + 1) ∧
      (bronzeCompanionFirst (2 * k) : ℝ) * α = bronzeCompanionFirst (2 * k + 1) +
        (13 + Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * α = bronzeCompanionSecond (2 * k + 1) +
        (13 - Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (3 * lucasU bronzeLucasParams (2 * k + 1) : ℝ) * β = bronzeCompanionFirst (2 * k + 2) +
        (13 - 3 * Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      ((lucasU bronzeLucasParams (2 * k + 1) + bronzeCompanionFirst (2 * k + 2) : ℤ) : ℝ) * β =
        bronzeCompanionSecond (2 * k + 2) +
          (65 - 17 * Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * β = lucasU bronzeLucasParams (2 * k + 1) +
        (13 - Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k)

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

/-- **Floor of greedy bronze sums times $(3 + \sqrt{13})/2$.** Let $B_n$ be the bronze numbers
($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ and $R'$ be the integer sequences with $R_{3m+1} = B_{2m+1}$,
$R_{3m+2} = C_{2m+2}$, $R_{3m} = D_{2m}$ and $R'_{3m+1} = D_{2m+1}$, $R'_{3m+2} = B_{2m+2}$,
$R'_{3m} = C_{2m+1}$ for all $m \ge 0$. Let $n$ be a natural number and $a_1, a_2, \dots$ natural
numbers such that $\sum_{k=1}^{m-1} a_k R_k < R_m$ for every $1 \le m \le n + 1$, and let
$t = \sum_{k=1}^{n} a_k R_k$. Then
$\lfloor t (3 + \sqrt{13})/2 \rfloor = \sum_{k=1}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 9;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (1). -/
theorem_wanted floor_greedy_bronze_companion_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1))
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, (a k : ℤ) * R k : ℤ) : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ =
      ∑ k ∈ Icc 1 n, (a k : ℤ) * R' (k + 1)

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

/-- **P-positions of the bronze game.** Let $\alpha = (3 + \sqrt{13})/2$ and
$\beta = (5 + \sqrt{13})/6$, let $B_n$ be the bronze numbers, and let $C_n$ and $D_n$ be the
companion bronze numbers of the first and second type. Let $P$ be the set of natural numbers
$x$ such that $x = 0$ or $x \in \{B_{2k+1}, C_{2k+2}, D_{2k+2}\}$ for some natural number $k$.
Then, in the Beatty octal game for $\alpha$ and $\beta$, no move takes a heap whose size lies
in $P$ to a heap whose size lies in $P$, and from every heap whose size is not in $P$ some move
leads to a heap whose size lies in $P$.

So $P$ is stable and absorbing for the moves of the game; since every move decreases the heap,
this determines $P$ as the set of P-positions, the heap sizes from which the previous player
wins: $0, B_1, C_2, D_2, B_3, C_4, D_4, \ldots$

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 11. -/
theorem_wanted bronzeGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔ x = 0 ∨ ∃ k, (x : ℤ) = lucasU bronzeLucasParams (2 * k + 1) ∨
      (x : ℤ) = bronzeCompanionFirst (2 * k + 2) ∨ (x : ℤ) = bronzeCompanionSecond (2 * k + 2)) :
    (∀ x y, x ∈ P →
        beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y → y ∉ P) ∧
      ∀ x, x ∉ P →
        ∃ y, beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y ∧ y ∈ P

end

end MetaMathlibExt
