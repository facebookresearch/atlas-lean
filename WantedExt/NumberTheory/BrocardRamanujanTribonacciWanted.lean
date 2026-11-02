/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.TribonacciInt
public import MathlibExt.NumberTheory.TetranacciSequence
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

namespace MetaMathlibExt

@[expose] public section

/--
**The Tribonacci number of index $-10$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence, determined by $T_0 = 0$, $T_1 = T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for all integers $n$. Then $T_{-10} = 5$.

Since $4! + 1 = 5^2$, the equation $m! + 1 = T_n^2$ has a solution once negative indices $n$ are
allowed.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1 normalization note.
-/
public theorem tribonacciInt_neg_ten : tribonacciInt (-10) = 5 := by
  rfl

/--
**The Brocard–Ramanujan equation has no Tribonacci solutions.** Let $(T_n)_{n \ge 0}$ be the
Tribonacci sequence, given by $T_0 = T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$
for $n \ge 0$. For all natural numbers $m$ and $n$, $m! + 1 \ne T_n^2$.

Only nonnegative indices are allowed: the extension of the Tribonacci sequence to negative indices
by the same recurrence takes the value $5$, and $4! + 1 = 5^2$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1.
-/
public theorem_wanted brocardRamanujan_not_tribonacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tribonacci n ^ 2

/--
**The Brocard–Ramanujan equation has no Tetranacci solutions.** Let $(Q_n)_{n \ge 0}$ be the
Tetranacci sequence, given by $Q_0 = Q_1 = Q_2 = 0$, $Q_3 = 1$ and
$Q_{n+4} = Q_{n+3} + Q_{n+2} + Q_{n+1} + Q_n$ for $n \ge 0$. For all natural numbers $m$ and $n$,
$m! + 1 \ne Q_n^2$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 2.
-/
public theorem_wanted brocardRamanujan_not_tetranacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tetranacci n ^ 2

/--
**The $47$-adic valuation of Tribonacci numbers near $\pm 1$.** Let $(T_n)_{n \in \mathbb{Z}}$
be the two-sided Tribonacci sequence, determined by $T_0 = 0$, $T_1 = T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for all integers $n$. Let $\nu_{47}$ be the $47$-adic
valuation on the integers, with the convention $\nu_{47}(0) = 0$, and let
$J = \{1, 2, -2, -3, -7\}$. First, $T_j = 1$ or $T_j = -1$ for every $j \in J$. Second, for every
$j \in J$ and every nonzero integer $r$, $\nu_{47}(T_{46r+j} - T_j) = 1 + \nu_{47}(r)$. Third, for
every integer $n$ that is not of the form $46r + j$ with $j \in J$ and $r \in \mathbb{Z}$, neither
$T_n - 1$ nor $T_n + 1$ is divisible by $47$.

The condition $r \ne 0$ is needed because $\nu_{47}(0)$ is $0$ here, whereas the paper uses an
infinite valuation at $0$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem_wanted tribonacci_padicValInt_fortySeven :
    (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ),
      tribonacciInt j = 1 ∨ tribonacciInt j = -1) ∧
    (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ), ∀ r : ℤ, r ≠ 0 →
      padicValInt 47 (tribonacciInt (46 * r + j) - tribonacciInt j) =
        1 + padicValInt 47 r) ∧
    (∀ n : ℤ,
      (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ), ∀ r : ℤ, n ≠ 46 * r + j) →
        ¬ (47 : ℤ) ∣ tribonacciInt n - 1 ∧ ¬ (47 : ℤ) ∣ tribonacciInt n + 1)

end

end MetaMathlibExt
