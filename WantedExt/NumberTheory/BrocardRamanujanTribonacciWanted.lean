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
The backward extension has `T₋₁₀ = 5`. This value explains why Theorem 1
must remain natural-indexed: `4! + 1 = 5²` would be a two-sided counterexample.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1 normalization note.
-/
public theorem tribonacciInt_neg_ten : tribonacciInt (-10) = 5 := by
  rfl

/--
Theorem 1: no natural-indexed Tribonacci square is one more than a factorial.
Formally, `m` is the factorial parameter and `n` witnesses that the square root
is `tribonacci n`. This deliberately excludes negative indices because
`tribonacciInt (-10) = 5` and `4! + 1 = 5²`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1.
-/
public theorem_wanted brocardRamanujan_not_tribonacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tribonacci n ^ 2

/--
Theorem 2: no natural-indexed Tetranacci square is one more than a factorial.
Formally, `m` is the factorial parameter and `n` witnesses that the square root
is `tetranacci n`. As in the paper, only nonnegative sequence indices occur.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 2.
-/
public theorem_wanted brocardRamanujan_not_tetranacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tetranacci n ^ 2

/--
Proposition 1 at `p = 47`. The first conjunct says that the terms at
`j ∈ {1, 2, -2, -3, -7}` are `±1`. The second gives
`ν₄₇(T_{46r+j} - T_j) = 1 + ν₄₇(r)` at those indices. It excludes `r = 0`
because Mathlib defines `padicValInt 47 0 = 0`, whereas the paper uses an
infinite valuation there. The third conjunct translates valuation zero for
all other indices into nondivisibility of both `T_n - 1` and `T_n + 1` by 47.
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
