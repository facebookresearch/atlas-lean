/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Multiplicative functions additive on squares and on sums of consecutive squares

Statements from Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive
Squares for Multiplicative Functions*, INTEGERS 25 (2025), Article A40. Multiplicative
functions are `ArithmeticFunction ℂ` with `IsMultiplicative` (which includes `f 1 = 1`).
The paper's set `T = {s_m - s_n : m > n ≥ 0}` with `s_n = ∑_{i=0}^{n} i²` is written as
the sums `∑ j ∈ Finset.Ioc n m, j ^ 2` with `n < m`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- A multiplicative function additive on pairs of positive squares satisfies
`f 4 ∈ {0, 4}`, `f (q ^ (2k)) = f (q ^ 2) ^ k` for all positive `q, k`, and, when
`f 4 = 4`, `f (m ^ 2) = m ^ 2` for every positive `m`. The paper's hypothesis `f ≠ 0`
is implied by `IsMultiplicative`.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 1
(`integers-2025-A40-thm-1`). -/
public theorem_wanted multiplicative_additive_on_squares (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ m n : ℕ, 0 < m → 0 < n → f (m ^ 2 + n ^ 2) = f (m ^ 2) + f (n ^ 2)) :
    (f 4 = 0 ∨ f 4 = 4) ∧
      (∀ q k : ℕ, 0 < q → 0 < k → f (q ^ (2 * k)) = f (q ^ 2) ^ k) ∧
      (f 4 = 4 → ∀ m : ℕ, 0 < m → f (m ^ 2) = (m : ℂ) ^ 2)

/-- For every `k ≥ 2`, the set of finite sums of consecutive squares is a `k`-additive
uniqueness set for multiplicative functions: a multiplicative `f` with
`f (x₁ + ⋯ + x_k) = f x₁ + ⋯ + f x_k` for all `x₁, …, x_k` in that set is the identity.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 2
(`integers-2025-A40-thm-2`). -/
public theorem_wanted consecutiveSquareSums_kAdditiveUniqueness (k : ℕ) (hk : 2 ≤ k)
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x : Fin k → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) :
    ∀ n : ℕ, f n = n

end

end MetaMathlibExt
