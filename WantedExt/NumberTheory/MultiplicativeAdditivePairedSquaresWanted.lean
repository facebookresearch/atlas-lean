/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

@[expose] public section

/-! # Multiplicative functions additive on partitions of `2k` nonzero squares

Statements from Mahajan's paper. Equation (1) of the paper is
`f(∑_{i=1}^{2k} x_i²) = ∑_{j=1}^{k} f(x_{2j-1}² + x_{2j}²)` for all positive integers
`x_1, …, x_{2k}`; it is written here with the pairs `(x_{2j-1}, x_{2j})` relabelled as
`(x j, y j)` for `j : Fin k`. Equation (2) is `k`-additivity on
`E₂ = {a² + b² : a, b ≥ 1}`. A multiplicative function `ℕ → ℂ` is an
`ArithmeticFunction ℂ` with `IsMultiplicative`; its value at `0` plays no role.
-/

open ArithmeticFunction

/-- Dubouis: for `m ≥ 4`, a positive integer `n` is a sum of `m` nonzero squares if and only
if `n` is not in the exceptional set: `{1, 3, 5, 9, 11, 17, 29, 41} ∪ {2·4^r, 6·4^r, 14·4^r}`
for `m = 4`; `{1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33}` for `m = 5`; and
`{1, …, m - 1} ∪ {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13}` for `m ≥ 6`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 1 (`integers-2026-A121-lem-1`), quoting
Dubouis (1911). -/
public theorem_wanted sum_nonzero_squares_iff_not_mem_exceptional (m n : ℕ) (hm : 4 ≤ m)
    (hn : 0 < n) :
    (∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ↔
      n ∉ (if m = 4 then
            ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
              {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r}
          else if m = 5 then ({1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33} : Set ℕ)
          else Set.Ico 1 m ∪
            {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13})

/-- Every integer `n ≥ 20` is a sum of `6` nonzero squares, and every integer `n ≥ 22` is a
sum of `8` nonzero squares.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Corollary 1, as extracted inside the Lemma 1
record (`integers-2026-A121-lem-1`). -/
public theorem_wanted sum_six_and_eight_nonzero_squares :
    (∀ n : ℕ, 20 ≤ n → ∃ a : Fin 6 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ∧
      ∀ n : ℕ, 22 ≤ n → ∃ a : Fin 8 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n

/-- If `f` is multiplicative, `3`-additive on `E₂ = {a² + b² : a, b ≥ 1}` (Equation (2) with
`k = 3`) and `f(2) ≠ 0`, then `f(2) = 2`, `f(3) = 3` and `f(5) = 5`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 2 (`integers-2026-A121-lem-2`). -/
public theorem_wanted multiplicative_three_additive_two_squares_base (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ A : Fin 3 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
      f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) :
    f 2 = 2 ∧ f 3 = 3 ∧ f 5 = 5

/-- If `f` is multiplicative, `4`-additive on `E₂ = {a² + b² : a, b ≥ 1}` (Equation (2) with
`k = 4`) and `f(2) ≠ 0`, then `f(n) = n` for every `n ∈ {2, 3, 4, 5, 6, 7, 8, 10}`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 3 (`integers-2026-A121-lem-3`). -/
public theorem_wanted multiplicative_four_additive_two_squares_base (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ A : Fin 4 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
      f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) :
    ∀ n ∈ ({2, 3, 4, 5, 6, 7, 8, 10} : Finset ℕ), f n = n

/-- If `f` is multiplicative, satisfies Equation (1) with `k ∈ {3, 4}` and `f(2) ≠ 0`, then
`f(n) = n` for all positive integers `n`. The record's following sentence about `k ≥ 5` is
the separate Theorem 2.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 1 (`integers-2026-A121-thm-1`). -/
public theorem_wanted multiplicative_additive_paired_squares_eq_id_of_three_or_four
    (k : ℕ) (hk : k = 3 ∨ k = 4) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n

/-- Let `k ≥ 5` and let `f` be multiplicative satisfying Equation (1). Then either `f(n) = n`
for all positive integers `n`, or `f` vanishes on
`{a² + b² : a, b ≥ 1} ∪ {2k + t : t ∈ {0, 3, 6, 8, 9, 11, 12}} ∪ {n : n ≥ 2k + 14}`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 2 (`integers-2026-A121-thm-2`). -/
public theorem_wanted multiplicative_additive_paired_squares_dichotomy
    (k : ℕ) (hk : 5 ≤ k) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2)) :
    (∀ n : ℕ, 0 < n → f n = n) ∨
      ∀ n : ℕ, ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2) ∨
          (∃ t ∈ ({0, 3, 6, 8, 9, 11, 12} : Finset ℕ), n = 2 * k + t) ∨ 2 * k + 14 ≤ n) →
        f n = 0

/-- Let `k ≥ 5` and let `f` be multiplicative satisfying Equation (1). If `f(β) ≠ 0` for
some `β ∈ {a² + b² : a, b ≥ 1} ∪ {2k + t : t ∈ {0, 3, 6, 8, 9, 11, 12}} ∪ {n : n ≥ 2k + 14}`,
then `f(n) = n` for all positive integers `n`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Corollary 2 (`integers-2026-A121-cor-2`). -/
public theorem_wanted multiplicative_additive_paired_squares_eq_id_of_ne_zero
    (k : ℕ) (hk : 5 ≤ k) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (β : ℕ) (hβ : (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ β = a ^ 2 + b ^ 2) ∨
      (∃ t ∈ ({0, 3, 6, 8, 9, 11, 12} : Finset ℕ), β = 2 * k + t) ∨ 2 * k + 14 ≤ β)
    (hfβ : f β ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n

/-- If `f` is multiplicative, satisfies Equation (1) with `k = 3` and `f(2) ≠ 0`, then
`f(n) = n` for all positive integers `n`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 3 (`integers-2026-A121-thm-3`). -/
public theorem_wanted multiplicative_additive_six_squares_eq_id (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n

/-- If `f` is multiplicative, satisfies Equation (1) with `k = 4` and `f(2) ≠ 0`, then
`f(n) = n` for all positive integers `n`.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 4 (`integers-2026-A121-thm-4`). -/
public theorem_wanted multiplicative_additive_eight_squares_eq_id (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 4 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n

end

end MetaMathlibExt
