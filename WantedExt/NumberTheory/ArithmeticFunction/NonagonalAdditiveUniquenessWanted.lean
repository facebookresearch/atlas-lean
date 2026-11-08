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
# Additive uniqueness of generalized nonagonal numbers (statements)

Statements from Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99. The generalized nonagonal numbers
are the values `m (7m - 5) / 2` for `m ∈ ℤ` (`0, 1, 6, 9, 19, 24, 39, …`, OEIS A118277),
written below without division as `2a = m (7m - 5)`. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.

Lemma 1 and Theorems 2-5 are the steps of the paper's induction proof of Theorem 1 and are stated
under Theorem 1's hypotheses (the paper's standing assumption, Section 2); each also follows from
Theorem 1 itself.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- A multiplicative function `f` with `f (a + b) = f a + f b` for all nonzero generalized
nonagonal numbers `a` and `b` is the identity.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 1
(`integers-2025-A99-thm-1`). -/
public theorem_wanted multiplicative_nonagonal_additive_eq_id
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) :
    ∀ n : ℕ, f n = n

/-- Lemma 1: under the hypotheses of Theorem 1 (`f` multiplicative and additive on nonzero
generalized nonagonal numbers), `f n = n` for `1 ≤ n ≤ 11`.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Lemma 1
(`integers-2025-A99-lem-1`). -/
public theorem_wanted multiplicative_nonagonal_additive_eq_self_of_le_eleven
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 11 → f n = n

/-- Theorem 2 (the step for powers of `3`): under the hypotheses of Theorem 1, with
`α(x) = (14/17)(2/3)x - 12/17`, if `f n = n` for every `n < α(3^r)`, then `f (3^r) = 3^r`.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 2
(`integers-2025-A99-thm-2`). -/
public theorem_wanted multiplicative_nonagonal_additive_three_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, (n : ℝ) < 14 / 17 * (2 / 3) * (3 : ℝ) ^ r - 12 / 17 → f n = n) :
    f (3 ^ r) = (3 ^ r : ℕ)

/-- Theorem 3 (the step for powers of `5`): under the hypotheses of Theorem 1, with
`β(x) = x/4`, if `r ≥ 3` and `f n = n` for every `n ≤ β(5^r)`, then `f (5^r) = 5^r`.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 3
(`integers-2025-A99-thm-3`). -/
public theorem_wanted multiplicative_nonagonal_additive_five_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) {r : ℕ} (hr : 3 ≤ r)
    (hind : ∀ n : ℕ, (n : ℝ) ≤ (5 : ℝ) ^ r / 4 → f n = n) :
    f (5 ^ r) = (5 ^ r : ℕ)

/-- Theorem 4 (the step for powers of `7`): under the hypotheses of Theorem 1, if `f n = n` for
every `n < 7^r`, then `f (7^r) = 7^r`.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 4
(`integers-2025-A99-thm-4`). -/
public theorem_wanted multiplicative_nonagonal_additive_seven_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, n < 7 ^ r → f n = n) :
    f (7 ^ r) = (7 ^ r : ℕ)

/-- Theorem 5 (the step for powers of `2`): under the hypotheses of Theorem 1, if `f n = n` for
every `n < 2^r`, then `f (2^r) = 2^r`.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 5
(`integers-2025-A99-thm-5`). -/
public theorem_wanted multiplicative_nonagonal_additive_two_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, n < 2 ^ r → f n = n) :
    f (2 ^ r) = (2 ^ r : ℕ)

end

end MetaMathlibExt
