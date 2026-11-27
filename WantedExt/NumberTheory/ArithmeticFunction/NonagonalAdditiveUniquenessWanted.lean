/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniqueness
public import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveFivePow
public import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveThreePow
public import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveSevenPow

/-!
# Additive uniqueness of generalized nonagonal numbers (statements)

Statements from Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99. The generalized nonagonal numbers
are the values `m (7m - 5) / 2` for `m ∈ ℤ` (`0, 1, 6, 9, 19, 24, 39, …`, OEIS A118277),
written below without division as `2a = m (7m - 5)`. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.

Lemma 1 and Theorems 2-5 are the steps of the paper's induction proof of Theorem 1 and are stated
under Theorem 1's hypotheses (the paper's standing assumption, Section 2); each also follows from
Theorem 1 itself. Theorem 2 (`multiplicative_nonagonal_additive_three_pow`) is in
`MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveThreePow`.
Theorem 3 (`multiplicative_nonagonal_additive_five_pow`) is in
`MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveFivePow`.
Theorem 4 (`multiplicative_nonagonal_additive_seven_pow`) is proved in
`MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveSevenPow`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- **Nonagonal additive uniqueness: the step at powers of 2.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Let $r$ be a natural number. If $f(n) = n$
for every natural number $n < 2^r$, then $f(2^r) = 2^r$.

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
