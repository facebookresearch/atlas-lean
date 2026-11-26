/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniqueness

/-!
# Nonagonal additive uniqueness: the step at powers of 3

Theorem 2 of Poo-Sung Park's *On the Additive Uniqueness of Generalized Nonagonal Numbers
for Multiplicative Functions* (INTEGERS 25 (2025), Article A99), as a corollary of the
proved identity theorem.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Nonagonal additive uniqueness: the step at powers of 3.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Let $r$ be a natural number and put
$\alpha(x) = \frac{14}{17} \cdot \frac{2}{3} x - \frac{12}{17}$. If $f(n) = n$ for every natural
number $n < \alpha(3^r)$, then $f(3^r) = 3^r$.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 2
(`integers-2025-A99-thm-2`). -/
public theorem multiplicative_nonagonal_additive_three_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, (n : ℝ) < 14 / 17 * (2 / 3) * (3 : ℝ) ^ r - 12 / 17 → f n = n) :
    f (3 ^ r) = (3 ^ r : ℕ) := by
  have _ := hind
  exact multiplicative_nonagonal_additive_eq_id f hf hadd _

end MetaMathlibExt
