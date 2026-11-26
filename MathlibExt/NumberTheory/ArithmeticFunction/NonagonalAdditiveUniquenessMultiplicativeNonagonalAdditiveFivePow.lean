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
# Nonagonal additive uniqueness: the step at powers of 5

A complex-valued multiplicative arithmetic function additive on pairs of positive generalized
nonagonal numbers fixes `5 ^ r` for `3 ≤ r` when it fixes every `n ≤ 5 ^ r / 4`, as a
consequence of the general identity theorem.

Statements from Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99. The generalized nonagonal numbers
are the values `m (7m - 5) / 2` for `m ∈ ℤ` (`0, 1, 6, 9, 19, 24, 39, …`, OEIS A118277),
written below without division as `2a = m (7m - 5)`. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

set_option linter.unusedVariables false in
/-- **Nonagonal additive uniqueness: the step at powers of 5.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Let $r \ge 3$ be a natural number and put
$\beta(x) = x/4$. If $f(n) = n$ for every natural number $n \le \beta(5^r)$, then $f(5^r) = 5^r$.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 3
(`integers-2025-A99-thm-3`). -/
public theorem multiplicative_nonagonal_additive_five_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) {r : ℕ} (hr : 3 ≤ r)
    (hind : ∀ n : ℕ, (n : ℝ) ≤ (5 : ℝ) ^ r / 4 → f n = n) :
    f (5 ^ r) = (5 ^ r : ℕ) :=
  multiplicative_nonagonal_additive_eq_id f hf hadd _

end MetaMathlibExt
