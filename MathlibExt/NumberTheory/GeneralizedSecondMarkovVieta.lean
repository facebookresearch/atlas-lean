/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Vieta jumping for the second generalized Markov equation

Both Vieta jumps preserve the second generalized Markov equation over the integers.
-/

namespace MetaMathlibExt

/-- **Vieta jumping for the second generalized Markov equation.** Let $k$ be a natural number
and let $a, b, c$ be integers with

$$a^2 + b^2 + c^2 + (k^2 + 2k)(a + b + c) + 2k^3 + 3k^2 = abc.$$

Then the triples $(a, ab - c - k^2 - 2k, b)$ and $(b, bc - a - k^2 - 2k, c)$ satisfy the same
equation.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.6. -/
public theorem genSecondMarkov_vieta (k : ℕ) {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c) :
    (let c' := a * b - c - (k : ℤ) ^ 2 - 2 * k;
      a ^ 2 + c' ^ 2 + b ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + c' + b) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = a * c' * b) ∧
    (let a' := b * c - a - (k : ℤ) ^ 2 - 2 * k;
      b ^ 2 + a' ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (b + a' + c) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = b * a' * c) := by
  constructor <;> linear_combination h

end MetaMathlibExt
