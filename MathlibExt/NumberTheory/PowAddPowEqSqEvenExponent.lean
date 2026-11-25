/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Evenness of the first exponent in `n^x + (5p)^y = z^2`

When `y > 0` and `n` is congruent to `2` or `3` modulo five, `even_of_pos_exp` shows that
`x` is even. Squaring the equation modulo five gives `z^4 = (-1)^x`.
-/

public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- The congruence argument works for every natural number `p`.
set_option linter.unusedVariables false in
/-- **Evenness of $x$ in $n^x + (5p)^y = z^2$ when $n \equiv 2, 3 \pmod 5$.** Let $p$ be a prime
and $n$ a natural number with $n \equiv 2 \pmod 5$ or $n \equiv 3 \pmod 5$. If natural numbers
$x$, $y$, $z$ with $y > 0$ satisfy $n^x + (5p)^y = z^2$, then $x$ is even.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 2. -/
theorem even_of_pos_exp (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 5 = 2 ∨ n % 5 = 3) (hy : 0 < y)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    Even x := by
  refine (Nat.even_or_odd x).resolve_right fun hx => ?_
  have hn₂ : (n : ZMod 5) ^ 2 = -1 := by
    rw [← ZMod.natCast_mod n 5]
    rcases hn with hn | hn <;> rw [hn] <;> decide
  have heq : (n : ZMod 5) ^ x = (z : ZMod 5) ^ 2 := by
    simpa [show (5 : ZMod 5) = 0 by decide, hy.ne'] using congrArg (Nat.cast : ℕ → ZMod 5) h
  have hz : ((z : ZMod 5) ^ 2) ^ 2 = -1 := calc
    _ = ((n : ZMod 5) ^ 2) ^ x := by rw [← heq, pow_right_comm]
    _ = -1 := by rw [hn₂, hx.neg_one_pow]
  exact (by decide : ∀ a : ZMod 5, (a ^ 2) ^ 2 ≠ -1) z hz

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
