/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq

/-!
# Opposite parity of the exponents in `n^x + (5p)^y = z^2`

Both bases are congruent to `-1` modulo four. If the exponents have the same parity,
the powers are both `1` or both `-1` modulo four. In either case their sum is `2`
modulo four, whereas a square is `0` or `1`.
-/

public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- The statement retains primality although the residue of `p` suffices.
set_option linter.unusedVariables false in
/-- **Opposite parity of the exponents in $n^x + (5p)^y = z^2$ when $n \equiv p \equiv 3 \pmod 4$.**
Let $p$ be a prime and $n$ a natural number with $n \equiv 3 \pmod 4$ and $p \equiv 3 \pmod 4$.
If natural numbers $x$, $y$, $z$ satisfy $n^x + (5p)^y = z^2$, then $x$ and $y$ have opposite
parity.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 3. -/
theorem opposite_parity (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 4 = 3) (hp4 : p % 4 = 3)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    x % 2 ≠ y % 2 := by
  intro hxy
  have hn' : (n : ℤ) ≡ -1 [ZMOD 4] := by unfold Int.ModEq; omega
  have hp' : 5 * (p : ℤ) ≡ -1 [ZMOD 4] := by unfold Int.ModEq; omega
  have hz : (n : ℤ) ^ x + (5 * (p : ℤ)) ^ y = (z : ℤ) ^ 2 := by exact_mod_cast h
  have hmod := ((hn'.pow x).add (hp'.pow y)).eq
  rw [hz, Int.sq_emod_four, neg_one_pow_eq_pow_mod_two x, neg_one_pow_eq_pow_mod_two y,
    hxy] at hmod
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hy] at hmod <;> omega

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
