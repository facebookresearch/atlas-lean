/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The exponential Diophantine equation `19^x + 151^y = z^2`

Corollary 1 of Shalini Choudhury and Naba Kanta Sarma,
"On the Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", *INTEGERS* 26 (2026), Article A87
(<https://math.colgate.edu/~integers/vol26.html>).

The left side is always `2` modulo `3`, which no square is.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Corollary 1**: the exponential Diophantine
equation `19^x + 151^y = z^2` has no solution.

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", Corollary 1.
Proves `Wanted` entry `pow19_add_pow151_ne_sq`. -/
theorem pow19_add_pow151_ne_sq (x y z : ℕ) :
    19 ^ x + 151 ^ y ≠ z ^ 2 := by
  intro h
  have h19 : 19 ^ x % 3 = 1 := by simp [Nat.pow_mod]
  have h151 : 151 ^ y % 3 = 1 := by simp [Nat.pow_mod]
  have hz : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
    rcases (by omega : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2) with hr | hr | hr <;>
      simp [Nat.pow_mod, hr]
  omega

end MetaMathlibExt
