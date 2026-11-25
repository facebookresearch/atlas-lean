/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-!
# GCDs of the factors of a sum or difference of cubes

In the factorizations of `x ^ 3 - 1` and `x ^ 3 + 1`, the quadratic factor differs
from `3` by an integer multiple of the linear factor.
-/

public section

namespace MetaMathlibExt

/-- **The gcd of $x \mp 1$ and $x^2 \pm x + 1$.** For every integer $x$,
$\gcd(x - 1, x^2 + x + 1) = \gcd(x - 1, 3)$ and $\gcd(x + 1, x^2 - x + 1) = \gcd(x + 1, 3)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 4
(`integers-2025-A103-lem-4`). -/
theorem gcd_sub_one_sq_add_add_one (x : ℤ) :
    Int.gcd (x - 1) (x ^ 2 + x + 1) = Int.gcd (x - 1) 3 ∧
      Int.gcd (x + 1) (x ^ 2 - x + 1) = Int.gcd (x + 1) 3 := by
  constructor
  · rw [show x ^ 2 + x + 1 = (x - 1) * (x + 2) + 3 by ring, Int.gcd_mul_left_add_right]
  · rw [show x ^ 2 - x + 1 = (x + 1) * (x - 2) + 3 by ring, Int.gcd_mul_left_add_right]

end MetaMathlibExt
