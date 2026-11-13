/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# A congruence obstruction for `|x² - d y²| = z`

Lemma 1(a), first sentence, of Takashi Hirotsu, *General Pell's
Equations and Angle Bisectors between Planar Lines with Rational
Slopes*, INTEGERS 24 (2024), Article A111.

Squares are `0` or `1` modulo `4`, so for `d ≡ 1 (mod 4)` the value
`x² - d y²` is `0`, `1`, or `3` modulo `4`, and so is its negation.
-/

@[expose] public section

namespace MetaMathlibExt

/-- If `d ≡ 1 (mod 4)` and `z ≡ 2 (mod 4)`, then `|x² - d y²| = z`
has no integral solutions.

The source's `z > 1` is not needed. The second sentence of part (a)
(on `S(d)` and `l_2`) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle
Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24
(2024), Article A111, Lemma 1(a), first sentence
(`integers-2024-A111-lem-1`).
Proves `Wanted` entry `abs_sq_sub_mul_sq_ne_of_two_mod_four`. -/
theorem abs_sq_sub_mul_sq_ne_of_two_mod_four (d z : ℤ) (hd : d % 4 = 1)
    (hz : z % 4 = 2) (x y : ℤ) : |x ^ 2 - d * y ^ 2| ≠ z := by
  have hsq : ∀ t : ℤ, t ^ 2 % 4 = 0 ∨ t ^ 2 % 4 = 1 := by
    intro t
    rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3)
        with ht | ht | ht | ht <;>
      simp [pow_two, Int.mul_emod, ht]
  have hdy : d * y ^ 2 % 4 = y ^ 2 % 4 := by
    rw [Int.mul_emod, hd, one_mul, Int.emod_emod_of_dvd _ (dvd_refl 4)]
  rcases abs_cases (x ^ 2 - d * y ^ 2) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rcases hsq x with hx | hx <;> rcases hsq y with hy | hy <;> omega

end MetaMathlibExt
