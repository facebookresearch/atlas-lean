/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The margin $q + 1 - 2\sqrt q > 12$ for $q \ge 23$

For every real number $q \ge 23$, $q + 1 - 2\sqrt q - 12 > 0$. This is the final inequality of the
proof of Lemma 2.3 of B. Poonen, "Characterizing integers among rational numbers with a
universal-existential formula", Amer. J. Math. 131 (2009), 675–682, where the Hasse bound
$\#X(\mathbb{F}_q) \ge (q + 1 - 2\sqrt q) - 12$ is shown to be positive.
-/

set_option autoImplicit false

@[expose] public section

namespace Real

/-- **The margin $q + 1 - 2\sqrt q > 12$ for real $q \ge 23$.** For every real number $q \ge 23$,
$q + 1 - 2\sqrt q - 12 > 0$.

The proof: $q + 1 - 2\sqrt q = (\sqrt q - 1)^2$ and $\sqrt q - 1 \ge \sqrt{23} - 1 > 3.7$, so
$(\sqrt q - 1)^2 > 13.69 > 12$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, p. 3 of the author's version with
the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "For any
$q \ge 23$, the Hasse bound yields $\#X(\mathbb{F}_q) \ge (q + 1 - 2\sqrt q) - 12 > 0$". -/
theorem add_one_sub_two_mul_sqrt_sub_twelve_pos {q : ℝ} (hq : 23 ≤ q) :
    0 < q + 1 - 2 * √q - 12 := by
  have hq0 : 0 ≤ q := by linarith
  have hs : (√q) ^ 2 = q := sq_sqrt hq0
  have h47 : (47 / 10 : ℝ) ≤ √q := by
    rw [le_sqrt (by norm_num) hq0]
    linarith
  nlinarith

/-- **The margin $q + 1 - 2\sqrt q > 12$ for natural $q \ge 23$.** For every natural number
$q \ge 23$, $q + 1 - 2\sqrt q - 12 > 0$ in $\mathbb{R}$. This is the case of
`Real.add_one_sub_two_mul_sqrt_sub_twelve_pos` that Poonen's proof uses, $q$ being the number of
elements of a finite field.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, p. 3 of the author's version with
the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "For any
$q \ge 23$, the Hasse bound yields $\#X(\mathbb{F}_q) \ge (q + 1 - 2\sqrt q) - 12 > 0$". -/
theorem natCast_add_one_sub_two_mul_sqrt_sub_twelve_pos {q : ℕ} (hq : 23 ≤ q) :
    0 < (q : ℝ) + 1 - 2 * √(q : ℝ) - 12 :=
  add_one_sub_two_mul_sqrt_sub_twelve_pos (by exact_mod_cast hq)

end Real
