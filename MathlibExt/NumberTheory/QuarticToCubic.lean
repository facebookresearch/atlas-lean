/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-!
# Integer points on an even quartic and its associated cubic

The substitution `(x, y) ↦ (a * x ^ 2, a * x * y)` takes integer points on
`y ^ 2 = a * x ^ 4 + c * x ^ 2 + e` to integer points on `Y ^ 2 = X ^ 3 + c * X ^ 2 + a * e * X`.
-/

public section

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

/-- **Integer points on a quartic give integer points on a cubic.** Let $a$, $c$ and $e$ be
integers with $a \neq 0$. If there are integers $x \neq 0$ and $y$ with
$y^2 = a x^4 + c x^2 + e$, then there are integers $X \neq 0$ and $Y$ with
$Y^2 = X^3 + c X^2 + a e X$.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 4. -/
theorem exists_int_point_elliptic_of_exists_int_point_quartic
    (a c e : ℤ) (ha : a ≠ 0)
    (h : ∃ x y : ℤ, x ≠ 0 ∧ y ^ 2 = a * x ^ 4 + c * x ^ 2 + e) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ^ 2 = X ^ 3 + c * X ^ 2 + a * e * X := by
  obtain ⟨x, y, hx, hxy⟩ := h
  refine ⟨a * x ^ 2, a * x * y, mul_ne_zero ha (pow_ne_zero _ hx), ?_⟩
  rw [mul_pow, hxy]
  ring

end MathlibExt.NumberTheory.PowerfulNumbersWanted
