/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The bisector equation with a zero slope

Let $a, b, c$ be integers satisfying the bisector equation
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. If $a = 0$, the equation reads
$c^2 (b^2 + 1) = (b - c)^2$, that is $b \bigl(b (c^2 - 1) + 2 c\bigr) = 0$. A nonzero $b$ would
give $|b| \, |c^2 - 1| = 2 |c|$, hence $c^2 - 1 \le 2 |c|$ and $|c| \le 2$; checking
$c \in \{-2, \dots, 2\}$ leaves no integer $b \ne 0$. So $b = 0$, and the case $b = 0$ is
symmetric.

This follows Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines
with Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(b).
-/

@[expose] public section

namespace MetaMathlibExt

namespace bisector_equation_int_zero

/-- If `c² (b² + 1) = (b - c)²` in the integers, then `b = 0`. -/
private theorem eq_zero_of_sq_mul (b c : ℤ) (h : c ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2) :
    b = 0 := by
  by_contra hb
  have h1 : b * (c ^ 2 - 1) = -2 * c := by
    have h2 : b * (b * (c ^ 2 - 1) + 2 * c) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hb
    · linear_combination h3
  have hc : -2 ≤ c ∧ c ≤ 2 := by
    rcases lt_or_gt_of_ne hb with hb' | hb'
    · have h2 : (b + 1) * (c ^ 2 - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by omega) (by nlinarith [sq_nonneg c, sq_nonneg (c - 1)])
      constructor <;> nlinarith
    · have h2 : 0 ≤ (b - 1) * (c ^ 2 - 1) :=
        mul_nonneg (by omega) (by nlinarith [sq_nonneg c, sq_nonneg (c - 1)])
      constructor <;> nlinarith
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases c <;> omega

end bisector_equation_int_zero

/-- **No nontrivial integer solutions of the bisector equation with $a = 0$ or $b = 0$.** Let
$a, b, c$ be integers with $a = 0$ or $b = 0$ and
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then $|a| = |b|$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(b)
(`integers-2024-A111-prop-2`). -/
theorem bisector_equation_int_zero (a b c : ℤ) (h0 : a = 0 ∨ b = 0)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) : |a| = |b| := by
  rcases h0 with rfl | rfl
  · rw [bisector_equation_int_zero.eq_zero_of_sq_mul b c (by linear_combination h)]
  · rw [bisector_equation_int_zero.eq_zero_of_sq_mul a c (by linear_combination -h)]

end MetaMathlibExt
