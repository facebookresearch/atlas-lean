/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Axis intercepts of a shifted Pell curve

We prove that the largest intercept norm is attained on the horizontal axis.
-/

namespace MetaMathlibExt

/-- **Largest intercept norm of a shifted Pell curve.** Let $D > 0$, $a \ne 0$ and $b$ be
integers. The intercepts of the shifted Pell curve $(x - a)^2 - D (y - b)^2 = 1$ with the axes
are $(a \pm \sqrt{1 + D b^2}, 0)$ and $(0, b \pm \sqrt{(a^2 - 1) / D})$, with $L^1$ norms
$|a \pm \sqrt{1 + D b^2}|$ and $|b \pm \sqrt{(a^2 - 1) / D}|$. The largest of these four norms
is $|a| + \sqrt{1 + D b^2}$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.2
(`integers-2025-A112-prop-3-2`). -/
public theorem pell_shifted_intercepts_max {D a : ℤ} (hD : 0 < D) (ha : a ≠ 0) (b : ℤ) :
    |(a : ℝ)| + Real.sqrt (1 + D * b ^ 2) =
      max (max |a + Real.sqrt (1 + D * b ^ 2)| |a - Real.sqrt (1 + D * b ^ 2)|)
        (max |b + Real.sqrt ((a ^ 2 - 1) / D)| |b - Real.sqrt ((a ^ 2 - 1) / D)|) := by
  have hD₁ : 1 ≤ (D : ℝ) := by
    exact_mod_cast (show 1 ≤ D by omega)
  have ha₁ : 1 ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha
  have haSq : 0 ≤ (a : ℝ) ^ 2 - 1 :=
    sub_nonneg.mpr ((one_le_sq_iff_one_le_abs _).mpr ha₁)
  have hy : Real.sqrt (((a : ℝ) ^ 2 - 1) / D) ≤ |(a : ℝ)| := by
    rw [← Real.sqrt_sq_eq_abs (a : ℝ)]
    exact Real.sqrt_le_sqrt ((div_le_self haSq hD₁).trans (sub_le_self _ zero_le_one))
  have hx : |(b : ℝ)| ≤ Real.sqrt (1 + D * (b : ℝ) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs (b : ℝ)]
    apply Real.sqrt_le_sqrt
    calc
      (b : ℝ) ^ 2 ≤ D * (b : ℝ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hD₁
      _ ≤ 1 + D * (b : ℝ) ^ 2 := le_add_of_nonneg_left zero_le_one
  have max_abs_add_sub (x y : ℝ) (hy₀ : 0 ≤ y) : max |x + y| |x - y| = |x| + y := by
    refine le_antisymm (max_le ?_ ?_) ?_
    · simpa only [abs_of_nonneg hy₀] using abs_add_le x y
    · simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg hy₀] using abs_add_le x (-y)
    · rcases le_or_gt 0 x with hx₀ | hx₀
      · simpa only [abs_of_nonneg hx₀, abs_of_nonneg (add_nonneg hx₀ hy₀)] using
          le_max_left |x + y| |x - y|
      · simpa only [abs_of_nonpos hx₀.le, abs_of_nonpos (sub_nonpos.mpr (hx₀.le.trans hy₀)),
          neg_sub, neg_add_eq_sub] using le_max_right |x + y| |x - y|
  rw [max_abs_add_sub _ _ (Real.sqrt_nonneg _), max_abs_add_sub _ _ (Real.sqrt_nonneg _)]
  exact (max_eq_left ((add_le_add hx hy).trans_eq (add_comm _ _))).symm

end MetaMathlibExt
