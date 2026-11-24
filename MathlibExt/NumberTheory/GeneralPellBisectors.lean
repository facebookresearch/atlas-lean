/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.SquareModEight

/-!
# Angle bisectors and congruence obstructions for `|x² - d y²| = z`

These results appear in Takashi Hirotsu, *General Pell's
Equations and Angle Bisectors between Planar Lines with Rational
Slopes*, INTEGERS 24 (2024), Article A111.

Squaring the equality of distances to two lines gives an equation for their bisector slope.

Squares are `0` or `1` modulo `4`, so for `d ≡ 1 (mod 4)` the value
`x² - d y²` is `0`, `1`, or `3` modulo `4`, and so is its negation.
Modulo `8`, squares are `0`, `1`, or `4`. If `x² ≡ 5 y² (mod 8)`, both squares are even.

Multiplying `x + y √d` by a solution `a + b √d` of `a² - d b² = -1` negates the value of
`x² - d y²` and keeps the first coordinate coprime to `d` times the second, so strictly primitive
solutions of `x² - d y² = z` give strictly primitive solutions of `x² - d y² = -z`.
-/

@[expose] public section

namespace MetaMathlibExt

-- The first bisector distance equality suffices for this implication.
set_option linter.unusedVariables false in
/-- **Angle bisectors satisfy the bisector equation.** Let $a, b, c$ be real numbers with
$|a| \ne |b|$ and $c \ne 0$, and suppose that the lines $y = cx$ and $y = -c^{-1} x$ both bisect
the angles between the lines $y = ax$ and $y = bx$, that is,
$$
\frac{|a - c|}{\sqrt{a^2 + 1}} = \frac{|b - c|}{\sqrt{b^2 + 1}} \quad\text{and}\quad
\frac{|a + c^{-1}|}{\sqrt{a^2 + 1}} = \frac{|b + c^{-1}|}{\sqrt{b^2 + 1}}.
$$
Then $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$.

A line $y = sx$ bisects the angles between $y = ax$ and $y = bx$ exactly when the point $(1, s)$
is equidistant from both lines, that is, when $|a - s| / \sqrt{a^2 + 1} = |b - s| / \sqrt{b^2 + 1}$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(a)
(`integers-2024-A111-prop-1`). -/
theorem bisector_slope_equation (a b c : ℝ) (hab : |a| ≠ |b|) (hc : c ≠ 0)
    (hbis : |a - c| / √(a ^ 2 + 1) = |b - c| / √(b ^ 2 + 1))
    (hbis' : |a + c⁻¹| / √(a ^ 2 + 1) = |b + c⁻¹| / √(b ^ 2 + 1)) :
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  have h := (div_eq_div_iff (by positivity) (by positivity)).mp hbis
  apply_fun (fun x : ℝ ↦ x ^ 2) at h
  simpa (disch := positivity) only [mul_pow, sq_abs, Real.sq_sqrt] using h

/-- **Bisector-equation solutions from two solutions of $x^2 - d y^2 = -1$.** Let $d$ be an integer
and let $a, a_2, b, b_2$ be rational numbers with $a^2 - d a_2^2 = -1$ and $b^2 - d b_2^2 = -1$.
If $a_2 + b_2 \ne 0$, then $c = (a b_2 + a_2 b) / (a_2 + b_2)$ satisfies
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1),$$
and if $a b_2 + a_2 b \ne 0$, then $c = -(a_2 + b_2) / (a b_2 + a_2 b)$ satisfies it as well.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (3) (`integers-2024-A111-thm-1`). -/
theorem bisector_equation_form_three (d : ℤ) (a a₂ b b₂ : ℚ)
    (ha : a ^ 2 - d * a₂ ^ 2 = -1) (hb : b ^ 2 - d * b₂ ^ 2 = -1) :
    (a₂ + b₂ ≠ 0 → let c := (a * b₂ + a₂ * b) / (a₂ + b₂)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) ∧
    (a * b₂ + a₂ * b ≠ 0 → let c := -(a₂ + b₂) / (a * b₂ + a₂ * b)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) := by
  have h : a₂ ^ 2 * (b ^ 2 + 1) = b₂ ^ 2 * (a ^ 2 + 1) := by
    linear_combination a₂ ^ 2 * hb - b₂ ^ 2 * ha
  constructor
  · intro hden
    dsimp only
    field_simp [hden]
    linear_combination (a - b) ^ 2 * h
  · intro hden
    dsimp only
    field_simp [hden]
    linear_combination -(a - b) ^ 2 * h

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

/-- **Solutions of |x² − dy²| = z are even when d ≡ 5 and z ≡ 0 (mod 8).** Let $d$ and $z$ be
integers with $d \equiv 5 \pmod 8$ and $z \equiv 0 \pmod 8$. If integers $x$ and $y$ satisfy
$|x^2 - dy^2| = z$, then $x$ and $y$ are both even.

The paper also assumes $z > 1$; this is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(d) (`integers-2024-A111-lem-1`). -/
theorem even_of_abs_sq_sub_mul_sq_zero_mod_eight (d z : ℤ) (hd : d % 8 = 5)
    (hz : z % 8 = 0) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y := by
  have hmod : d * y ^ 2 % 8 = x ^ 2 % 8 := by
    apply Int.modEq_iff_dvd.mpr
    rw [← dvd_abs, h]
    exact Int.dvd_of_emod_eq_zero hz
  rw [Int.mul_emod, hd] at hmod
  suffices hxy : Even (x ^ 2) ∧ Even (y ^ 2) by simpa [Int.even_pow] using hxy
  simp only [Int.even_iff]
  have hx := Int.sq_emod_eight x
  have hy := Int.sq_emod_eight y
  omega

-- The hypotheses `1 < d`, `Squarefree d` and `z ≠ 0` from the source are not needed.
set_option linter.unusedVariables false in
/-- **Negating the value of a strictly primitive solution.** Let $d > 1$ be a square-free integer
such that $x^2 - d y^2 = -1$ has an integral solution, and let $z \ne 0$ be an integer. If
$x^2 - d y^2 = z$ has an integral solution with $x$ and $d y$ coprime, then so does
$x^2 - d y^2 = -z$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 4
(`integers-2024-A111-prop-4`). -/
theorem strictlyPrimitive_neg (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (z : ℤ)
    (hz : z ≠ 0) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = z) :
    ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = -z := by
  obtain ⟨a, b, hab⟩ := hneg
  obtain ⟨x, y, ⟨u, v, huv⟩, rfl⟩ := h
  -- Take `(x + y √d) (a + b √d)`. Since `a² - d b² = -1`, the Bézout identity
  -- `u x + v (d y) = 1` turns into one for the new first coordinate and `d` times the second.
  refine ⟨x * a + d * y * b, x * b + y * a, ⟨-u * a + v * d * b, u * b - v * a, ?_⟩, ?_⟩
  · linear_combination (-(a ^ 2 - d * b ^ 2)) * huv - hab
  · linear_combination (x ^ 2 - d * y ^ 2) * hab

end MetaMathlibExt
