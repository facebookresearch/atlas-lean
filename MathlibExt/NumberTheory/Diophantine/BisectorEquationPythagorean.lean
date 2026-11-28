/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Pythagorean parametrization of rational bisector slopes

Suppose rational slopes $a, b, c$ satisfy $|a| \ne |b|$ and the bisector equation
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$, and $a^2 + 1$ and $b^2 + 1$ are rational squares.
Use the positive square roots to parametrize $a$ and $b$, and write the parameters with a
common denominator. After substitution, the bisector equation factors into two linear equations
for $c$, giving the two fractions in Form (2).

## References

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
  Rational Slopes*, INTEGERS 24 (2024), Article A111, pp. 1–26, Theorem 1(i), Form (2), and its
  proof in §4, pp. 16–17. The slope parameters come from the sums of the two coordinates of
  the solutions of $x^2 - y^2 = -1$, as in §4. We obtain the two fractions by factoring the
  bisector equation directly.
-/

namespace MetaMathlibExt

private theorem pos_slope_parameter (p q : ℚ) (h : p ^ 2 - q ^ 2 = -1) :
    0 < p + |q| ∧ 2 * (p + |q|) * p = (p + |q|) ^ 2 - 1 := by
  have hq : q ^ 2 = p ^ 2 + 1 := by linear_combination -h
  have hlt : |p| < |q| := sq_lt_sq.mp (by rw [hq]; exact lt_add_of_pos_right _ zero_lt_one)
  refine ⟨?_, ?_⟩
  · simpa only [sub_neg_eq_add, add_comm] using sub_pos.mpr ((neg_le_abs p).trans_lt hlt)
  · rw [← sq_abs q] at h
    linear_combination h

/-- **Pythagorean parametrization of rational solutions of the bisector equation.** Let $a, b, c$
be rational numbers with $|a| \ne |b|$ and $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$, and suppose
that $a^2 + 1$ and $b^2 + 1$ are squares of rational numbers. Then there are integers $l, m, n$ with
$|l| \ne |m|$, $l m \ne n^2$ and $l m n \ne 0$ such that
$$a = \frac{l^2 - n^2}{2 l n}, \qquad b = \frac{m^2 - n^2}{2 m n},$$
and
$$c = \frac{l m - n^2}{(l + m) n} \qquad \text{or} \qquad c = -\frac{(l + m) n}{l m - n^2}.$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(i)
(`integers-2024-A111-thm-1`). -/
public theorem bisector_equation_rat_solution_pythagorean (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - b₂ ^ 2 = -1) :
    ∃ l m n : ℤ, |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      (c = ((l : ℚ) * m - n ^ 2) / ((l + m) * n) ∨ c = -(((l : ℚ) + m) * n) / (l * m - n ^ 2)) := by
  obtain ⟨a₂, ha₂⟩ := ha
  obtain ⟨b₂, hb₂⟩ := hb
  let x := a + |a₂|
  let y := b + |b₂|
  obtain ⟨hx, hax⟩ : 0 < x ∧ 2 * x * a = x ^ 2 - 1 := pos_slope_parameter a a₂ ha₂
  obtain ⟨hy, hby⟩ : 0 < y ∧ 2 * y * b = y ^ 2 - 1 := pos_slope_parameter b b₂ hb₂
  -- Write `x = l / n` and `y = m / n` using the same positive denominator.
  let l : ℤ := x.num * y.den
  let m : ℤ := y.num * x.den
  let n : ℤ := (x.den : ℤ) * y.den
  have hl : (l : ℚ) = x * n := by
    simp only [l, n, Int.cast_mul, Int.cast_natCast, ← x.mul_den_eq_num, mul_assoc]
  have hm : (m : ℚ) = y * n := by
    simp only [m, n, Int.cast_mul, Int.cast_natCast, ← y.mul_den_eq_num, mul_assoc]
    rw [mul_comm (y.den : ℚ) (x.den : ℚ)]
  have hn : 0 < (n : ℚ) := by
    simp only [n, Int.cast_mul, Int.cast_natCast]
    exact mul_pos (Nat.cast_pos.mpr x.den_pos) (Nat.cast_pos.mpr y.den_pos)
  have hlpos : 0 < (l : ℚ) := hl.symm ▸ mul_pos hx hn
  have hmpos : 0 < (m : ℚ) := hm.symm ▸ mul_pos hy hn
  have ha' : 2 * (l : ℚ) * n * a = (l : ℚ) ^ 2 - n ^ 2 := by
    rw [hl]
    linear_combination (n : ℚ) ^ 2 * hax
  have hb' : 2 * (m : ℚ) * n * b = (m : ℚ) ^ 2 - n ^ 2 := by
    rw [hm]
    linear_combination (n : ℚ) ^ 2 * hby
  have haForm : a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) :=
    (eq_div_iff (by positivity)).2 (by simpa only [mul_comm a] using ha')
  have hbForm : b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) :=
    (eq_div_iff (by positivity)).2 (by simpa only [mul_comm b] using hb')
  have hab₀ : a ≠ b := fun he => hab (congrArg abs he)
  have habSum : a + b ≠ 0 := by
    intro he
    exact hab (by rw [eq_neg_of_add_eq_zero_left he, abs_neg])
  have hlm : |l| ≠ |m| := by
    have hlz : 0 < l := by exact_mod_cast hlpos
    have hmz : 0 < m := by exact_mod_cast hmpos
    rw [abs_of_pos hlz, abs_of_pos hmz]
    intro he
    rw [he] at haForm
    exact hab₀ (haForm.trans hbForm.symm)
  -- `u` and `v` are the numerator and denominator of the first bisector slope.
  let u : ℚ := (l : ℚ) * m - n ^ 2
  let v : ℚ := ((l : ℚ) + m) * n
  let D : ℚ := 2 * (l : ℚ) * m * n ^ 2
  have hsum : (a + b) * D = u * v := by
    dsimp only [D, u, v]
    linear_combination (m : ℚ) * n * ha' + (l : ℚ) * n * hb'
  have hprod : 2 * (a * b - 1) * D = u ^ 2 - v ^ 2 := by
    dsimp only [D, u, v]
    linear_combination (2 * (m : ℚ) * n * b) * ha' + ((l : ℚ) ^ 2 - n ^ 2) * hb'
  have hD : D ≠ 0 := by dsimp only [D]; positivity
  have hu : u ≠ 0 := by
    intro he
    exact mul_ne_zero habSum hD (by simpa only [he, zero_mul] using hsum)
  have hv : v ≠ 0 := by dsimp only [v]; positivity
  have hquad : (a + b) * (1 - c ^ 2) + 2 * c * (a * b - 1) = 0 := by
    have ht : (a - b) * ((a + b) * (1 - c ^ 2) + 2 * c * (a * b - 1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp ht).resolve_left (sub_ne_zero.mpr hab₀)
  have hfactor : (u - c * v) * (v + c * u) = 0 := by
    linear_combination D * hquad - (1 - c ^ 2) * hsum - c * hprod
  have hln : l * m ≠ n ^ 2 := by
    intro he
    apply hu
    exact sub_eq_zero.mpr (by exact_mod_cast he)
  have hnonzero : l * m * n ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero hlpos.ne' hmpos.ne') hn.ne')
  refine ⟨l, m, n, hlm, hln, hnonzero, haForm, hbForm, ?_⟩
  rcases mul_eq_zero.mp hfactor with he | he
  · exact Or.inl ((eq_div_iff hv).2 (by linear_combination -he))
  · exact Or.inr ((eq_div_iff hu).2 (by linear_combination he))

end MetaMathlibExt
