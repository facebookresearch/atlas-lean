/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Tactic.LinearCombination

/-!
# Rational solutions of the bisector equation

For rational slopes $a, b, c$ with $|a| \ne |b|$ satisfying the bisector equation, $a$ and $b$
are first coordinates of rational solutions of the same negative Pell equation with a positive
square-free parameter $d$. A signed choice of the second coordinates gives the fraction for $c$.

## References

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
  Rational Slopes*, INTEGERS 24 (2024), Article A111, pp. 1–26, Proposition 1(b) and its proof in
  §2, pp. 6–7. We extract the square-free factor from the first slope alone and use the signed
  ratio of the slope differences to obtain the other second coordinate.
-/

namespace MetaMathlibExt

/-- **Rational solutions of the bisector equation.** Let $a, b, c$ be rational numbers with
$|a| \ne |b|$ and $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then there are a square-free
natural number $d > 0$ and rational numbers $a_2, b_2$ with $a^2 - d a_2^2 = -1$ and
$b^2 - d b_2^2 = -1$ such that either $a_2 + b_2 \ne 0$ and
$c = (a b_2 + a_2 b) / (a_2 + b_2)$, or $b_2 - a_2 \ne 0$ and $c = (a b_2 - a_2 b) / (b_2 - a_2)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(b)
(`integers-2024-A111-prop-1`). -/
public theorem bisector_equation_rat_solution (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧
      b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((b₂ + a₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (b₂ + a₂)) ∨
        (b₂ - a₂ ≠ 0 ∧ c = (a * b₂ - a₂ * b) / (b₂ - a₂))) := by
  obtain ⟨s, d, hsd, hd⟩ := exists_sq_mul_squarefree (a.num.natAbs ^ 2 + a.den ^ 2)
  let a₂ : ℚ := (s : ℚ) / a.den
  have ha : a ^ 2 + 1 = (d : ℚ) * a₂ ^ 2 := by
    have hfac : (s : ℚ) ^ 2 * d = (a.num.natAbs : ℚ) ^ 2 + (a.den : ℚ) ^ 2 := by
      exact_mod_cast hsd
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs, ← a.mul_den_eq_num, mul_pow] at hfac
    have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
    dsimp only [a₂]
    rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hden)]
    linear_combination -hfac
  have hac : a - c ≠ 0 := by
    intro hz
    have hb0 : (b - c) ^ 2 * (a ^ 2 + 1) = 0 := by simpa [hz] using h.symm
    have ha₀ : a ^ 2 + 1 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg a) zero_lt_one).ne'
    have hbc : b = c := by
      by_contra hne
      exact (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hne)) ha₀) hb0
    exact hab (congrArg abs ((sub_eq_zero.mp hz).trans hbc.symm))
  -- This signed choice gives the difference formula without a sign case split.
  let b₂ : ℚ := (b - c) * a₂ / (a - c)
  have hcross : (a - c) * b₂ = (b - c) * a₂ := by
    dsimp only [b₂]
    rw [mul_comm, div_mul_cancel₀ _ hac]
  have hb : b ^ 2 + 1 = (d : ℚ) * b₂ ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hac)
    calc
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := h
      _ = (d : ℚ) * ((b - c) * a₂) ^ 2 := by rw [ha, mul_pow]; ring
      _ = (a - c) ^ 2 * (d * b₂ ^ 2) := by rw [← hcross, mul_pow]; ring
  have hden : b₂ - a₂ ≠ 0 := by
    intro hz
    rw [sub_eq_zero.mp hz, ← ha] at hb
    exact hab ((sq_eq_sq_iff_abs_eq_abs a b).mp (add_right_cancel hb.symm))
  refine ⟨d, Nat.pos_of_ne_zero hd.ne_zero, hd, a₂, b₂, ?_, ?_, Or.inr ⟨hden, ?_⟩⟩
  · linear_combination ha
  · linear_combination hb
  · apply (eq_div_iff hden).2
    linear_combination -hcross

end MetaMathlibExt
