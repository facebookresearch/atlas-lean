/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressions

/-!
# A nine-term progression for binary quadratic forms

An integral binary quadratic form with non-square discriminant represents every term
of some nonconstant nine-term arithmetic progression over the integers.
-/

public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- **Binary quadratic forms with non-square discriminant represent nine-term progressions.**
Let $a, b, c$ be integers such that the discriminant $b^2 - 4ac$ is not a perfect square. Then
there are integers $u_0$ and $d \ne 0$ such that for every natural number $i < 9$ there are
integers $x, y$ with $u_0 + id = ax^2 + bxy + cy^2$.

The condition $d \ne 0$ excludes constant progressions.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 2. -/
theorem exists_nine_term_arithmetic_progression_binary_quadratic
    (a b c : ℤ) (hirr : ¬IsSquare (b ^ 2 - 4 * a * c)) :
    ∃ u0 d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      u0 + i * d = a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hirr (by simpa using IsSquare.sq b)
  let q : ℤ := 4 * a * c - b ^ 2
  -- Multiplying the discriminant by four preserves nonsquareness over the integers.
  have hdiag : ¬IsSquare (-4 * 1 * q) := by
    rintro ⟨r, hr⟩
    have hmod : r % 2 = 0 := by
      rw [← Int.sq_emod_two, pow_two, ← hr]
      omega
    have hr' : r = 2 * (r / 2) := by omega
    rw [hr'] at hr
    dsimp [q] at hr
    exact hirr ⟨r / 2, by nlinarith only [hr]⟩
  have hq : q ≠ 0 := fun h => hdiag ⟨0, by simp [h]⟩
  -- Take the parameters `p = h = 1` and choose `g` so none of the factors of `d` vanish.
  let g : ℤ := 6 * |q| + 1
  have hgpos : 0 < g := by
    dsimp [g]
    linarith [abs_nonneg q]
  have hg : 6 * |q| < g ^ 2 := by
    dsimp [g]
    nlinarith [sq_nonneg (6 * |q|), abs_nonneg q]
  have h₁ : 0 < g ^ 2 - 3 * q := by linarith [le_abs_self q, abs_nonneg q]
  have h₂ : 0 < g ^ 2 + 6 * q := by linarith [neg_abs_le q]
  have h₃ : 0 < 2 * g ^ 2 + 3 * q := by linarith [neg_abs_le q, abs_nonneg q]
  let u := 4 * g ^ 10 - 47 * q * g ^ 8 - 156 * q ^ 2 * g ^ 6 +
    2052 * q ^ 3 * g ^ 4 + 4833 * q ^ 4 * g ^ 2 + 324 * q ^ 5
  let d := 12 * q * g ^ 2 * (g ^ 2 - 3 * q) * (g ^ 2 + 6 * q) * (2 * g ^ 2 + 3 * q)
  have hd : d ≠ 0 := by simp [d, hq, hgpos.ne', h₁.ne', h₂.ne', h₃.ne']
  refine ⟨a * u, a * d, mul_ne_zero ha hd, ?_⟩
  intro i hi
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, u + i * d = x ^ 2 + q * y ^ 2 := by
    simpa [u, d] using exists_representation_nine_term_diagonal_quadratic 1 q g 1 hdiag i hi
  -- The integral substitution scales the diagonal values by `a`.
  refine ⟨x - b * y, 2 * a * y, ?_⟩
  calc
    a * u + i * (a * d) = a * (u + i * d) := by ring
    _ = a * (x ^ 2 + q * y ^ 2) := by rw [hxy]
    _ = _ := by
      dsimp only [q]
      ring

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted
