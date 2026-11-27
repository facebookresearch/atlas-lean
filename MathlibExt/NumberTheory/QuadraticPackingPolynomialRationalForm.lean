/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticPackingPolynomials
import all MathlibExt.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The form of quadratic packing polynomials on rational sectors

## References

- M. Brandt and K. S. Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of R^2*,
  INTEGERS 25 (2025), Article A81, pp. 1–23, Theorem 2.
- C. Stanton, *Packing Polynomials on Sectors of R^2*, INTEGERS 14 (2014), Article A67, pp. 1–13,
  Theorem 2.
- K. S. Gjaldbæk, *Non-injectivity of nonzero discriminant polynomials and applications to packing
  polynomials*, Combinatorial and Additive Number Theory IV, Springer (2021), pp. 195–201,
  Equation 1 and Theorem 5.
-/

namespace MetaMathlibExt

open quadraticPackingPolynomial_staircase_congruence

/-- **Stanton's form of a quadratic packing polynomial on a rational sector.** Let $m, n$ be
coprime positive integers and let $P$ be a quadratic packing polynomial on the lattice points
$I(n/m)$ of the sector of slope $n/m$. Then $n$ divides $(m - 1)^2$, and there are integers
$D, E, F$ such that for all real $x, y$
$$
P(x, y) = \frac{n}{2} \left(x - \frac{m - 1}{n} y\right)^2 + \left(D - \frac{n}{2}\right) x +
  \left(E - \frac{(m - 1)^2}{2n}\right) y + F.
$$

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Theorem 2 (`integers-2025-A81-thm-2`). -/
public theorem quadraticPackingPolynomial_rational_sector_form {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P) :
    (n : ℤ) ∣ ((m : ℤ) - 1) ^ 2 ∧
      ∃ D E F : ℤ, ∀ x y, P x y =
        (n : ℝ) / 2 * (x - ((m : ℝ) - 1) / n * y) ^ 2 + (D - (n : ℝ) / 2) * x +
          (E - (((m : ℝ) - 1) ^ 2 / n) / 2) * y + F := by
  obtain ⟨_, _, C, _, _, _, hdouble⟩ := integral_coefficients hm hn hP
  obtain ⟨d, e, f, hform⟩ := packing_form hm hn hmn hP
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- Read the doubled y² coefficient as an integer second difference.
  have hdiff : P 0 1 + P 0 (-1) - 2 * P 0 0 = (C : ℝ) := by
    linear_combination hdouble 0 1 / 2 + hdouble 0 (-1) / 2 - hdouble 0 0
  have hC : (n : ℝ) * C = ((m : ℝ) - 1) ^ 2 := by
    rw [← hdiff]
    simp only [hform]
    field_simp [hnR]
    ring
  have hCZ : (n : ℤ) * C = ((m : ℤ) - 1) ^ 2 := by exact_mod_cast hC
  obtain ⟨F, hF⟩ := integral_values hm hn hP 0 0
  obtain ⟨X, hX⟩ := integral_values hm hn hP 1 0
  obtain ⟨Y, hY⟩ := integral_values hm hn hP 0 1
  have hf : (F : ℝ) = f := by simpa [hform] using hF
  have hx : (X : ℝ) = (n : ℝ) / 2 + d + f := calc
    (X : ℝ) = P 1 0 := by simpa using hX
    _ = _ := by
      rw [hform]
      field_simp [hnR]
      ring
  have hy : (Y : ℝ) = ((m : ℝ) - 1) ^ 2 / n / 2 + e + f := calc
    (Y : ℝ) = P 0 1 := by simpa using hY
    _ = _ := by
      rw [hform]
      field_simp [hnR]
      ring
  refine ⟨⟨C, hCZ.symm⟩, X - F, Y - F, F, fun x y => ?_⟩
  have hquad : ((n : ℝ) * x - ((m : ℝ) - 1) * y) ^ 2 / (2 * n) =
      (n : ℝ) / 2 * (x - ((m : ℝ) - 1) / n * y) ^ 2 := by
    field_simp [hnR]
  rw [hform, hquad]
  push_cast
  linear_combination -x * hx - y * hy + (x + y - 1) * hf

end MetaMathlibExt
