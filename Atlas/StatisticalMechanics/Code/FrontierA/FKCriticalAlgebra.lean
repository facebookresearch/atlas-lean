/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib

namespace StatMech.FrontierA


def triangularFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 + 3 * y ^ 2 - q


def hexagonalFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 - 3 * q * y - q ^ 2


theorem dualOdds_eq_of_triangularFKCritical {q y yStar : ℝ}
    (hy : y ≠ 0) (hdual : y * yStar = q)
    (htri : triangularFKCriticalPolynomial q y = 0) :
    yStar = y ^ 2 + 3 * y := by
  unfold triangularFKCriticalPolynomial at htri
  rw [← hdual] at htri
  apply (mul_left_cancel₀ hy)
  nlinarith


theorem hexagonalFKCritical_of_dual_triangular {q y yStar : ℝ}
    (hy : y ≠ 0) (hdual : y * yStar = q)
    (htri : triangularFKCriticalPolynomial q y = 0) :
    hexagonalFKCriticalPolynomial q yStar = 0 := by
  have hStar := dualOdds_eq_of_triangularFKCritical hy hdual htri
  unfold hexagonalFKCriticalPolynomial
  rw [← hdual, hStar]
  ring


theorem hexagonalFKCritical_div_of_triangular {q y : ℝ}
    (hy : y ≠ 0) (htri : triangularFKCriticalPolynomial q y = 0) :
    hexagonalFKCriticalPolynomial q (q / y) = 0 := by
  apply hexagonalFKCritical_of_dual_triangular hy
  · field_simp
  · exact htri



theorem triangularFKCritical_of_dual_hexagonal {q y yStar : ℝ}
    (hyStar : yStar ≠ 0) (hdual : y * yStar = q)
    (hhex : hexagonalFKCriticalPolynomial q yStar = 0) :
    triangularFKCriticalPolynomial q y = 0 := by
  unfold hexagonalFKCriticalPolynomial at hhex
  rw [← hdual] at hhex
  have hStar : yStar = y ^ 2 + 3 * y := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hyStar))
    nlinarith
  unfold triangularFKCriticalPolynomial
  rw [← hdual, hStar]
  ring



theorem triangularFKCritical_iff_hexagonal_of_dual {q y yStar : ℝ}
    (hy : y ≠ 0) (hyStar : yStar ≠ 0) (hdual : y * yStar = q) :
    triangularFKCriticalPolynomial q y = 0 ↔
      hexagonalFKCriticalPolynomial q yStar = 0 :=
  ⟨hexagonalFKCritical_of_dual_triangular hy hdual,
    triangularFKCritical_of_dual_hexagonal hyStar hdual⟩

end StatMech.FrontierA
