/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SylvesterCriterion

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Sylvester's criterion

`!![2, 1; 1, 2]` is positive definite (leading minors `2`, `3`);
`!![1, 2; 2, 1]` is symmetric but not positive definite (determinant
`-3`); `!![-1, 0; 0, -1]` fails already at the first minor; the
`3 × 3` tridiagonal `!![2, 1, 0; 1, 2, 1; 0, 1, 2]` is positive definite
(leading minors `2`, `3`, `4`). The Hermitian hypothesis is essential:
`!![1, 2; 0, 1]` has leading minors `1` and `1` but is not positive
definite. And nonnegativity of the leading minors does not imply
positive semidefiniteness: `!![0, 0; 0, -1]` has leading minors `0`
and `0` but is not positive semidefinite.
-/

namespace MathlibExtTest.SylvesterCriterion

open Matrix

/-- A symmetric `2 × 2` matrix is Hermitian. -/
private theorem hermitian_of_symm_two {a b c : ℝ} :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The leading `0 × 0` minor is `1`. -/
private theorem det_leading_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hk : 0 ≤ n) :
    (leadingPrincipalSubmatrix A 0 hk).det = 1 := by
  simp [leadingPrincipalSubmatrix, Matrix.det_fin_zero]

/-- The leading `1 × 1` minor is the top-left entry. The entry is
written with `Fin.castLE` so that no `OfNat (Fin n)` instance is needed
for a variable `n`. -/
private theorem det_leading_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hk : 1 ≤ n) :
    (leadingPrincipalSubmatrix A 1 hk).det =
      A (Fin.castLE hk 0) (Fin.castLE hk 0) := by
  rw [leadingPrincipalSubmatrix, Matrix.det_fin_one]
  rfl

/-- The leading `2 × 2` minor is the `2 × 2` determinant of the
top-left entries, again written with `Fin.castLE` indices. -/
private theorem det_leading_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hk : 2 ≤ n) :
    (leadingPrincipalSubmatrix A 2 hk).det =
      A (Fin.castLE hk 0) (Fin.castLE hk 0) *
          A (Fin.castLE hk 1) (Fin.castLE hk 1)
        - A (Fin.castLE hk 0) (Fin.castLE hk 1) *
          A (Fin.castLE hk 1) (Fin.castLE hk 0) := by
  rw [leadingPrincipalSubmatrix, Matrix.det_fin_two]
  rfl

/-- `!![2, 1; 1, 2]` is positive definite: leading minors `2` and `3`. -/
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have hH : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian :=
    hermitian_of_symm_two
  refine (posDef_iff_leadingPrincipalMinors_pos 2 _ hH).mpr fun k hk => ?_
  interval_cases k
  · rw [det_leading_zero]; norm_num
  · rw [det_leading_one]; change (0 : ℝ) < 2; norm_num
  · rw [leadingPrincipalSubmatrix_self, Matrix.det_fin_two]
    change (0 : ℝ) < 2 * 2 - 1 * 1; norm_num

/-- `!![1, 2; 2, 1]` is not positive definite: its determinant is `-3`. -/
example : ¬ (!![1, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  intro hPos
  have hH : (!![1, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian :=
    hermitian_of_symm_two
  have h2 := (posDef_iff_leadingPrincipalMinors_pos 2 _ hH).mp hPos 2 (le_refl 2)
  rw [leadingPrincipalSubmatrix_self, Matrix.det_fin_two] at h2
  change (0 : ℝ) < 1 * 1 - 2 * 2 at h2
  norm_num at h2

/-- `!![-1, 0; 0, -1]` is not positive definite: its first minor is `-1`. -/
example : ¬ (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  intro hPos
  have hH : (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian :=
    hermitian_of_symm_two
  have h1 := (posDef_iff_leadingPrincipalMinors_pos 2 _ hH).mp hPos 1 (by norm_num)
  rw [det_leading_one] at h1
  change (0 : ℝ) < (-1 : ℝ) at h1
  norm_num at h1

/-- The `3 × 3` tridiagonal `!![2, 1, 0; 1, 2, 1; 0, 1, 2]` is positive
definite: leading minors `2`, `3`, `4`. -/
example : (!![2, 1, 0; 1, 2, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  have hH : (!![2, 1, 0; 1, 2, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine (posDef_iff_leadingPrincipalMinors_pos 3 _ hH).mpr fun k hk => ?_
  interval_cases k
  · rw [det_leading_zero]; norm_num
  · rw [det_leading_one]; change (0 : ℝ) < 2; norm_num
  · rw [det_leading_two]; change (0 : ℝ) < 2 * 2 - 1 * 1; norm_num
  · rw [leadingPrincipalSubmatrix_self, Matrix.det_fin_three]
    change (0 : ℝ) < 2 * 2 * 2 - 2 * 1 * 1 - 1 * 1 * 2 + 1 * 1 * 0 + 0 * 1 * 1
      - 0 * 2 * 0
    norm_num

/-- The Hermitian hypothesis is essential: `!![1, 2; 0, 1]` has leading
minors `1` and `1` but is not Hermitian, hence not positive definite. -/
example : ¬ (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  intro hPos
  have hEq : (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ = !![1, 2; 0, 1] :=
    hPos.isHermitian
  have h01 := Matrix.ext_iff.mpr hEq 0 1
  simp [Matrix.conjTranspose_apply] at h01

/-- Nonnegativity of the leading minors does not imply positive
semidefiniteness: `!![0, 0; 0, -1]` has leading minors `0` and `0`,
but `x = (0, 1)` gives quadratic form `-1`. -/
example : ¬ (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  intro hPSD
  have hle := hPSD.dotProduct_mulVec_nonneg ![0, 1]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hle

/-- The leading minors of `!![0, 0; 0, -1]` are both `0`, so the
previous counterexample is sharp: nonnegativity of the leading minors
is not enough for semidefiniteness. -/
example : (leadingPrincipalSubmatrix (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) 1
      (by norm_num)).det = 0 := by
  rw [det_leading_one]
  rfl

example : (leadingPrincipalSubmatrix (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) 2
      (le_refl 2)).det = 0 := by
  rw [leadingPrincipalSubmatrix_self, Matrix.det_fin_two]
  norm_num

/-- The block-matrix step of the proof, in the case `B = 1`, `u = 0`,
`D = 1`: the `2 × 2` identity over `Fin 1 ⊕ Fin 1` is positive
definite. -/
example : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ
    (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos isHermitian_one fun x hx => ?_
    have hx0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      funext i
      fin_cases i; simp [h0]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply,
      star_trivial, Matrix.one_apply]
    simp [hx0]
  have hS : (1 - (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
      * 0).PosDef := by
    simpa using h1
  exact PosDef.fromBlocks (u := (0 : Matrix (Fin 1) (Fin 1) ℝ)) h1 isHermitian_one hS

#print axioms Matrix.posDef_iff_leadingPrincipalMinors_pos
#print axioms Matrix.PosDef.fromBlocks

end MathlibExtTest.SylvesterCriterion
