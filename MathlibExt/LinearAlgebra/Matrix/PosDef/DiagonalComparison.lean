/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant

import Mathlib.Tactic.Linarith

/-!
# Comparison of a positive definite form with its diagonal

Let `Y` be a real positive definite matrix and `Q(n) = nᵀ Y n` its quadratic form.

* For every index `i` and every vector `n`, `n i ^ 2 ≤ Y⁻¹ i i * Q(n)`. Here `Y⁻¹ i i` is the
  value of `Q` at `u = Y⁻¹ eᵢ`, and `uᵀ Y n = n i`, so this is the Cauchy–Schwarz inequality for
  the positive semidefinite bilinear form `(a, b) ↦ aᵀ Y b`.
* For a matrix indexed by `Fin (m + 1)`, the diagonal entry `Y⁻¹ i i` of the inverse is the
  determinant of the principal minor of `Y` obtained by deleting row and column `i`, divided by
  `det Y`.
* If the product of the diagonal entries of `Y` is at most `μ * det Y`, then
  `Y i i * n i ^ 2 ≤ μ * Q(n)` for every `i` and `n`, and summing over `i`,
  `∑ i, Y i i * n i ^ 2 ≤ g * μ * Q(n)` for `Y` of size `g × g`. The principal minor is positive
  semidefinite, so Hadamard's inequality bounds its determinant by the product of its diagonal
  entries, which is `(∏ j, Y j j) / Y i i ≤ μ * det Y / Y i i`.

All three statements are standard linear algebra. The last one reuses Hadamard's inequality
`Matrix.PosSemidef.det_le_prod_diag` for real positive semidefinite matrices.

## Main declarations

* `Matrix.PosSemidef.dotProduct_mulVec_sq_le`: Cauchy–Schwarz for `(a, b) ↦ a ⬝ᵥ Y *ᵥ b`.
* `Matrix.PosDef.sq_apply_le_inv_apply_mul_dotProduct_mulVec`:
  `n i ^ 2 ≤ Y⁻¹ i i * (n ⬝ᵥ Y *ᵥ n)`.
* `Matrix.inv_apply_self_eq_det_submatrix_div_det`:
  `A⁻¹ i i = (A.submatrix i.succAbove i.succAbove).det / A.det`.
* `Matrix.PosDef.diag_mul_inv_apply_self_le_of_prod_diag_le`: `Y i i * Y⁻¹ i i ≤ μ`.
* `Matrix.PosDef.diag_mul_sq_le_of_prod_diag_le`: `Y i i * n i ^ 2 ≤ μ * (n ⬝ᵥ Y *ᵥ n)`.
* `Matrix.PosDef.sum_diag_mul_sq_le_of_prod_diag_le`:
  `∑ i, Y i i * n i ^ 2 ≤ g * μ * (n ⬝ᵥ Y *ᵥ n)`.
-/

@[expose] public section

namespace Matrix

/-- **Cauchy–Schwarz inequality for a positive semidefinite form.** Let $Y$ be a positive
semidefinite real matrix indexed by a finite type. For all real vectors $u$ and $v$,
$(u^{\mathsf T} Y v)^2 \le (u^{\mathsf T} Y u)(v^{\mathsf T} Y v)$. -/
theorem PosSemidef.dotProduct_mulVec_sq_le {ι : Type*} [Fintype ι] {Y : Matrix ι ι ℝ}
    (hY : Y.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ Y *ᵥ v) ^ 2 ≤ (u ⬝ᵥ Y *ᵥ u) * (v ⬝ᵥ Y *ᵥ v) := by
  have hsymm : v ⬝ᵥ Y *ᵥ u = u ⬝ᵥ Y *ᵥ v := by
    have hT : Yᵀ = Y := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hY.isHermitian.eq
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  have hq : ∀ t : ℝ,
      0 ≤ (u ⬝ᵥ Y *ᵥ u) * (t * t) + 2 * (u ⬝ᵥ Y *ᵥ v) * t + v ⬝ᵥ Y *ᵥ v := by
    intro t
    have h := hY.dotProduct_mulVec_nonneg (t • u + v)
    simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hsymm] at h
    linarith
  have h := discrim_le_zero hq
  rw [discrim] at h
  linarith

/-- **A coordinate bounded by the diagonal of the inverse.** Let $Y$ be a positive definite real
matrix indexed by a finite type and $Q(n) = n^{\mathsf T} Y n$. For every index $i$ and every
real vector $n$, $n_i^2 \le (Y^{-1})_{ii}\, Q(n)$. -/
theorem PosDef.sq_apply_le_inv_apply_mul_dotProduct_mulVec {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Y : Matrix ι ι ℝ} (hY : Y.PosDef) (i : ι) (n : ι → ℝ) :
    n i ^ 2 ≤ Y⁻¹ i i * (n ⬝ᵥ Y *ᵥ n) := by
  set u : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hu
  have hYu : Y *ᵥ u = Pi.single i 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det Y).mp hY.isUnit),
      one_mulVec]
  have h1 : n ⬝ᵥ Y *ᵥ u = n i := by
    rw [hYu, dotProduct_single, mul_one]
  have h2 : u ⬝ᵥ Y *ᵥ u = Y⁻¹ i i := by
    rw [hYu, dotProduct_single, mul_one, hu, mulVec_single_one]
    rfl
  have h := hY.posSemidef.dotProduct_mulVec_sq_le n u
  rw [h1, h2] at h
  linarith [mul_comm (Y⁻¹ i i) (n ⬝ᵥ Y *ᵥ n)]

/-- **Diagonal entries of the inverse as quotients of determinants.** Let $A$ be a square matrix
of size $m + 1$ over a field and $A^{(i)}$ the matrix obtained from $A$ by deleting row $i$ and
column $i$. Then $(A^{-1})_{ii} = \det A^{(i)} / \det A$. When $\det A = 0$ both sides are $0$,
with the conventions $A^{-1} = 0$ and $x / 0 = 0$. -/
theorem inv_apply_self_eq_det_submatrix_div_det {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    A⁻¹ i i = (A.submatrix i.succAbove i.succAbove).det / A.det := by
  rw [inv_def, Matrix.smul_apply, adjugate_fin_succ_eq_det_submatrix, Ring.inverse_eq_inv',
    smul_eq_mul, (Even.add_self (i : ℕ)).neg_one_pow, one_mul, div_eq_inv_mul]

/-- Let $Y$ be a positive definite real $g \times g$ matrix and $\mu$ a real number with
$\prod_j y_{jj} \le \mu \det Y$. Then $y_{ii} (Y^{-1})_{ii} \le \mu$ for every index $i$. -/
theorem PosDef.diag_mul_inv_apply_self_le_of_prod_diag_le {g : ℕ}
    {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {μ : ℝ} (hμ : ∏ j, Y j j ≤ μ * Y.det)
    (i : Fin g) : Y i i * Y⁻¹ i i ≤ μ := by
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by have := i.pos; omega⟩
  have hdet : 0 < Y.det := hY.det_pos
  have hyii : 0 < Y i i := hY.diag_pos
  have hminor : (Y.submatrix i.succAbove i.succAbove).det ≤
      ∏ j, Y (i.succAbove j) (i.succAbove j) :=
    (hY.posSemidef.submatrix i.succAbove).det_le_prod_diag
  rw [inv_apply_self_eq_det_submatrix_div_det, ← mul_div_assoc, div_le_iff₀ hdet]
  calc Y i i * (Y.submatrix i.succAbove i.succAbove).det
      ≤ Y i i * ∏ j, Y (i.succAbove j) (i.succAbove j) :=
        mul_le_mul_of_nonneg_left hminor hyii.le
    _ = ∏ j, Y j j := (Fin.prod_univ_succAbove (fun j => Y j j) i).symm
    _ ≤ μ * Y.det := hμ

/-- **Comparison of a reduced form with its diagonal.** Let $Y = (y_{ij})$ be a positive definite
real $g \times g$ matrix, $Q(n) = n^{\mathsf T} Y n$, and $\mu$ a real number with
$\prod_j y_{jj} \le \mu \det Y$. Then $y_{ii} n_i^2 \le \mu\, Q(n)$ for every index $i$ and every
real vector $n$. -/
theorem PosDef.diag_mul_sq_le_of_prod_diag_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}
    (hY : Y.PosDef) {μ : ℝ} (hμ : ∏ j, Y j j ≤ μ * Y.det) (i : Fin g) (n : Fin g → ℝ) :
    Y i i * n i ^ 2 ≤ μ * (n ⬝ᵥ Y *ᵥ n) := by
  have hyii : 0 < Y i i := hY.diag_pos
  have hQ : 0 ≤ n ⬝ᵥ Y *ᵥ n := by
    simpa only [star_trivial] using hY.posSemidef.dotProduct_mulVec_nonneg n
  calc Y i i * n i ^ 2 ≤ Y i i * (Y⁻¹ i i * (n ⬝ᵥ Y *ᵥ n)) :=
        mul_le_mul_of_nonneg_left (hY.sq_apply_le_inv_apply_mul_dotProduct_mulVec i n) hyii.le
    _ = (Y i i * Y⁻¹ i i) * (n ⬝ᵥ Y *ᵥ n) := (mul_assoc _ _ _).symm
    _ ≤ μ * (n ⬝ᵥ Y *ᵥ n) :=
        mul_le_mul_of_nonneg_right (hY.diag_mul_inv_apply_self_le_of_prod_diag_le hμ i) hQ

/-- **Comparison of a reduced form with its diagonal, summed form.** Let $Y = (y_{ij})$ be a
positive definite real $g \times g$ matrix, $Q(n) = n^{\mathsf T} Y n$, and $\mu$ a real number
with $\prod_j y_{jj} \le \mu \det Y$. Then $\sum_i y_{ii} n_i^2 \le g \mu\, Q(n)$ for every real
vector $n$. -/
theorem PosDef.sum_diag_mul_sq_le_of_prod_diag_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}
    (hY : Y.PosDef) {μ : ℝ} (hμ : ∏ j, Y j j ≤ μ * Y.det) (n : Fin g → ℝ) :
    ∑ i, Y i i * n i ^ 2 ≤ g * μ * (n ⬝ᵥ Y *ᵥ n) := by
  calc ∑ i, Y i i * n i ^ 2 ≤ ∑ _i : Fin g, μ * (n ⬝ᵥ Y *ᵥ n) :=
        Finset.sum_le_sum fun i _ => hY.diag_mul_sq_le_of_prod_diag_le hμ i n
    _ = g * μ * (n ⬝ᵥ Y *ᵥ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end Matrix
