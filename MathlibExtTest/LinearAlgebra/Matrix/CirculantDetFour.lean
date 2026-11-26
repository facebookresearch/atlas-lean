/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.CirculantDetFour

/-!
# Tests for the four-by-four circulant determinant
-/

open MetaMathlibExt

-- Distinct integer entries give a negative determinant.
example : circulantDetFour ![(1 : ℤ), 2, 3, 4] = -160 := by
  rw [circulantDetFour_eq]
  norm_num

-- When opposite entries coincide, the matrix has two pairs of equal rows.
example {R : Type*} [CommRing R] (a b : R) : circulantDetFour ![a, b, a, b] = 0 := by
  simp [circulantDetFour_eq]

-- The delta at the identity gives four copies of the unit circulant determinant.
example :
    (Matrix.circulant (Pi.single (0, 0) 1 : Fin 4 × Fin 4 → ℂ)).det = 1 := by
  rw [c4Sq_groupDet_eq_prod_circulantDetFour]
  have h (k : Fin 4) :
      (fun r : Fin 4 => ∑ s : Fin 4,
        Complex.I ^ (k.val * s.val) * (Pi.single (0, 0) 1 : Fin 4 × Fin 4 → ℂ) (r, s)) =
      Pi.single 0 1 := by
    funext r
    by_cases hr : r = 0 <;> simp [hr, Pi.single_apply, Prod.mk.injEq]
  simp [h, circulantDetFour_single_one]

-- The second-coordinate shift has Fourier coefficients 2 + i^k at r = 0 only.
-- Their product is 3 · 1 · (2 + i)(2 - i) = 15, and every block has size four.
example :
    (Matrix.circulant (fun p : Fin 4 × Fin 4 =>
      (if p = (0, 0) then (2 : ℂ) else 0) + if p = (0, 1) then 1 else 0)).det = 15 ^ 4 := by
  let y : Fin 4 × Fin 4 → ℂ := fun p =>
    (if p = (0, 0) then 2 else 0) + if p = (0, 1) then 1 else 0
  change (Matrix.circulant y).det = _
  rw [c4Sq_groupDet_eq_prod_circulantDetFour (y := y)]
  have h (k : Fin 4) :
      (fun r : Fin 4 => ∑ s : Fin 4, Complex.I ^ (k.val * s.val) * y (r, s)) =
      Pi.single 0 (2 + Complex.I ^ k.val) := by
    funext r
    by_cases hr : r = 0 <;> norm_num [y, hr, Fin.sum_univ_four, Pi.single_apply, Prod.mk.injEq]
  have hdiag (c : ℂ) : circulantDetFour (Pi.single 0 c) = c ^ 4 := by
    have hm : Matrix.circulant (Pi.single 0 c : Fin 4 → ℂ) = Matrix.diagonal (fun _ => c) := by
      ext r s
      simp [Matrix.circulant_apply, Matrix.diagonal_apply, Pi.single_apply, sub_eq_zero]
    rw [circulantDetFour, hm, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp only [h, hdiag]
  rw [Finset.prod_pow]
  congr 1
  have h₃ : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq, neg_one_mul]
  have hpair : (2 + Complex.I) * (2 - Complex.I) = 5 := by
    calc
      _ = 4 - Complex.I ^ 2 := by ring
      _ = _ := by norm_num [Complex.I_sq]
  norm_num [Fin.prod_univ_four, Complex.I_sq, h₃, ← sub_eq_add_neg,
    mul_left_comm (2 + Complex.I) 1, ← mul_assoc, mul_assoc (3 : ℂ), hpair]
