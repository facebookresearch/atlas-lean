/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingSymbol

namespace StatMech.FrontierA

open scoped Matrix




noncomputable def triangularKacWardTurnMatrix
    (rho : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  !![1, 0, rho ^ 2, -(rho ^ 6), rho, -(rho ^ 5);
     0, 1, -(rho ^ 6), rho ^ 2, -(rho ^ 5), rho;
     -(rho ^ 6), rho ^ 2, 1, 0, -(rho ^ 7), rho ^ 3;
     rho ^ 2, -(rho ^ 6), 0, 1, rho ^ 3, -(rho ^ 7);
     -(rho ^ 7), rho ^ 3, rho, -(rho ^ 5), 1, 0;
     rho ^ 3, -(rho ^ 7), -(rho ^ 5), rho, 0, 1]


noncomputable def triangularKacWardWeightDiagonal
    (t1 t2 t3 z1 z2 z3 : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  Matrix.diagonal ![t1 * z1, t1 * z1⁻¹, t2 * z2,
    t2 * z2⁻¹, t3 * z3, t3 * z3⁻¹]


noncomputable def triangularKacWardSymbolMatrix
    (t1 t2 t3 rho z1 z2 z3 : Complex) :
    Matrix (Fin 6) (Fin 6) Complex :=
  1 - triangularKacWardWeightDiagonal t1 t2 t3 z1 z2 z3 *
    triangularKacWardTurnMatrix rho

private noncomputable def triangularKacWardDiagonalSymbol
    (d0 d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 6) (Fin 6) Complex :=
  1 - Matrix.diagonal ![d0, d1, d2, d3, d4, d5] *
    triangularKacWardTurnMatrix rho

private noncomputable def triangularKacWardMinor0
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     -(d2 * rho ^ 2), 1 - d2, 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     d3 * rho ^ 6, 0, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 1 - d4, 0;
     d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 0, 1 - d5]

private noncomputable def triangularKacWardMinor1
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, 1 - d2, 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), 0, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho), d4 * rho ^ 5, 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 5, -(d5 * rho), 0, 1 - d5]

private noncomputable def triangularKacWardMinor2
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, -(d1 * rho ^ 2), d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 0, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 1 - d3, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), d4 * rho ^ 5, 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, -(d5 * rho), 0, 1 - d5]

private noncomputable def triangularKacWardMinor3
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, d1 * rho ^ 5, -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, d2 * rho ^ 7, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, -(d3 * rho ^ 3), d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), 1 - d4, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, 0, 1 - d5]

private noncomputable def triangularKacWardMinor4
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), -(d1 * rho);
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, 0, -(d2 * rho ^ 3);
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, 1 - d3, d3 * rho ^ 7;
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 0;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 1 - d5]

private noncomputable def triangularKacWardMinor5
    (d1 d2 d3 d4 d5 rho : Complex) : Matrix (Fin 5) (Fin 5) Complex :=
  !![0, 1 - d1, d1 * rho ^ 6, -(d1 * rho ^ 2), d1 * rho ^ 5;
     d2 * rho ^ 6, -(d2 * rho ^ 2), 1 - d2, 0, d2 * rho ^ 7;
     -(d3 * rho ^ 2), d3 * rho ^ 6, 0, 1 - d3, -(d3 * rho ^ 3);
     d4 * rho ^ 7, -(d4 * rho ^ 3), -(d4 * rho), d4 * rho ^ 5, 1 - d4;
     -(d5 * rho ^ 3), d5 * rho ^ 7, d5 * rho ^ 5, -(d5 * rho), 0]

private theorem triangularKacWardDiagonalSymbol_submatrix0
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (0 : Fin 6).succAbove =
        triangularKacWardMinor0 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor0, Fin.succAbove]

private theorem triangularKacWardDiagonalSymbol_submatrix1
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (1 : Fin 6).succAbove =
        triangularKacWardMinor1 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor1, Fin.succAbove]

private theorem triangularKacWardDiagonalSymbol_submatrix2
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (2 : Fin 6).succAbove =
        triangularKacWardMinor2 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor2, Fin.succAbove]

private theorem triangularKacWardDiagonalSymbol_submatrix3
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (3 : Fin 6).succAbove =
        triangularKacWardMinor3 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor3, Fin.succAbove]

private theorem triangularKacWardDiagonalSymbol_submatrix4
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (4 : Fin 6).succAbove =
        triangularKacWardMinor4 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor4, Fin.succAbove]

private theorem triangularKacWardDiagonalSymbol_submatrix5
    (d0 d1 d2 d3 d4 d5 rho : Complex) :
    (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).submatrix
      Fin.succ (5 : Fin 6).succAbove =
        triangularKacWardMinor5 d1 d2 d3 d4 d5 rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
      triangularKacWardMinor5, Fin.succAbove]

local macro "triangular_minor_det" r:term : term => `(by
  have hrho_local : $r ^ 4 = Complex.I := by assumption
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : $r ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho_local, hI]
  have hrho12 : $r ^ 12 = -Complex.I := by
    rw [show (12 : Nat) = 8 + 4 from rfl, pow_add, hrho8, hrho_local]
    ring
  have hrho9 : $r ^ 9 = -$r := by
    rw [show (9 : Nat) = 8 + 1 from rfl, pow_add, hrho8, pow_one]
    ring
  have hrho10 : $r ^ 10 = -($r ^ 2) := by
    rw [show (10 : Nat) = 8 + 2 from rfl, pow_add, hrho8]
    ring
  have hrho11 : $r ^ 11 = -($r ^ 3) := by
    rw [show (11 : Nat) = 8 + 3 from rfl, pow_add, hrho8]
    ring
  have hrho13 : $r ^ 13 = -($r * Complex.I) := by
    rw [show (13 : Nat) = 12 + 1 from rfl, pow_add, hrho12, pow_one]
    ring
  have hrho14 : $r ^ 14 = -($r ^ 2 * Complex.I) := by
    rw [show (14 : Nat) = 12 + 2 from rfl, pow_add, hrho12]
    ring
  have hrho15 : $r ^ 15 = -($r ^ 3 * Complex.I) := by
    rw [show (15 : Nat) = 12 + 3 from rfl, pow_add, hrho12]
    ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 from rfl, pow_add, hI, pow_one]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    rw [show (5 : Nat) = 4 + 1 from rfl, pow_add, hI4, pow_one, one_mul]
  have hrho5 : $r ^ 5 = $r * Complex.I := by
    rw [show (5 : Nat) = 1 + 4 from rfl, pow_add, hrho_local, pow_one]
  have hrho6 : $r ^ 6 = $r ^ 2 * Complex.I := by
    rw [show (6 : Nat) = 2 + 4 from rfl, pow_add, hrho_local]
  have hrho7 : $r ^ 7 = $r ^ 3 * Complex.I := by
    rw [show (7 : Nat) = 3 + 4 from rfl, pow_add, hrho_local]
  rw [Matrix.det_succ_row_zero]
  simp [triangularKacWardMinor0, triangularKacWardMinor1,
    triangularKacWardMinor2, triangularKacWardMinor3,
    triangularKacWardMinor4, triangularKacWardMinor5,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  try simp only [hrho5, hrho6, hrho7]
  simp only [@Matrix.det_succ_row_zero _ _ 3]
  simp [triangularKacWardMinor0, triangularKacWardMinor1,
    triangularKacWardMinor2, triangularKacWardMinor3,
    triangularKacWardMinor4, triangularKacWardMinor5,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.det_fin_three,
    Fin.succAbove]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring)

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor0_det
    (d1 d2 d3 d4 d5 rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor0 d1 d2 d3 d4 d5 rho).det =
      -d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 + 4 * d1 * d3 * d4 +
        d1 * d4 * d5 - d1 + d2 * d3 * d4 * d5 + d2 * d3 * d4 +
        d2 * d3 * d5 + d2 * d3 + d2 * d4 * d5 - d2 + d3 * d4 * d5 -
        d3 + d4 * d5 - d4 - d5 + 1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : rho ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho, hI]
  have hrho12 : rho ^ 12 = -Complex.I := by
    rw [show (12 : Nat) = 8 + 4 from rfl, pow_add, hrho8, hrho]
    ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 from rfl, pow_add, hI, pow_one]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    rw [show (5 : Nat) = 4 + 1 from rfl, pow_add, hI4, pow_one, one_mul]
  have hrho5 : rho ^ 5 = rho * Complex.I := by
    rw [show (5 : Nat) = 1 + 4 from rfl, pow_add, hrho, pow_one]
  have hrho6 : rho ^ 6 = rho ^ 2 * Complex.I := by
    rw [show (6 : Nat) = 2 + 4 from rfl, pow_add, hrho]
  have hrho7 : rho ^ 7 = rho ^ 3 * Complex.I := by
    rw [show (7 : Nat) = 3 + 4 from rfl, pow_add, hrho]
  rw [triangularKacWardMinor0, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  simp only [hrho5, hrho6, hrho7]
  simp only [@Matrix.det_succ_row_zero _ _ 3]
  simp [Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.det_fin_three,
    Fin.succAbove]
  ring_nf
  rw [hrho8, hrho12, hI3, hI4, hI5, hrho]
  ring_nf
  rw [hI]
  ring

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor1_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor1 d1 d2 d3 d4 d5 rho).det =
      rho ^ 4 *
        (-d1 * d2 * d3 * d4 + d1 * d2 * d3 * d5 - d1 * d2 * d4 * d5 +
          d1 * d2 + d1 * d3 * d4 * d5 - d1 * d3 + d1 * d4 - d1 * d5) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor2_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor2 d1 d2 d3 d4 d5 rho).det =
      rho ^ 6 *
        (d1 * d2 * d3 * d4 * d5 - 2 * d1 * d2 * d3 * d4 +
          d1 * d2 * d3 - d1 * d2 * d4 * d5 + d1 * d2 -
          d2 * d3 * d4 * d5 + d2 * d3 - d2 * d4 * d5 + 2 * d2 * d5 - d2) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor3_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor3 d1 d2 d3 d4 d5 rho).det =
      rho ^ 2 *
        (-d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 + d1 * d3 * d4 * d5 +
          2 * d1 * d3 * d4 + d1 * d3 + d2 * d3 * d4 * d5 +
          2 * d2 * d3 * d5 + d2 * d3 + d3 * d4 * d5 - d3) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor4_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor4 d1 d2 d3 d4 d5 rho).det =
      rho ^ 7 *
        (-d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 * d4 +
          2 * d1 * d3 * d4 + d1 * d4 * d5 + d1 * d4 +
          d2 * d3 * d4 * d5 + d2 * d3 * d4 + 2 * d2 * d4 * d5 +
          d4 * d5 - d4) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

private theorem triangularKacWardMinor5_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor5 d1 d2 d3 d4 d5 rho).det =
      rho ^ 3 *
        (d1 * d2 * d3 * d4 * d5 - d1 * d2 * d3 * d5 -
          2 * d1 * d3 * d4 * d5 + d1 * d4 * d5 + d1 * d5 -
          d2 * d3 * d4 * d5 - d2 * d3 * d5 + 2 * d2 * d5 +
          d4 * d5 - d5) :=
  triangular_minor_det rho

set_option maxHeartbeats 1000000 in

private theorem triangularKacWardTurnMatrix_diagonal_det
    (d0 d1 d2 d3 d4 d5 rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    (1 - Matrix.diagonal ![d0, d1, d2, d3, d4, d5] *
      triangularKacWardTurnMatrix rho).det =
      1 - (d0 + d1 + d2 + d3 + d4 + d5) +
        (d0 * d1 + d2 * d3 + d4 * d5) +
        d0 * d1 * (d2 + d3 + d4 + d5) +
        d2 * d3 * (d0 + d1 + d4 + d5) +
        d4 * d5 * (d0 + d1 + d2 + d3) +
        4 * (d0 * d2 * d5 + d1 * d3 * d4) +
        (d0 * d1 * d2 * d3 + d0 * d1 * d4 * d5 +
          d2 * d3 * d4 * d5) -
        (d1 * d2 * d3 * d4 * d5 + d0 * d2 * d3 * d4 * d5 +
          d0 * d1 * d3 * d4 * d5 + d0 * d1 * d2 * d4 * d5 +
          d0 * d1 * d2 * d3 * d5 + d0 * d1 * d2 * d3 * d4) +
        d0 * d1 * d2 * d3 * d4 * d5 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : rho ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho, hI]
  change (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).det = _
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by rfl,
    show Fin.succ (Fin.succ (2 : Fin 4)) = (4 : Fin 6) by rfl,
    show Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) = (5 : Fin 6) by rfl]
  rw [triangularKacWardDiagonalSymbol_submatrix0,
    triangularKacWardDiagonalSymbol_submatrix1,
    triangularKacWardDiagonalSymbol_submatrix2,
    triangularKacWardDiagonalSymbol_submatrix3,
    triangularKacWardDiagonalSymbol_submatrix4,
    triangularKacWardDiagonalSymbol_submatrix5,
    triangularKacWardMinor0_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor1_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor2_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor3_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor4_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor5_det _ _ _ _ _ _ hrho]
  simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
    Fin.succAbove]
  ring_nf
  rw [hrho8]
  ring




theorem triangularKacWardSymbolMatrix_det
    (t1 t2 t3 rho z1 z2 z3 : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0)
    (hzsum : z3 = z1 * z2) :
    (triangularKacWardSymbolMatrix t1 t2 t3 rho z1 z2 z3).det =
      (1 + t1 ^ 2) * (1 + t2 ^ 2) * (1 + t3 ^ 2) +
        8 * t1 * t2 * t3 -
        t1 * (1 - t2 ^ 2) * (1 - t3 ^ 2) * (z1 + z1⁻¹) -
        t2 * (1 - t1 ^ 2) * (1 - t3 ^ 2) * (z2 + z2⁻¹) -
        t3 * (1 - t1 ^ 2) * (1 - t2 ^ 2) * (z3 + z3⁻¹) := by
  subst z3
  rw [triangularKacWardSymbolMatrix, triangularKacWardWeightDiagonal,
    triangularKacWardTurnMatrix_diagonal_det _ _ _ _ _ _ _ hrho]
  field_simp [hz1, hz2, hz3]
  ring

end StatMech.FrontierA
