/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# One stage of the discrete LQR Riccati recursion

For a linear stage `x ↦ A x + B u` with state cost `xᵀQx`, input cost
`uᵀRu`, and next-stage value `xᵀPx` (all real matrices, `P ⪰ 0`,
`Q ⪰ 0`, `R ≻ 0` in the sense of `Matrix.PosSemidef`/`Matrix.PosDef`),
`riccatiStep A B P Q R = Q + AᵀPA - AᵀPB (R + BᵀPB)⁻¹ BᵀPA` is the
one-step Riccati update. The gain denominator `R + BᵀPB` is positive
definite (`posDef_R_add_transpose_mul_mul`), the completing-the-square
identity

`xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu) = xᵀP'x + (u + Kx)ᵀ(R + BᵀPB)(u + Kx)`

with `K = (R + BᵀPB)⁻¹ BᵀPA` holds for every state `x` and input `u`
(`complete_square`), and the update stays positive semidefinite
(`riccatiStep_posSemidef`): at `u = -Kx` the square term vanishes, so
`xᵀP'x` is the minimum of the stage cost, a sum of nonnegative terms.
Quadratic forms are written `x ⬝ᵥ M *ᵥ x`. Only one stage is treated
here; finite-horizon iteration and the infinite horizon are separate.

Provenance: the standard LQR dynamic-programming square completion;
control-theory roadmap leaf `SSC-U21.T01` (clauses `SSC-U21.c01`,
`SSC-U21.c02`).
-/

open Matrix

@[expose] public section

namespace ControlTheory

/-- One step of the discrete LQR Riccati recursion: for state matrix `A`,
input matrix `B`, stage costs `Q` (state) and `R` (input), and next-stage
cost matrix `P`,
`riccatiStep A B P Q R = Q + AᵀPA - AᵀPB (R + BᵀPB)⁻¹ BᵀPA`
(roadmap leaf `SSC-U21.T01`). -/
noncomputable def riccatiStep {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (P Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) : Matrix n n ℝ :=
  Q + Aᵀ * P * A - Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A

private theorem transpose_eq_of_posSemidef {n : Type*} [Fintype n]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) : Pᵀ = P := by
  have hH : Pᴴ = P := hP.isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  exact hH

private theorem transpose_eq_of_posDef {n : Type*} [Fintype n]
    {R : Matrix n n ℝ} (hR : R.PosDef) : Rᵀ = R := by
  have hH : Rᴴ = R := hR.isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  exact hH

private theorem transpose_S {n m : Type*} [Fintype n] [Fintype m]
    {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) : (R + Bᵀ * P * B)ᵀ = R + Bᵀ * P * B := by
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hP, hR,
    Matrix.mul_assoc]

private theorem transpose_inv_S {m : Type*} [Fintype m] [DecidableEq m]
    {S : Matrix m m ℝ} (hS : Sᵀ = S) : (S⁻¹)ᵀ = S⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hS]

private theorem mulVec_eq_vecMul_transpose {n m : Type*} [Fintype m]
    (M : Matrix n m ℝ) (x : m → ℝ) : M *ᵥ x = x ᵥ* Mᵀ := by
  rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose]

private theorem dot_move_left {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (M : Matrix n m ℝ) (N : Matrix n p ℝ) (x : m → ℝ) (y : p → ℝ) :
    (M *ᵥ x) ⬝ᵥ N *ᵥ y = x ⬝ᵥ (Mᵀ * N) *ᵥ y := by
  rw [mulVec_eq_vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec]

private theorem dot_move_right {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]
    (N : Matrix n p ℝ) (M : Matrix p q ℝ) (x : n → ℝ) (y : q → ℝ) :
    x ⬝ᵥ N *ᵥ (M *ᵥ y) = x ⬝ᵥ (N * M) *ᵥ y := by
  rw [Matrix.mulVec_mulVec]

private theorem dot_move_both {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p]
    [Fintype q]
    (M : Matrix n m ℝ) (N : Matrix n p ℝ) (L : Matrix p q ℝ) (x : m → ℝ)
    (y : q → ℝ) :
    (M *ᵥ x) ⬝ᵥ N *ᵥ (L *ᵥ y) = x ⬝ᵥ (Mᵀ * N * L) *ᵥ y := by
  rw [dot_move_left, dot_move_right]

private theorem key_SK {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hSS : (R + Bᵀ * P * B) * (R + Bᵀ * P * B)⁻¹ = 1) :
    (R + Bᵀ * P * B) * ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) = Bᵀ * P * A := by
  have h : (R + Bᵀ * P * B) * ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)
      = ((R + Bᵀ * P * B) * (R + Bᵀ * P * B)⁻¹) * (Bᵀ * P * A) := by
    simp only [Matrix.mul_assoc]
  rw [h, hSS, Matrix.one_mul]

private theorem key_KT {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hSi : ((R + Bᵀ * P * B)⁻¹)ᵀ = (R + Bᵀ * P * B)⁻¹) :
    ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ
      = Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP, hSi]
  simp only [Matrix.mul_assoc]

private theorem key_KS {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hKT : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ
      = Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹)
    (hSiS : (R + Bᵀ * P * B)⁻¹ * (R + Bᵀ * P * B) = 1) :
    ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B) = Aᵀ * P * B := by
  have h : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B)
      = Aᵀ * P * B * ((R + Bᵀ * P * B)⁻¹ * (R + Bᵀ * P * B)) := by
    rw [hKT]
    simp only [Matrix.mul_assoc]
  rw [h, hSiS, Matrix.mul_one]

private theorem key_KSK {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hKS : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B)
      = Aᵀ * P * B) :
    ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B)
        * ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)
      = Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A := by
  rw [hKS]
  simp only [Matrix.mul_assoc]

/-- The gain matrix denominator is positive definite: for `P ⪰ 0` and
`R ≻ 0`, `R + BᵀPB ≻ 0` (roadmap leaf `SSC-U21.T01`). -/
theorem posDef_R_add_transpose_mul_mul {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {B : Matrix n m ℝ} {P : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : P.PosSemidef) (hR : R.PosDef) :
    (R + Bᵀ * P * B).PosDef := by
  have hBTB : (Bᴴ * P * B).PosSemidef := hP.conjTranspose_mul_mul_same B
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hBTB
  exact hR.add_posSemidef hBTB

/-- Completing the square for one LQR stage: for `P ⪰ 0`, `Q ⪰ 0`,
`R ≻ 0`, with gain `K = (R + BᵀPB)⁻¹ BᵀPA` and `P' = riccatiStep A B P Q R`,
every state `x` and input `u` satisfy
`xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu) = xᵀP'x + (u + Kx)ᵀ(R + BᵀPB)(u + Kx)`
(roadmap leaf `SSC-U21.T01`, clauses `SSC-U21.c01`, `SSC-U21.c02`).
Quadratic forms are written `x ⬝ᵥ M *ᵥ x`. -/
theorem complete_square {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P Q : Matrix n n ℝ}
    {R : Matrix m m ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosDef)
    (x : n → ℝ) (u : m → ℝ) :
    x ⬝ᵥ Q *ᵥ x + u ⬝ᵥ R *ᵥ u
        + (A *ᵥ x + B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ u)
      = x ⬝ᵥ (riccatiStep A B P Q R) *ᵥ x
        + (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
          ⬝ᵥ (R + Bᵀ * P * B) *ᵥ (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) := by
  have hS : (R + Bᵀ * P * B).PosDef := posDef_R_add_transpose_mul_mul hP hR
  have hdet : IsUnit (R + Bᵀ * P * B).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hSS : (R + Bᵀ * P * B) * (R + Bᵀ * P * B)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hSiS : (R + Bᵀ * P * B)⁻¹ * (R + Bᵀ * P * B) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hPt : Pᵀ = P := transpose_eq_of_posSemidef hP
  have hRt : Rᵀ = R := transpose_eq_of_posDef hR
  have hSt : (R + Bᵀ * P * B)ᵀ = R + Bᵀ * P * B := transpose_S hPt hRt
  have hSit : ((R + Bᵀ * P * B)⁻¹)ᵀ = (R + Bᵀ * P * B)⁻¹ := transpose_inv_S hSt
  have hKT : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ
      = Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ := key_KT hPt hSit
  have hKS : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B)
      = Aᵀ * P * B := key_KS hKT hSiS
  have hSK : (R + Bᵀ * P * B) * ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)
      = Bᵀ * P * A := key_SK hSS
  have hKSK : ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)ᵀ * (R + Bᵀ * P * B)
        * ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A)
      = Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A := key_KSK hKS
  have t1 : (A *ᵥ x) ⬝ᵥ P *ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᵀ * P * A) *ᵥ x :=
    dot_move_both A P A x x
  have t2 : (A *ᵥ x) ⬝ᵥ P *ᵥ (B *ᵥ u) = x ⬝ᵥ (Aᵀ * P * B) *ᵥ u :=
    dot_move_both A P B x u
  have t3 : (B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x) = u ⬝ᵥ (Bᵀ * P * A) *ᵥ x :=
    dot_move_both B P A u x
  have t4 : (B *ᵥ u) ⬝ᵥ P *ᵥ (B *ᵥ u) = u ⬝ᵥ (Bᵀ * P * B) *ᵥ u :=
    dot_move_both B P B u u
  have v1 : u ⬝ᵥ (R + Bᵀ * P * B) *ᵥ u
      = u ⬝ᵥ R *ᵥ u + u ⬝ᵥ (Bᵀ * P * B) *ᵥ u := by
    rw [Matrix.add_mulVec, dotProduct_add]
  have v2 : u ⬝ᵥ (R + Bᵀ * P * B) *ᵥ (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
      = u ⬝ᵥ (Bᵀ * P * A) *ᵥ x := by
    rw [dot_move_right, hSK]
  have v3 : (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) ⬝ᵥ (R + Bᵀ * P * B) *ᵥ u
      = x ⬝ᵥ (Aᵀ * P * B) *ᵥ u := by
    rw [dot_move_left, hKS]
  have v4 : (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) ⬝ᵥ (R + Bᵀ * P * B) *ᵥ
        (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
      = x ⬝ᵥ (Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x := by
    rw [dot_move_both, hKSK]
  have hP' : x ⬝ᵥ (riccatiStep A B P Q R) *ᵥ x
      = x ⬝ᵥ Q *ᵥ x + x ⬝ᵥ (Aᵀ * P * A) *ᵥ x
        - x ⬝ᵥ (Aᵀ * P * B * (R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x := by
    unfold riccatiStep
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
  have hT : (A *ᵥ x + B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ u)
      = (A *ᵥ x) ⬝ᵥ P *ᵥ (A *ᵥ x) + (A *ᵥ x) ⬝ᵥ P *ᵥ (B *ᵥ u)
        + ((B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x) + (B *ᵥ u) ⬝ᵥ P *ᵥ (B *ᵥ u)) := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  have hV : (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) ⬝ᵥ (R + Bᵀ * P * B) *ᵥ
        (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
      = u ⬝ᵥ (R + Bᵀ * P * B) *ᵥ u
        + u ⬝ᵥ (R + Bᵀ * P * B) *ᵥ (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
        + ((((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) ⬝ᵥ (R + Bᵀ * P * B) *ᵥ u
          + (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) ⬝ᵥ (R + Bᵀ * P * B) *ᵥ
            (((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)) := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  rw [hT, hV, hP', t1, t2, t3, t4, v1, v2, v3, v4]
  ring

/-- The Riccati step preserves positive semidefiniteness: for `P ⪰ 0`,
`Q ⪰ 0`, `R ≻ 0`, the matrix `riccatiStep A B P Q R` is positive
semidefinite, since by `complete_square` at `u = -Kx` its quadratic form
is a sum of the three nonnegative stage terms (roadmap leaf
`SSC-U21.T01`). -/
theorem riccatiStep_posSemidef {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P Q : Matrix n n ℝ}
    {R : Matrix m m ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosDef) :
    (riccatiStep A B P Q R).PosSemidef := by
  have hPt : Pᵀ = P := transpose_eq_of_posSemidef hP
  have hQt : Qᵀ = Q := transpose_eq_of_posSemidef hQ
  have hRt : Rᵀ = R := transpose_eq_of_posDef hR
  have hSt : (R + Bᵀ * P * B)ᵀ = R + Bᵀ * P * B := transpose_S hPt hRt
  have hSit : ((R + Bᵀ * P * B)⁻¹)ᵀ = (R + Bᵀ * P * B)⁻¹ := transpose_inv_S hSt
  have hRT : (riccatiStep A B P Q R)ᵀ = riccatiStep A B P Q R := by
    simp only [riccatiStep, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPt, hQt, hSit]
    simp only [Matrix.mul_assoc]
  have hRH : (riccatiStep A B P Q R).IsHermitian := by
    show (riccatiStep A B P Q R)ᴴ = riccatiStep A B P Q R
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hRT]
  have hnn : ∀ x : n → ℝ, 0 ≤ star x ⬝ᵥ ((riccatiStep A B P Q R) *ᵥ x) := by
    intro x
    rw [star_trivial]
    set u : m → ℝ := -(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) with hu
    have hcs := complete_square (A := A) (B := B) hP hQ hR x u
    have hzero : u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x = 0 := by
      rw [hu]
      exact neg_add_cancel _
    rw [hzero, Matrix.mulVec_zero, dotProduct_zero, add_zero] at hcs
    have h1 : 0 ≤ x ⬝ᵥ Q *ᵥ x := by
      have h := hQ.dotProduct_mulVec_nonneg x
      rwa [star_trivial] at h
    have h2 : 0 ≤ u ⬝ᵥ R *ᵥ u := by
      have h := hR.posSemidef.dotProduct_mulVec_nonneg u
      rwa [star_trivial] at h
    have h3 : 0 ≤ (A *ᵥ x + B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ u) := by
      have h := hP.dotProduct_mulVec_nonneg (A *ᵥ x + B *ᵥ u)
      rwa [star_trivial] at h
    rw [← hcs]
    exact add_nonneg (add_nonneg h1 h2) h3
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hRH hnn

end ControlTheory
