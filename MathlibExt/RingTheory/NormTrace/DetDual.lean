/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`
and
`P2M/Sol/S_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Determinant of a scaled dual pairing

For a basis `b` of a commutative algebra `A` over `R`, a linear form
`τ` on `A`, and `c : A`, scaling the first factor in the pairing
`(i, j) ↦ τ (b i * b j)` by `c` multiplies its determinant by the
norm of `c`. Column `i` of `Algebra.leftMulMatrix b c` holds the
coordinates of `c * b i`, so the scaled matrix is
`(Algebra.leftMulMatrix b c).transpose * U`, where `U` is the unscaled
matrix (Mathlib's `LinearMap.toMatrix₂_comp` for the pairing
`(x, y) ↦ τ (x * y)`), and transposing does not change the determinant.
-/

@[expose] public section

open Module

private theorem of_dual_mul_mul_eq {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R A)
    (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)) =
      (Algebra.leftMulMatrix b c).transpose * Matrix.of fun i j => τ (b i * b j) := by
  ext i j
  simpa [Matrix.mul_apply, Algebra.leftMulMatrix_apply] using
    congrFun₂ (LinearMap.toMatrix₂_comp b b b ((LinearMap.mul R A).compr₂ τ)
      (Algebra.lmul R A c)) i j

/-- **Determinant of a scaled dual pairing.** Let $R$ be a commutative ring, $A$ a
commutative $R$-algebra with a basis $(b_i)_{i \in \iota}$ indexed by a finite type $\iota$,
$\tau \colon A \to R$ an $R$-linear form, and $c \in A$. Then

$$\det\bigl(\tau(c\, b_i b_j)\bigr)_{i,j} = N_{A/R}(c)\,\det\bigl(\tau(b_i b_j)\bigr)_{i,j},$$

where $N_{A/R}(c)$, the norm of $c$, is the determinant of multiplication by $c$. Column $i$
of the matrix $L_c$ of that multiplication in the basis $b$ holds the coordinates of
$c\, b_i$, so the left-hand matrix is $L_c^{\top}$ times $\bigl(\tau(b_i b_j)\bigr)_{i,j}$,
and $\det L_c^{\top} = \det L_c = N_{A/R}(c)$. -/
theorem Algebra.det_dual_mul_mul_eq_norm_mul_det (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det =
      Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by
  rw [of_dual_mul_mul_eq b τ c, Matrix.det_mul, Matrix.det_transpose,
    Algebra.norm_eq_matrix_det b]
