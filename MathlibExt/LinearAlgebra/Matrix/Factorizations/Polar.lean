/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import MathlibExt.LinearAlgebra.Matrix.Factorizations.SVD

/-!
# Polar decomposition

Every square complex matrix admits a polar decomposition, derived from the singular value
decomposition: if `A = U * D * star V`, then `A = (U * star V) * (V * D * star V)`.
The result is `Matrix.exists_unitaryGroup_posSemidef`. For an invertible square matrix over an
`RCLike` field, `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` gives the unique
unitary-positive-definite polar decomposition.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
**Polar decomposition of a complex square matrix.** Let $A$ be a square complex matrix indexed by
a finite type, and let $A^*$ be its conjugate transpose. Then there are a unitary matrix $U$ and a
positive semidefinite matrix $P$ such that $P^2 = A^* A$ and $A = UP$.

Source: R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013).
Proves `Wanted` entry `polar_decomposition`, restated over `Matrix.unitaryGroup` in place of the
entry's `IsUnitaryMatrix`.
-/
theorem exists_unitaryGroup_posSemidef (A : Matrix n n ℂ) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ),
      P.PosSemidef ∧ P * P = Aᴴ * A ∧ A = (U : Matrix n n ℂ) * P := by
  obtain ⟨U, V, σ, hσ, hA⟩ := exists_unitaryGroup_diagonal_nonneg A
  set D : Matrix n n ℂ := diagonal fun i => (σ i : ℂ)
  have hD : D.PosSemidef := PosSemidef.diagonal fun i => Complex.zero_le_real.2 (hσ i)
  have hDs : star D = D := by
    simp [D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  have hU : ∀ X : Matrix n n ℂ, star (U : Matrix n n ℂ) * (U * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 U.2, one_mul]
  have hV : ∀ X : Matrix n n ℂ, star (V : Matrix n n ℂ) * (V * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 V.2, one_mul]
  refine ⟨U * star V, V * D * star (V : Matrix n n ℂ), ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same (V : Matrix n n ℂ)
  · rw [hA, ← Matrix.star_eq_conjTranspose]
    simp only [star_mul, star_star, hDs, mul_assoc, hU, hV]
  · rw [hA, Submonoid.coe_mul, Unitary.coe_star]
    simp only [mul_assoc, hV]

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]

private theorem polar_posDef_conjTranspose_mul_self [DecidableEq n] (A : Matrix n n 𝕜)
    (hA : IsUnit A.det) : (Aᴴ * A).PosDef :=
  PosDef.conjTranspose_mul_self A <|
    mulVec_injective_iff_isUnit.mpr <| (isUnit_iff_isUnit_det A).mpr hA

open scoped MatrixOrder Classical in
private theorem polar_posDef_sqrt {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    (CFC.sqrt Q).PosDef := by
  exact isStrictlyPositive_iff_posDef.mp hQ.isStrictlyPositive.sqrt

open scoped MatrixOrder Classical in
private theorem polar_sqrt_mul_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    CFC.sqrt Q * CFC.sqrt Q = Q :=
  CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg

private theorem polar_mul_inv_mem_unitaryGroup [DecidableEq n]
    {A P : Matrix n n 𝕜} (hP : P.PosDef) (hsq : P * P = Aᴴ * A) :
    A * P⁻¹ ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  simp only [star_mul, star_eq_conjTranspose, conjTranspose_nonsing_inv,
    hP.isHermitian.eq]
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    (P⁻¹ * Aᴴ) * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by simp only [mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [← hsq]
    _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul P hPdet, mul_nonsing_inv P hPdet, one_mul]

open scoped MatrixOrder Classical in
private theorem polar_eq_sqrt_of_posDef_sq {P Q : Matrix n n 𝕜} (hP : P.PosDef)
    (hsq : P * P = Q) : P = CFC.sqrt Q :=
  (CFC.sqrt_unique hsq hP.posSemidef.nonneg).symm

private theorem polar_mul_inv_mul [DecidableEq n] {A P : Matrix n n 𝕜} (hP : P.PosDef) :
    A = (A * P⁻¹) * P := by
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    A = A * 1 := (mul_one A).symm
    _ = A * (P⁻¹ * P) := by rw [nonsing_inv_mul P hPdet]
    _ = (A * P⁻¹) * P := (mul_assoc _ _ _).symm

private theorem polar_sq_eq_conjTranspose_mul_self [DecidableEq n]
    {A U P : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (hP : P.PosDef)
    (hA : A = U * P) : P * P = Aᴴ * A := by
  have hUconj : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  calc
    P * P = P * (Uᴴ * U) * P := by rw [hUconj, mul_one]
    _ = (U * P)ᴴ * (U * P) := by
      rw [conjTranspose_mul, hP.isHermitian.eq]
      simp only [mul_assoc]
    _ = Aᴴ * A := by rw [← hA]

open scoped MatrixOrder in
/-- **Uniqueness of the polar decomposition of an invertible matrix.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and let $A$ be a square matrix over $\mathbb{K}$, indexed by a finite
type, with $\det A \neq 0$. Then there are a unitary matrix $U$ and a positive-definite matrix $P$
with $A = UP$, and they are unique: if $U'$ is unitary, $P'$ is positive definite and
$A = U'P'$, then $U' = U$ and $P' = P$. -/
theorem exists_unique_unitaryGroup_posDef_of_isUnit_det [DecidableEq n]
    (A : Matrix n n 𝕜) (hA : IsUnit A.det) :
    ∃ (U : Matrix.unitaryGroup n 𝕜) (P : Matrix n n 𝕜),
      P.PosDef ∧ A = (U : Matrix n n 𝕜) * P ∧
        ∀ (U' : Matrix.unitaryGroup n 𝕜) (P' : Matrix n n 𝕜),
          P'.PosDef → A = (U' : Matrix n n 𝕜) * P' → U' = U ∧ P' = P := by
  let Q := Aᴴ * A
  let P := CFC.sqrt Q
  let U := A * P⁻¹
  have hQ : Q.PosDef := by
    simpa only [Q] using polar_posDef_conjTranspose_mul_self A hA
  have hP : P.PosDef := by
    simpa only [P] using polar_posDef_sqrt hQ
  have hPsq : P * P = Aᴴ * A := by
    simpa only [P, Q] using polar_sqrt_mul_self hQ
  have hU : U ∈ unitaryGroup n 𝕜 := by
    simpa only [U] using polar_mul_inv_mem_unitaryGroup hP hPsq
  have hdecomp : A = U * P := by
    simpa only [U] using polar_mul_inv_mul hP
  refine ⟨⟨U, hU⟩, P, hP, hdecomp, ?_⟩
  intro U' P' hP' hdecomp'
  have hP'eq : P' = P := by
    apply polar_eq_sqrt_of_posDef_sq hP'
    simpa only [P, Q] using
      polar_sq_eq_conjTranspose_mul_self U'.property hP' hdecomp'
  have hU'eq : (U' : Matrix n n 𝕜) = U := by
    apply hP.isUnit.mul_right_cancel
    calc
      (U' : Matrix n n 𝕜) * P = U' * P' := by rw [hP'eq]
      _ = A := hdecomp'.symm
      _ = U * P := hdecomp
  exact ⟨Subtype.ext hU'eq, hP'eq⟩

end Matrix
