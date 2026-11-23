/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Real quadratic forms under congruence

The quadratic form of a real square matrix under the congruence `A ↦ Uᵀ * A * U`, its orthogonal
invariants, an explicit `2 × 2` positivity criterion, and the degenerate case.

## i. Overview

For a real matrix `A : Matrix n n ℝ` over a finite index type `n`, `quadForm A x` is the
quadratic form `Q_A(x) = x ⬝ᵥ (A *ᵥ x)`. A change of variables by any square matrix `U` acts on
matrices by the congruence `A ↦ Uᵀ * A * U`, and `Q_{Uᵀ A U}(x) = Q_A(U x)` holds without any
orthogonality hypothesis. Congruence maps symmetric matrices to symmetric matrices. When `U` is
orthogonal, `U ∈ Matrix.orthogonalGroup n ℝ` (equivalently `Uᵀ * U = 1`, or `U * Uᵀ = 1`, by
`Matrix.mem_orthogonalGroup_iff'` and `Matrix.mem_orthogonalGroup_iff`), the congruence is a
similarity, so it preserves the trace and the determinant.

For the symmetric `2 × 2` matrix `!![a, b; b, d]` the form is `a x₀² + 2 b x₀ x₁ + d x₁²`.
Completing the square gives `a Q(x) = (a x₀ + b x₁)² + (a d - b²) x₁²`, so the explicit
inequalities `0 < a` and `0 < a * d - b ^ 2` make the matrix positive definite in the sense of
`Matrix.PosDef`. Degeneracy is stated separately: if `A *ᵥ v = 0` then `Q_A(v) = 0`, so a matrix
with a nonzero kernel vector is not positive definite.

Interpretation, not proved here: a rotated frame acts by orthogonal congruence on a
symmetric `3 × 3` tensor, and the principal stresses are the eigenvalues of the stress
tensor `σ`, so trace and determinant invariance is the
invariant part of this slice: the trace is the sum of the principal stresses
(`Matrix.IsHermitian.trace_eq_sum_eigenvalues`) and the determinant is their product
(`Matrix.IsHermitian.det_eq_prod_eigenvalues`). Invariance of the full eigenvalue multiset is not
claimed. The invariance of the eigenvalue sign counts under invertible congruence
(`IsUnit P.det` in `MetaMathlibExt.sylvester_law_of_inertia`), in particular under the orthogonal
congruences above, is Sylvester's law of inertia, not re-proved here. A symmetric `2 × 2`
Hamiltonian has real eigenvalues with orthogonal eigenvectors by Mathlib's
`Matrix.IsHermitian.spectral_theorem`; the tests check the eigenpairs of `!![2, 1; 1, 2]`
directly. For the symmetric Hessian `H` of a function, `Q_H(h) / 2` is the second-order term of
its Taylor expansion; no derivative is identified here.

The results are algebraic over `ℝ`. They prove no spectral theorem, no general Sylvester
criterion or law of inertia, and no orthogonal diagonalization of symmetric matrices (that is
Mathlib's `Matrix.IsHermitian.spectral_theorem`). Nonnegativity of a physical energy is claimed
only under the stated inequalities, and a singular constitutive matrix is not claimed to describe
a real material.

Reuse-verified against Mathlib/Physlib/ATLAS main; no ATLAS-50 prerequisite PR dependency.

## ii. Key results

- `quadForm` : the quadratic form `x ⬝ᵥ (A *ᵥ x)` of a real square matrix.
- `quadForm_congr` : `quadForm (Uᵀ * A * U) x = quadForm A (U *ᵥ x)`.
- `IsSymm_congr` : congruence preserves symmetry.
- `trace_congr_of_mem_orthogonalGroup` : orthogonal congruence preserves the trace.
- `det_congr_of_mem_orthogonalGroup` : orthogonal congruence preserves the determinant.
- `quadForm_two_by_two` : the quadratic form of `!![a, b; b, d]`.
- `posDef_two_by_two_of_pos` : `0 < a` and `0 < a * d - b ^ 2` make `!![a, b; b, d]` positive
  definite.
- `quadForm_eq_zero_of_mulVec_eq_zero` : the quadratic form vanishes on the kernel.
- `not_posDef_of_mulVec_eq_zero` : a nonzero kernel vector rules out positive definiteness.

## iii. Table of contents

- A. The quadratic form of a real matrix
- B. Congruence
  - B.1. The quadratic form under congruence
  - B.2. Symmetry under congruence
  - B.3. Orthogonal congruence invariants
- C. Symmetric `2 × 2` matrices
  - C.1. The quadratic form of a symmetric `2 × 2` matrix
  - C.2. Positive definiteness from explicit inequalities
- D. Degeneracy

## iv. References

- ATLAS roadmap, module MF03 (foundations, core).
- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  Chapter 4 (Hermitian matrices, symmetric matrices, and congruences) and Chapter 7 (positive
  definite and semidefinite matrices).
- Reused, not re-proved: Mathlib's `Matrix.IsSymm`, `Matrix.IsHermitian`, `Matrix.PosDef`,
  `Matrix.orthogonalGroup` and `Matrix.IsHermitian.spectral_theorem`; ATLAS's Sylvester criterion
  `Matrix.posDef_iff_leadingPrincipalMinors_pos`
  (`MathlibExt.LinearAlgebra.Matrix.SylvesterCriterion`), law of inertia
  `MetaMathlibExt.sylvester_law_of_inertia` (`MathlibExt.LinearAlgebra.Matrix.SylvesterInertia`)
  and normal spectral theorem `Matrix.exists_unitary_diagonal_of_isStarNormal`
  (`MathlibExt.Analysis.Matrix.NormalSpectralTheorem`).
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence

/-!

## A. The quadratic form of a real matrix

-/

/-- The quadratic form `Q_A(x) = x ⬝ᵥ (A *ᵥ x)` of a real square matrix `A`. It has the same values
as Mathlib's `Matrix.toQuadraticForm' A`, which bundles the form as a `QuadraticForm` and needs
`DecidableEq n`; this file keeps the plain real-valued function under its MF03 name. -/
def quadForm {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-!

## B. Congruence

### B.1. The quadratic form under congruence

-/

/-- Congruence by any square matrix `U` is a change of variables in the quadratic form,
`Q_{Uᵀ A U}(x) = Q_A(U x)`. Neither orthogonality nor invertibility of `U` is needed. -/
lemma quadForm_congr {n : Type*} [Fintype n] (A U : Matrix n n ℝ) (x : n → ℝ) :
    quadForm (Uᵀ * A * U) x = quadForm A (U *ᵥ x) := by
  rw [quadForm, quadForm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-!

### B.2. Symmetry under congruence

-/

/-- Congruence by any square matrix maps symmetric matrices to symmetric matrices. This is the
real case of Mathlib's `Matrix.isHermitian_conjTranspose_mul_mul`, to which the proof reduces. -/
lemma IsSymm_congr {n : Type*} [Fintype n] (A U : Matrix n n ℝ) :
    A.IsSymm → (Uᵀ * A * U).IsSymm := by
  intro hA
  have h := isHermitian_conjTranspose_mul_mul U (isHermitian_iff_isSymm.2 hA)
  rwa [conjTranspose_eq_transpose_of_trivial, isHermitian_iff_isSymm] at h

/-!

### B.3. Orthogonal congruence invariants

-/

/-- Orthogonal congruence preserves the trace. Membership `U ∈ Matrix.orthogonalGroup n ℝ` is
Mathlib's encoding of `Uᵀ * U = 1` and `U * Uᵀ = 1`; the proof uses `U * Uᵀ = 1`. -/
lemma trace_congr_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    (σ U : Matrix n n ℝ) (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    Matrix.trace (Uᵀ * σ * U) = Matrix.trace σ := by
  rw [trace_mul_cycle, (mem_orthogonalGroup_iff n ℝ).1 hU, Matrix.one_mul]

/-- Orthogonal congruence preserves the determinant. The proof uses `Uᵀ * U = 1`, so that
`det Uᵀ * det U = 1`. -/
lemma det_congr_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    (σ U : Matrix n n ℝ) (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    Matrix.det (Uᵀ * σ * U) = Matrix.det σ := by
  have h := congrArg det ((mem_orthogonalGroup_iff' n ℝ).1 hU)
  rw [det_mul, det_one] at h
  rw [det_mul, det_mul, mul_right_comm, h, one_mul]

/-!

## C. Symmetric `2 × 2` matrices

### C.1. The quadratic form of a symmetric `2 × 2` matrix

-/

/-- The quadratic form of the symmetric matrix `!![a, b; b, d]` at `![x₀, x₁]` is
`a x₀² + 2 b x₀ x₁ + d x₁²`. -/
lemma quadForm_two_by_two (a b d x₀ x₁ : ℝ) :
    quadForm !![a, b; b, d] ![x₀, x₁] = a * x₀ ^ 2 + 2 * b * x₀ * x₁ + d * x₁ ^ 2 := by
  simp [quadForm, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-!

### C.2. Positive definiteness from explicit inequalities

-/

/-- Completing the square, `a (a x₀² + 2 b x₀ x₁ + d x₁²) = (a x₀ + b x₁)² + (a d - b²) x₁²`, so
the binary form is positive at every nonzero point when `0 < a` and `0 < a * d - b ^ 2`. -/
private lemma two_by_two_pos {a b d x₀ x₁ : ℝ} (ha : 0 < a) (hdet : 0 < a * d - b ^ 2)
    (hx : x₀ ≠ 0 ∨ x₁ ≠ 0) : 0 < a * x₀ ^ 2 + 2 * b * x₀ * x₁ + d * x₁ ^ 2 := by
  rcases eq_or_ne x₁ 0 with rfl | h₁
  · have h₀ : x₀ ≠ 0 := by simpa using hx
    have h : 0 < a * x₀ ^ 2 := by positivity
    linarith
  · have hsq : a * (a * x₀ ^ 2 + 2 * b * x₀ * x₁ + d * x₁ ^ 2) =
        (a * x₀ + b * x₁) ^ 2 + (a * d - b ^ 2) * x₁ ^ 2 := by
      ring
    have h : 0 < (a * d - b ^ 2) * x₁ ^ 2 := mul_pos hdet (by positivity)
    refine (mul_pos_iff_of_pos_left ha).1 ?_
    rw [hsq]
    linarith [sq_nonneg (a * x₀ + b * x₁)]

/-- Explicit constitutive inequalities for a symmetric `2 × 2` matrix: if `0 < a` and
`0 < a * d - b ^ 2`, then `!![a, b; b, d]` is positive definite. The two inequalities say that the
leading principal minors `a` and `a * d - b ^ 2 = det` are positive, so this is the `2 × 2`
instance of the sufficiency direction of the ATLAS Sylvester criterion
`Matrix.posDef_iff_leadingPrincipalMinors_pos`. That module is not imported; the proof completes
the square in the expansion `quadForm_two_by_two` instead. -/
lemma posDef_two_by_two_of_pos (a b d : ℝ) (ha : 0 < a) (hdet : 0 < a * d - b ^ 2) :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hx' : x = ![x 0, x 1] := by
      ext i
      fin_cases i <;> rfl
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    have h := two_by_two_pos ha hdet hne
    rw [← quadForm_two_by_two, ← hx'] at h
    rw [star_trivial]
    exact h

/-!

## D. Degeneracy

-/

/-- The quadratic form vanishes on the kernel: if `A *ᵥ v = 0` then `quadForm A v = 0`. The
hypothesis `v ≠ 0` of the degeneracy statement is not needed for this half. -/
lemma quadForm_eq_zero_of_mulVec_eq_zero {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (v : n → ℝ) (hv : A *ᵥ v = 0) : quadForm A v = 0 := by
  rw [quadForm, hv, dotProduct_zero]

/-- Degeneracy rules out positive definiteness: a nonzero `v` with `A *ᵥ v = 0` has
`quadForm A v = 0`, whereas `Matrix.PosDef.dotProduct_mulVec_pos` would make it positive. -/
lemma not_posDef_of_mulVec_eq_zero {n : Type*} [Fintype n] (A : Matrix n n ℝ) (v : n → ℝ)
    (hv : A *ᵥ v = 0) (hne : v ≠ 0) : ¬ A.PosDef := by
  intro hA
  have hpos := hA.dotProduct_mulVec_pos hne
  rw [star_trivial] at hpos
  exact hpos.ne' (quadForm_eq_zero_of_mulVec_eq_zero A v hv)

end MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence
