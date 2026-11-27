/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Spectral reciprocal and support of finite Hermitian matrices

For any square matrix over `ℝ` or `ℂ` with finite index type `n`, apply
real continuous functional calculus to `x ↦ x⁻¹` and to the zero-or-one
nonzero-eigenvalue indicator. On a Hermitian matrix these give the spectral
pseudoinverse and its support projection. Real inversion is total, with
`0⁻¹ = 0`, so zero eigenspaces are annihilated. The finite real spectrum
makes both scalar functions continuous on that spectrum. Outside the
Hermitian predicate the total functional-calculus definitions have value zero.

Both resulting matrices are Hermitian; the support is idempotent. For a
Hermitian input, multiplying by the spectral reciprocal on either side gives
the support, and all four Moore–Penrose equations hold. Singular matrices,
zero matrices and an empty finite index type retain the same definitions.
Conjugate transpose, matrix multiplication and Euclidean coordinate structures
are the stated real-or-complex ones.

## References

The four equations are those of Theorem 1 in R. Penrose, “A generalized inverse for matrices”,
*Mathematical Proceedings of the Cambridge Philosophical Society* 51(3) (1955), 406–413. The
theorem gives existence and uniqueness for arbitrary complex matrices; the construction here is
its Hermitian square real-or-complex specialization, with the spectral reciprocal set to zero on
the zero eigenspace.
-/

@[expose] public section

noncomputable section

open scoped Matrix Classical Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real functional-calculus value of `x ↦ x⁻¹`; for Hermitian input it inverts every nonzero
real eigenvalue and leaves zero eigenvalues zero. Total CFC gives zero on non-Hermitian input.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type. -/
def spectralPseudoInverse (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  cfc (fun x : ℝ => x⁻¹) A

/-- The real functional-calculus value of the indicator that is zero at zero and one at every other
real eigenvalue; it is zero on non-Hermitian input.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type. -/
def spectralSupport (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) A

private lemma continuousOn_real_spectrum (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

/-- The spectral pseudoinverse of the zero matrix is zero.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralPseudoInverse_zero : spectralPseudoInverse (0 : Matrix n n 𝕜) = 0
``` -/
@[simp]
theorem spectralPseudoInverse_zero : spectralPseudoInverse (0 : Matrix n n 𝕜) = 0 := by
  simp [spectralPseudoInverse]

/-- The spectral support of the zero matrix is zero.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_zero : spectralSupport (0 : Matrix n n 𝕜) = 0
``` -/
@[simp]
theorem spectralSupport_zero : spectralSupport (0 : Matrix n n 𝕜) = 0 := by
  simp [spectralSupport]

/-- The total spectral-pseudoinverse construction always yields a Hermitian matrix.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem isHermitian_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A).IsHermitian
``` -/
theorem isHermitian_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A).IsHermitian :=
  cfc_predicate (fun x : ℝ => x⁻¹) A

/-- The total spectral-support construction always yields a Hermitian matrix.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem isHermitian_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A).IsHermitian
``` -/
theorem isHermitian_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A).IsHermitian :=
  cfc_predicate (fun x : ℝ => if x = 0 then 0 else 1) A

/-- Conjugate transpose fixes the spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem conjTranspose_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A)ᴴ = spectralPseudoInverse A
``` -/
@[simp]
theorem conjTranspose_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A)ᴴ = spectralPseudoInverse A :=
  (isHermitian_spectralPseudoInverse A).eq

/-- Conjugate transpose fixes the spectral support.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem conjTranspose_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A)ᴴ = spectralSupport A
``` -/
@[simp]
theorem conjTranspose_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A)ᴴ = spectralSupport A :=
  (isHermitian_spectralSupport A).eq

/-- The spectral support is idempotent for every matrix input, including the total-CFC zero case.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_mul_self (A : Matrix n n 𝕜) :
    spectralSupport A * spectralSupport A = spectralSupport A
``` -/
@[simp]
theorem spectralSupport_mul_self (A : Matrix n n 𝕜) :
    spectralSupport A * spectralSupport A = spectralSupport A := by
  unfold spectralSupport
  rw [← cfc_mul _ _ A (continuousOn_real_spectrum A _) (continuousOn_real_spectrum A _)]
  apply cfc_congr
  intro x _
  by_cases hx : x = 0 <;> simp [hx]

/-- On each nonzero eigenspace, multiplication by the spectral reciprocal
cancels the eigenvalue; the zero eigenspace is annihilated.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.mul_spectralPseudoInverse_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A = spectralSupport A
``` -/
theorem IsHermitian.mul_spectralPseudoInverse_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A = spectralSupport A := by
  unfold spectralPseudoInverse spectralSupport
  calc
    A * cfc (fun x : ℝ => x⁻¹) A =
        cfc (fun x : ℝ => x) A * cfc (fun x : ℝ => x⁻¹) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
    _ = cfc (fun x : ℝ => x * x⁻¹) A :=
      (cfc_mul _ _ A (continuousOn_real_spectrum A _) (continuousOn_real_spectrum A _)).symm
    _ = cfc (fun x : ℝ => if x = 0 then 0 else 1) A := by
      apply cfc_congr
      intro x _
      by_cases hx : x = 0 <;> simp [hx]

/-- For a Hermitian matrix, right multiplication by the input after its spectral pseudoinverse
gives the spectral support.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_mul_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A = spectralSupport A
``` -/
theorem IsHermitian.spectralPseudoInverse_mul_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A = spectralSupport A := by
  unfold spectralPseudoInverse spectralSupport
  calc
    cfc (fun x : ℝ => x⁻¹) A * A =
        cfc (fun x : ℝ => x⁻¹) A * cfc (fun x : ℝ => x) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
    _ = cfc (fun x : ℝ => x⁻¹ * x) A :=
      (cfc_mul _ _ A (continuousOn_real_spectrum A _) (continuousOn_real_spectrum A _)).symm
    _ = cfc (fun x : ℝ => if x = 0 then 0 else 1) A := by
      apply cfc_congr
      intro x _
      by_cases hx : x = 0 <;> simp [hx]

/-- For a Hermitian input, its support acts as the identity on that input.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralSupport_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralSupport A * A = A
``` -/
@[simp]
theorem IsHermitian.spectralSupport_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralSupport A * A = A := by
  unfold spectralSupport
  calc
    cfc (fun x : ℝ => if x = 0 then 0 else 1) A * A =
        cfc (fun x : ℝ => if x = 0 then 0 else 1) A * cfc (fun x : ℝ => x) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
    _ = cfc (fun x : ℝ => (if x = 0 then 0 else 1) * x) A :=
      (cfc_mul _ _ A (continuousOn_real_spectrum A _) (continuousOn_real_spectrum A _)).symm
    _ = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x _
      by_cases hx : x = 0 <;> simp [hx]
    _ = A := cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint

/-- The spectral support acts as the identity on the spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_mul_spectralPseudoInverse (A : Matrix n n 𝕜) :
    spectralSupport A * spectralPseudoInverse A = spectralPseudoInverse A
``` -/
@[simp]
theorem spectralSupport_mul_spectralPseudoInverse (A : Matrix n n 𝕜) :
    spectralSupport A * spectralPseudoInverse A = spectralPseudoInverse A := by
  unfold spectralSupport spectralPseudoInverse
  rw [← cfc_mul _ _ A (continuousOn_real_spectrum A _) (continuousOn_real_spectrum A _)]
  apply cfc_congr
  intro x _
  by_cases hx : x = 0 <;> simp [hx]

/-- A Hermitian matrix satisfies the first Penrose equation `A A† A = A`.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.mul_spectralPseudoInverse_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A
``` -/
@[simp]
theorem IsHermitian.mul_spectralPseudoInverse_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A := by
  rw [hA.mul_spectralPseudoInverse_eq_spectralSupport, hA.spectralSupport_mul]

/-- A Hermitian matrix satisfies the second Penrose equation `A† A A† = A†`.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A
``` -/
@[simp]
theorem IsHermitian.spectralPseudoInverse_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A := by
  rw [hA.spectralPseudoInverse_mul_eq_spectralSupport, spectralSupport_mul_spectralPseudoInverse]

/-- For Hermitian input, the product `A A†` is fixed by conjugate transpose.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.conjTranspose_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A
``` -/
theorem IsHermitian.conjTranspose_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A := by
  rw [hA.mul_spectralPseudoInverse_eq_spectralSupport, conjTranspose_spectralSupport]

/-- For Hermitian input, the product `A† A` is fixed by conjugate transpose.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.conjTranspose_spectralPseudoInverse_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A
``` -/
theorem IsHermitian.conjTranspose_spectralPseudoInverse_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A := by
  rw [hA.spectralPseudoInverse_mul_eq_spectralSupport, conjTranspose_spectralSupport]

/-- The computed spectral reciprocal of a finite Hermitian matrix satisfies all four Moore–Penrose
equations.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_penrose {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A ∧
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A ∧
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A ∧
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A
``` -/
theorem IsHermitian.spectralPseudoInverse_penrose {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A ∧
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A ∧
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A ∧
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A :=
  ⟨hA.mul_spectralPseudoInverse_mul, hA.spectralPseudoInverse_mul_spectralPseudoInverse,
    hA.conjTranspose_mul_spectralPseudoInverse, hA.conjTranspose_spectralPseudoInverse_mul⟩

end Matrix
