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

public import MathlibExt.Analysis.Matrix.HermitianPseudoInverse

/-!
# Uniqueness of the finite Hermitian pseudoinverse

For a finite real-or-complex Hermitian matrix `A`, a candidate matrix `X`
equals its computed spectral pseudoinverse when `AXA=A`, `XAX=X`, and both
`AX` and `XA` are Hermitian. These are the four Moore–Penrose equations.
No invertibility or nonzero-eigenvalue assumption is imposed. Zero and
empty-index matrices are included, with the same total spectral reciprocal.

## References

Uniqueness under the four equations is Theorem 1 in R. Penrose, “A generalized inverse for
matrices”, *Mathematical Proceedings of the Cambridge Philosophical Society* 51(3) (1955),
406–413. Here the input is a Hermitian square matrix over `ℝ` or `ℂ`, and its unique generalized
inverse is the computed spectral reciprocal.
-/

@[expose] public section

noncomputable section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a finite Hermitian input `A`, any matrix `X` satisfying both Penrose product equations and
Hermitianity of `AX` and `XA` equals the computed spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem eq_spectralPseudoInverse_of_penrose {A X : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAXA : A * X * A = A) (hXAX : X * A * X = X)
    (hAX : (A * X).IsHermitian) (hXA : (X * A).IsHermitian) :
    X = spectralPseudoInverse A
``` -/
theorem eq_spectralPseudoInverse_of_penrose {A X : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAXA : A * X * A = A) (hXAX : X * A * X = X)
    (hAX : (A * X).IsHermitian) (hXA : (X * A).IsHermitian) :
    X = spectralPseudoInverse A := by
  let P := spectralPseudoInverse A
  have hAPA : A * P * A = A := hA.mul_spectralPseudoInverse_mul
  have hPAP : P * A * P = P := hA.spectralPseudoInverse_mul_spectralPseudoInverse
  have hAP : (A * P).IsHermitian := hA.conjTranspose_mul_spectralPseudoInverse
  have hPA : (P * A).IsHermitian := hA.conjTranspose_spectralPseudoInverse_mul
  have hAXAP : (A * X) * (A * P) = A * P := by
    calc
      (A * X) * (A * P) = (A * X * A) * P := by simp only [Matrix.mul_assoc]
      _ = A * P := by rw [hAXA]
  have hAPAX : (A * P) * (A * X) = A * X := by
    calc
      (A * P) * (A * X) = (A * P * A) * X := by simp only [Matrix.mul_assoc]
      _ = A * X := by rw [hAPA]
  have hleft : A * X = A * P := by
    have h := congrArg Matrix.conjTranspose hAXAP
    simp only [conjTranspose_mul, hAP.eq, hAX.eq] at h
    exact hAPAX.symm.trans h
  have hXAPA : (X * A) * (P * A) = X * A := by
    calc
      (X * A) * (P * A) = X * (A * P * A) := by simp only [Matrix.mul_assoc]
      _ = X * A := by rw [hAPA]
  have hPAXA : (P * A) * (X * A) = P * A := by
    calc
      (P * A) * (X * A) = P * (A * X * A) := by simp only [Matrix.mul_assoc]
      _ = P * A := by rw [hAXA]
  have hright : X * A = P * A := by
    have h := congrArg Matrix.conjTranspose hPAXA
    simp only [conjTranspose_mul, hPA.eq, hXA.eq] at h
    exact hXAPA.symm.trans h
  calc
    X = X * A * X := hXAX.symm
    _ = P * A * X := by rw [hright]
    _ = P * A * P := by rw [Matrix.mul_assoc, hleft, ← Matrix.mul_assoc]
    _ = P := hPAP

end Matrix
