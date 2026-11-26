/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Translation automorphisms of a polynomial algebra

For a commutative ring `R`, a type `σ`, and `t : σ → R`, substitution `X_i ↦ X_i + C(t_i)`
fixes the coefficients and defines an `R`-algebra automorphism of `MvPolynomial σ R`.

Its inverse substitutes `X_i ↦ X_i - C(t_i)` and also fixes coefficients.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 1.
-/

@[expose] public section
noncomputable section

universe u v

namespace MvPolynomial

variable (R : Type u) [CommRing R] {σ : Type v}

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. The `R`-algebra homomorphism
`translationAlgHom R t : MvPolynomial σ R →ₐ[R] MvPolynomial σ R` substitutes `X_i ↦ X_i + C(t
i)` and fixes every coefficient `C r`. -/
def translationAlgHom (t : σ → R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i + C (t i))

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. Substitution `X_i ↦ X_i + C(t i)`
is the `R`-algebra equivalence `translationAlgEquiv R t`. Its inverse substitutes `X_i ↦ X_i -
C(t i)`, with both maps fixing coefficients. -/
def translationAlgEquiv (t : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (translationAlgHom R t)
    (translationAlgHom R (fun i => -t i))
    (by ext i; simp [translationAlgHom, aeval_C, add_assoc])
    (by ext i; simp [translationAlgHom, aeval_C, add_assoc])

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. For `i : σ`, `translationAlgEquiv
R t (X i) = X i + C(t i)`. -/
@[simp]
theorem translationAlgEquiv_X (t : σ → R) (i : σ) :
    translationAlgEquiv R t (X i) = X i + C (t i) := by
  change translationAlgHom R t (X i) = _
  exact aeval_X (fun j : σ => (X j : MvPolynomial σ R) + C (t j)) i

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. For `r : R`, `translationAlgEquiv
R t (C r) = C r`. -/
@[simp]
theorem translationAlgEquiv_C (t : σ → R) (r : R) :
    translationAlgEquiv R t (C r) = C r := by
  change translationAlgHom R t (C r) = C r
  simp only [translationAlgHom, aeval_C, algebraMap_eq]

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. For `i : σ`, `(translationAlgEquiv
R t).symm (X i) = X i - C(t i)`. -/
@[simp]
theorem translationAlgEquiv_symm_X (t : σ → R) (i : σ) :
    (translationAlgEquiv R t).symm (X i) = X i - C (t i) := by
  change translationAlgHom R (fun j => -t j) (X i) = _
  simp only [translationAlgHom, aeval_X, map_neg, sub_eq_add_neg]

/-- Let `R` be a commutative ring, `σ` a type, and `t : σ → R`. For `r : R`, `(translationAlgEquiv
R t).symm (C r) = C r`. -/
@[simp]
theorem translationAlgEquiv_symm_C (t : σ → R) (r : R) :
    (translationAlgEquiv R t).symm (C r) = C r := by
  change translationAlgHom R (fun j => -t j) (C r) = C r
  simp only [translationAlgHom, aeval_C, algebraMap_eq]

end MvPolynomial
