/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Translation of arbitrary multivariate polynomial coordinates

The original coefficient ring is fixed. Every variable is translated by an
actual element of that ring, and translating by its negative is the proved
inverse. The variable type and the commutative coefficient ring are arbitrary.
-/

@[expose] public section
noncomputable section

universe u v

namespace MvPolynomial

variable (R : Type u) [CommRing R] {σ : Type v}

/-- Substitute the actual translated variables, fixing every coefficient. -/
def translationAlgHom (t : σ → R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i + C (t i))

/-- Translation has the actual inverse substitution by the negative constants. -/
def translationAlgEquiv (t : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (translationAlgHom R t)
    (translationAlgHom R (fun i => -t i))
    (by ext i; simp [translationAlgHom, aeval_C, add_assoc])
    (by ext i; simp [translationAlgHom, aeval_C, add_assoc])

/-- The forward map changes only the original variable coordinate. -/
@[simp]
theorem translationAlgEquiv_X (t : σ → R) (i : σ) :
    translationAlgEquiv R t (X i) = X i + C (t i) := by
  change translationAlgHom R t (X i) = _
  exact aeval_X (fun j : σ => (X j : MvPolynomial σ R) + C (t j)) i

/-- The forward map retains every original coefficient. -/
@[simp]
theorem translationAlgEquiv_C (t : σ → R) (r : R) :
    translationAlgEquiv R t (C r) = C r := by
  change translationAlgHom R t (C r) = C r
  simp only [translationAlgHom, aeval_C, algebraMap_eq]

/-- The inverse removes the same original translation constant. -/
@[simp]
theorem translationAlgEquiv_symm_X (t : σ → R) (i : σ) :
    (translationAlgEquiv R t).symm (X i) = X i - C (t i) := by
  change translationAlgHom R (fun j => -t j) (X i) = _
  simp only [translationAlgHom, aeval_X, map_neg, sub_eq_add_neg]

/-- The inverse also retains every original coefficient. -/
@[simp]
theorem translationAlgEquiv_symm_C (t : σ → R) (r : R) :
    (translationAlgEquiv R t).symm (C r) = C r := by
  change translationAlgHom R (fun j => -t j) (C r) = C r
  simp only [translationAlgHom, aeval_C, algebraMap_eq]

end MvPolynomial
