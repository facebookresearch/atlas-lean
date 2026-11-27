/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of semilinear maps in a basis

Let `σ` be a ring endomorphism of a commutative ring `R`, `b` a finite basis of an `R`-module `M`
and `f : M → M` a `σ`-semilinear map. The matrix of `f` in `b` is `b.toMatrix (f ∘ b)`, so that
`f (b j) = ∑ i, b.toMatrix (f ∘ b) i j • b i`, and its determinant is `b.det (f ∘ b)`. Unlike for
linear maps, this determinant depends on `b`: for another basis `b'` it is multiplied by
`σ u / u`, where `u = b.det b'` is the determinant of the change of basis.

## Main results

* `Module.Basis.toMatrix_compₛₗ`: the matrix of `f ∘ v` for a family `v` is
  `b.toMatrix (f ∘ b) * (b.toMatrix v).map σ`.
* `Module.Basis.det_compₛₗ`: `b.det (f ∘ v) = b.det (f ∘ b) * σ (b.det v)`.
* `Module.Basis.det_mul_det_compₛₗ`: the change of basis formula
  `b.det b' * b'.det (f ∘ b') = b.det (f ∘ b) * σ (b.det b')`.
* `Module.Basis.isUnit_det_compₛₗ`: for a semilinear equivalence `f`, `b.det (f ∘ b)` is a unit.
-/

@[expose] public section

namespace Module.Basis

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {σ : R →+* R}
  {ι ι' : Type*} [Fintype ι]

/-- The matrix in a finite basis `b` of the image `f ∘ v` of a family `v` under a `σ`-semilinear
map `f : M → M` is the product of the matrix of `f` in `b` with the matrix of `v` in `b`, to which
`σ` is applied entrywise. -/
theorem toMatrix_compₛₗ (b : Basis ι R M) (f : M →ₛₗ[σ] M) (v : ι' → M) :
    b.toMatrix (f ∘ v) = b.toMatrix (f ∘ b) * (b.toMatrix v).map σ := by
  ext i j
  conv_lhs => rw [toMatrix_apply, Function.comp_apply, ← b.sum_repr (v j)]
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Matrix.mul_apply, toMatrix_apply, Matrix.map_apply,
    Function.comp_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable [DecidableEq ι]

/-- For a finite basis `b`, a `σ`-semilinear map `f : M → M` and a family `v` indexed like `b`,
`b.det (f ∘ v) = b.det (f ∘ b) * σ (b.det v)`. -/
theorem det_compₛₗ (b : Basis ι R M) (f : M →ₛₗ[σ] M) (v : ι → M) :
    b.det (f ∘ v) = b.det (f ∘ b) * σ (b.det v) := by
  rw [det_apply, det_apply, det_apply, toMatrix_compₛₗ, Matrix.det_mul, RingHom.map_det]
  rfl

/-- Change of basis for the determinant of a `σ`-semilinear map `f : M → M`: for finite bases `b`
and `b'` indexed by the same type, `b.det b' * b'.det (f ∘ b') = b.det (f ∘ b) * σ (b.det b')`. -/
theorem det_mul_det_compₛₗ (b b' : Basis ι R M) (f : M →ₛₗ[σ] M) :
    b.det b' * b'.det (f ∘ b') = b.det (f ∘ b) * σ (b.det b') := by
  rw [← det_compₛₗ, det_apply, det_apply, det_apply, ← Matrix.det_mul, toMatrix_mul_toMatrix]

/-- For a finite basis `b` and a `σ`-semilinear equivalence `f : M ≃ M` (for a ring automorphism
`σ` with inverse `σ'`), the determinant `b.det (f ∘ b)` of the matrix of `f` in `b` is a unit. -/
theorem isUnit_det_compₛₗ {σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (b : Basis ι R M) (f : M ≃ₛₗ[σ] M) : IsUnit (b.det (f ∘ b)) := by
  have h := det_compₛₗ b (f : M →ₛₗ[σ] M) (f.symm ∘ b)
  have hb : (f : M →ₛₗ[σ] M) ∘ f.symm ∘ b = b := by
    ext i
    simp
  rw [hb, det_self] at h
  exact IsUnit.of_mul_eq_one _ h.symm

end Module.Basis
