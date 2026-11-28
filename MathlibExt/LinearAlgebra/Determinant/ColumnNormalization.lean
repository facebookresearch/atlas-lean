/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant factorization from normalized basis columns

Let R be a commutative ring, M an R-module with finite basis b:I→M, π∈R and c_i∈ℕ. If
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g). The determinant
identity holds for every scalar π.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe uR uM uI

namespace LinearMap

variable {R : Type uR} {M : Type uM} {ι : Type uI}
variable [CommRing R] [Fintype ι]
variable [AddCommGroup M] [Module R M]

/-- **Extracted column powers sum in the determinant.**

Let R be a commutative ring, M an R-module with finite basis b:I→M, π∈R and c_i∈ℕ. If
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g). This is
det_eq_pow_sum_mul_det_of_apply_basis, including empty bases.
-/
theorem det_eq_pow_sum_mul_det_of_apply_basis
    (b : Module.Basis ι R M) (π : R) (c : ι → ℕ)
    (f g : M →ₗ[R] M)
    (h : ∀ i, f (b i) = π ^ c i • g (b i)) :
    f.det = π ^ (∑ i, c i) * g.det := by
  classical
  have hmatrix :
      LinearMap.toMatrix b b f =
        LinearMap.toMatrix b b g * Matrix.diagonal (fun i ↦ π ^ c i) := by
    ext i j
    rw [LinearMap.toMatrix_apply, h j, map_smul, Matrix.mul_diagonal,
      LinearMap.toMatrix_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  calc
    f.det = (LinearMap.toMatrix b b f).det :=
      (LinearMap.det_toMatrix b f).symm
    _ = (LinearMap.toMatrix b b g *
          Matrix.diagonal (fun i ↦ π ^ c i)).det := by rw [hmatrix]
    _ = (LinearMap.toMatrix b b g).det *
          (Matrix.diagonal (fun i ↦ π ^ c i)).det := by
      rw [Matrix.det_mul]
    _ = g.det * ∏ i, π ^ c i := by
      rw [LinearMap.det_toMatrix, Matrix.det_diagonal]
    _ = π ^ (∑ i, c i) * g.det := by
      rw [Finset.prod_pow_eq_pow_sum]
      exact mul_comm _ _

/-- **Determinant factorization from divisible basis columns.**

Let R be a commutative ring, b a finite basis of M, π∈R and c_i∈ℕ chosen exponents. If each
f(b_i) has the form π^(c_i)•y_i, there is an endomorphism g with these normalized basis images
and det(f)=π^(∑i c_i)det(g). The scalar π is arbitrary, and g and the exponents are choices.
-/
theorem exists_det_eq_pow_sum_mul_det_of_exists_apply_basis
    (b : Module.Basis ι R M) (π : R) (c : ι → ℕ) (f : M →ₗ[R] M)
    (h : ∀ i, ∃ y : M, f (b i) = π ^ c i • y) :
    ∃ g : M →ₗ[R] M,
      (∀ i, f (b i) = π ^ c i • g (b i)) ∧
        f.det = π ^ (∑ i, c i) * g.det := by
  classical
  let g : M →ₗ[R] M := b.constr R fun i ↦ Classical.choose (h i)
  have hg : ∀ i, f (b i) = π ^ c i • g (b i) := by
    intro i
    rw [g, Module.Basis.constr_basis]
    exact Classical.choose_spec (h i)
  exact ⟨g, hg, det_eq_pow_sum_mul_det_of_apply_basis b π c f g hg⟩

end LinearMap

end
