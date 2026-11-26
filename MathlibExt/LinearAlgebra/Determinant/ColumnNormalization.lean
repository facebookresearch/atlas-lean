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
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g). The determinant identity holds for every scalar π.
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

/-- **Finite basis-column normalization data.**

Let R be a commutative ring, M an R-module with finite basis b:I→M, π∈R and c_i∈ℕ. If
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g).
UniformizerColumnNormalization π f records a finite basis b, exponents c_i, an endomorphism g
and these column identities.
-/
structure UniformizerColumnNormalization {R : Type uR} {M : Type uM}
    [CommRing R] [AddCommGroup M] [Module R M]
    (pi : R) (f : M →ₗ[R] M) where
  index : Type uI
  indexFintype : Fintype index
  basis : Module.Basis index R M
  exponent : index → ℕ
  normalized : M →ₗ[R] M
  apply_basis : ∀ i,
    f (basis i) = pi ^ exponent i • normalized (basis i)

namespace UniformizerColumnNormalization

variable {pi : R} {f : M →ₗ[R] M}

/-- **Column normalization from divisibility of basis images.**

Let R be a commutative ring, b a finite basis of M, π∈R,c_i∈ℕ and f an endomorphism. If for
every i there exists y_i with f(b_i)=π^(c_i)•y_i, ofExists constructs the normalization with
g(b_i)=y_i.
-/
noncomputable def ofExists (b : Module.Basis ι R M) (pi : R)
    (c : ι → ℕ) (f : M →ₗ[R] M)
    (h : ∀ i, ∃ y : M, f (b i) = pi ^ c i • y) :
    UniformizerColumnNormalization pi f where
  index := ι
  indexFintype := inferInstance
  basis := b
  exponent := c
  normalized := b.constr R fun i ↦ Classical.choose (h i)
  apply_basis := fun i ↦ by
    rw [Module.Basis.constr_basis]
    exact Classical.choose_spec (h i)

/-- **Sum of extracted basis-column exponents.**

Let R be a commutative ring, M an R-module with finite basis b:I→M, π∈R and c_i∈ℕ. If
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g). For
normalization data D, totalExponent D=∑i D.exponent(i).
-/
noncomputable def totalExponent
    (D : UniformizerColumnNormalization pi f) : ℕ := by
  letI : Fintype D.index := D.indexFintype
  exact ∑ i, D.exponent i

@[simp]
theorem totalExponent_ofExists (b : Module.Basis ι R M) (pi : R)
    (c : ι → ℕ) (f : M →ₗ[R] M)
    (h : ∀ i, ∃ y : M, f (b i) = pi ^ c i • y) :
    (ofExists b pi c f h).totalExponent = ∑ i, c i :=
  rfl

/-- **Determinant formula from column-normalization data.**

Let R be a commutative ring, M an R-module with finite basis b:I→M, π∈R and c_i∈ℕ. If
endomorphisms f,g satisfy f(b_i)=π^(c_i)•g(b_i), then det(f)=π^(∑i c_i)det(g). For
D:UniformizerColumnNormalization π f, det(f)=π^(D.totalExponent)det(D.normalized).
-/
theorem det_eq (D : UniformizerColumnNormalization pi f) :
    f.det = pi ^ D.totalExponent * D.normalized.det := by
  let _ : Fintype D.index := D.indexFintype
  exact det_eq_pow_sum_mul_det_of_apply_basis
    D.basis pi D.exponent f D.normalized D.apply_basis

end UniformizerColumnNormalization

end LinearMap

end
