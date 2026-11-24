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
# Determinants after basis-column normalization

This file records the determinant factorization obtained by extracting a
possibly different power of one scalar from every column of a linear
endomorphism.

## Main result

* `LinearMap.det_eq_pow_sum_mul_det_of_apply_basis`: if, on a finite basis
  `b`, two endomorphisms satisfy

  ```text
  f (b i) = π ^ c i • g (b i),
  ```

  then

  ```text
  det f = π ^ (∑ i, c i) * det g.
  ```
* `LinearMap.UniformizerColumnNormalization`: bundles the basis, extracted
  exponents, normalized endomorphism, and column identities; its `det_eq`
  theorem applies the factorization directly.

The statement is valid over an arbitrary commutative ring.  In particular,
`π` need not be regular or a uniformizer; those hypotheses belong only to
applications which construct `g` by dividing the columns of `f`.  The
explicit finite basis supplies the determinant data, so no separate
`Module.Free` or `Module.Finite` instance is required.

## Informal proof

Write both endomorphisms in the basis `b`.  The hypothesis says that column
`i` of the matrix of `f` is column `i` of the matrix of `g`, multiplied by
`π ^ c i`.  Hence

```text
matrix(f) = matrix(g) * diagonal(i ↦ π ^ c i).
```

Taking determinants turns the matrix product into a product.  The determinant
of the diagonal factor is `∏ i, π ^ c i`, and collecting powers of the common
base `π` changes this product to `π ^ ∑ i, c i`.
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

/-- Extracting the power `π ^ c i` from basis column `i` extracts the sum of
the exponents from the determinant.

This is a columnwise factorization theorem, not a division theorem: the
normalized endomorphism `g` and the displayed basis equalities are supplied
as data.  Consequently no regularity assumption on `π` is required. -/
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

/-- Basis-indexed data exhibiting an endomorphism as columnwise powers of
one scalar times a normalized endomorphism. -/
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

/-- Construct bundled column-normalization data from basiswise divisibility
witnesses.  The normalized endomorphism is the linear map sending each basis
vector to a chosen quotient column. -/
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

/-- Total scalar exponent extracted from all basis columns. -/
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

/-- Determinant factorization supplied by bundled column-normalization
data. -/
theorem det_eq (D : UniformizerColumnNormalization pi f) :
    f.det = pi ^ D.totalExponent * D.normalized.det := by
  let _ : Fintype D.index := D.indexFintype
  exact det_eq_pow_sum_mul_det_of_apply_basis
    D.basis pi D.exponent f D.normalized D.apply_basis

end UniformizerColumnNormalization

end LinearMap

end
