/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Fintype.BigOperators

/-!
# Kronecker product distributes over sums

This module provides minimal generic lemmas for distributing the Kronecker
product over `Finset` and `Fintype` sums, abstracting the private copies that
appear in QIT consumers.

Kronecker multiplication is pointwise multiplication of entries, so
`(∑ᵢ Aᵢ) ⊗ₖ B = ∑ᵢ (Aᵢ ⊗ₖ B)` uses right-distributivity `add_mul` and
`zero_mul`, while `A ⊗ₖ (∑ᵢ Bᵢ) = ∑ᵢ (A ⊗ₖ Bᵢ)` uses `mul_add` and `mul_zero`.
Hence `NonUnitalNonAssocSemiring` on the coefficient type suffices; we do not
assume commutativity, associativity of `*`, or a one.

The proofs use the existing `Matrix.add_kronecker`, `Matrix.kronecker_add`,
`Matrix.zero_kronecker`, and `Matrix.kronecker_zero` lemmas and plain
`Finset.induction`.  The `Fintype` corollaries follow from `Finset.univ`;
equivalently they can be obtained from `Matrix.kroneckerBilinear` and
`LinearMap.map_sum` when a `Semiring` instance is available, which yields the
same equalities in one line.

## Main results

* `Matrix.sum_kronecker` – `∑ i ∈ s, f i ⊗ₖ N = (∑ i ∈ s, f i) ⊗ₖ N`
* `Matrix.kronecker_sum` – `∑ i ∈ s, M ⊗ₖ f i = M ⊗ₖ (∑ i ∈ s, f i)`
* `Matrix.sum_kronecker_fintype` – Fintype version of `sum_kronecker`
* `Matrix.kronecker_sum_fintype` – Fintype version of `kronecker_sum`

## Tags

matrix, Kronecker product, Finset sum, Fintype sum
-/

@[expose] public section

open Matrix Finset
open scoped Kronecker

namespace Matrix

variable {l m n p : Type*}
variable {α : Type*} {ι : Type*}

-- Finset sum, left argument varies.

/-- Kronecker product distributes over a `Finset` sum on the left:
`∑ i ∈ s, f i ⊗ₖ N = (∑ i ∈ s, f i) ⊗ₖ N`. -/
theorem sum_kronecker {s : Finset ι} {f : ι → Matrix l m α} {N : Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i ∈ s, f i ⊗ₖ N = (∑ i ∈ s, f i) ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_kronecker, ih]

/-- Kronecker product distributes over a `Finset` sum on the right:
`∑ i ∈ s, M ⊗ₖ f i = M ⊗ₖ (∑ i ∈ s, f i)`. -/
theorem kronecker_sum {s : Finset ι} {M : Matrix l m α} {f : ι → Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i ∈ s, M ⊗ₖ f i = M ⊗ₖ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, kronecker_add, ih]

-- Fintype corollaries via `Finset.univ`.

/-- Fintype version of `Matrix.sum_kronecker`. -/
theorem sum_kronecker_fintype [Fintype ι] {f : ι → Matrix l m α} {N : Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i : ι, f i ⊗ₖ N = (∑ i : ι, f i) ⊗ₖ N := by
  calc ∑ _ : ι, _ ⊗ₖ N
      = ∑ i ∈ Finset.univ, f i ⊗ₖ N := rfl
    _ = (∑ i ∈ Finset.univ, f i) ⊗ₖ N := sum_kronecker
    _ = (∑ _ : ι, f _) ⊗ₖ N := rfl

/-- Fintype version of `Matrix.kronecker_sum`. -/
theorem kronecker_sum_fintype [Fintype ι] {M : Matrix l m α} {f : ι → Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i : ι, M ⊗ₖ f i = M ⊗ₖ ∑ i : ι, f i := by
  calc ∑ _ : ι, M ⊗ₖ f _
      = ∑ i ∈ Finset.univ, M ⊗ₖ f i := rfl
    _ = M ⊗ₖ ∑ i ∈ Finset.univ, f i := kronecker_sum
    _ = M ⊗ₖ ∑ _ : ι, f _ := rfl

end Matrix
