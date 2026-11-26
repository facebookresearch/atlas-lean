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
# Kronecker products and finite sums

Let R be an additive commutative monoid with a possibly nonassociative multiplication
distributing over addition and absorbing zero, and let A,B be rectangular matrices over R.
Their Kronecker product has entries (A⊗B)_((i,k),(j,l))=A_(i,j)B_(k,l). The product
distributes over finite sums in either factor: (∑A_i)⊗B=∑(A_i⊗B) and A⊗(∑B_i)=∑(A⊗B_i). Only
distributivity and zero absorption are required; matrix index types are arbitrary.
-/

@[expose] public section

open Matrix Finset
open scoped Kronecker

namespace Matrix

variable {l m n p : Type*}
variable {α : Type*} {ι : Type*}

-- Finset sum, left argument varies.

/-- **Finite-sum distribution in the first Kronecker factor.**

Let R be an additive commutative monoid with a possibly nonassociative multiplication
distributing over addition and absorbing zero, and let A,B be rectangular matrices over R.
Their Kronecker product has entries (A⊗B)_((i,k),(j,l))=A_(i,j)B_(k,l). For a finite set s⊂I,
matrices A_i of common l×m size and B of n×p size, ∑i∈s(A_i⊗B)=(∑i∈s A_i)⊗B.
-/
theorem sum_kronecker {s : Finset ι} {f : ι → Matrix l m α} {N : Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i ∈ s, f i ⊗ₖ N = (∑ i ∈ s, f i) ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_kronecker, ih]

/-- **Finite-sum distribution in the second Kronecker factor.**

Let R be an additive commutative monoid with a possibly nonassociative multiplication
distributing over addition and absorbing zero, and let A,B be rectangular matrices over R.
Their Kronecker product has entries (A⊗B)_((i,k),(j,l))=A_(i,j)B_(k,l). For A of l×m size, a
finite set s⊂I and matrices B_i of common n×p size, ∑i∈s(A⊗B_i)=A⊗(∑i∈s B_i).
-/
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

/-- **Whole finite-index sum in the first Kronecker factor.**

Let R be an additive commutative monoid with a possibly nonassociative multiplication
distributing over addition and absorbing zero, and let A,B be rectangular matrices over R.
Their Kronecker product has entries (A⊗B)_((i,k),(j,l))=A_(i,j)B_(k,l). For finite I, matrices
A_i of a common rectangular size and fixed B, ∑i∈I(A_i⊗B)=(∑i∈I A_i)⊗B.
-/
theorem sum_kronecker_fintype [Fintype ι] {f : ι → Matrix l m α} {N : Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i : ι, f i ⊗ₖ N = (∑ i : ι, f i) ⊗ₖ N := by
  calc ∑ _ : ι, _ ⊗ₖ N
      = ∑ i ∈ Finset.univ, f i ⊗ₖ N := rfl
    _ = (∑ i ∈ Finset.univ, f i) ⊗ₖ N := sum_kronecker
    _ = (∑ _ : ι, f _) ⊗ₖ N := rfl

/-- **Whole finite-index sum in the second Kronecker factor.**

Let R be an additive commutative monoid with a possibly nonassociative multiplication
distributing over addition and absorbing zero, and let A,B be rectangular matrices over R.
Their Kronecker product has entries (A⊗B)_((i,k),(j,l))=A_(i,j)B_(k,l). For finite I, fixed A
and matrices B_i of a common rectangular size, ∑i∈I(A⊗B_i)=A⊗(∑i∈I B_i).
-/
theorem kronecker_sum_fintype [Fintype ι] {M : Matrix l m α} {f : ι → Matrix n p α}
    [NonUnitalNonAssocSemiring α] :
    ∑ i : ι, M ⊗ₖ f i = M ⊗ₖ ∑ i : ι, f i := by
  calc ∑ _ : ι, M ⊗ₖ f _
      = ∑ i ∈ Finset.univ, M ⊗ₖ f i := rfl
    _ = M ⊗ₖ ∑ i ∈ Finset.univ, f i := kronecker_sum
    _ = M ⊗ₖ ∑ _ : ι, f _ := rfl

end Matrix
