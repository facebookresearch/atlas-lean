/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.AddMonoidAlgebraAlgHom

@[expose] public section

open AddMonoidAlgebra

universe u v

/-- Consumer with the original binders and universes. -/
private theorem exactSource {L : Type u} [Field L] (A : ValuationSubring L)
    {G : Type v} [AddMonoid G] (hG : ∀ g : G, IsOfFinAddOrder g)
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    (∀ x, χ x ∈ A) ∧ ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x :=
  A.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder hG χ

/-- In particular, the factorisation exists for a finite additive group. -/
example {L : Type*} [Field L] (A : ValuationSubring L)
    {G : Type*} [AddCommGroup G] [Finite G]
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x :=
  (A.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
    (fun g => isOfFinAddOrder_of_finite g) χ).2
