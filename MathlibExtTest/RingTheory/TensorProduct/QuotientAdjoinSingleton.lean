/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.TensorProduct.QuotientAdjoinSingleton

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

/-- Exact source statement, with the original `Type` binders. -/
example
    (Z₀ : Type) [CommRing Z₀] (V : Type) [CommRing V] [Algebra Z₀ V] (ϖ : V)
    (hgen : Algebra.adjoin Z₀ {ϖ} = ⊤)
    (A : Type) [CommRing A] [Algebra Z₀ A] [Algebra V A] [IsScalarTower Z₀ V A]
    (C : Type) [CommRing C] [Algebra Z₀ C] [Algebra V C] [IsScalarTower Z₀ V C]
    (μ : A) (w : C) (hA : algebraMap V A ϖ = 1 - μ) (hC : algebraMap V C ϖ = 1 - w) :
    ∃ e : ((A ⊗[Z₀] C) ⧸ Ideal.span {(μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w)}) ≃+* (C ⊗[V] A),
      ∀ (a : A) (c : C), e (Ideal.Quotient.mk _ (a ⊗ₜ[Z₀] c)) = c ⊗ₜ[V] a :=
  nonempty_ringEquiv_quotient_span_tmul_sub_tmul_of_adjoin_singleton_eq_top
    Z₀ V ϖ hgen A C μ w hA hC

/-- Higher-universe consumer. -/
example
    (Z₀ : Type 1) [CommRing Z₀] (V : Type 1) [CommRing V] [Algebra Z₀ V] (ϖ : V)
    (hgen : Algebra.adjoin Z₀ {ϖ} = ⊤)
    (A : Type 1) [CommRing A] [Algebra Z₀ A] [Algebra V A] [IsScalarTower Z₀ V A]
    (C : Type 1) [CommRing C] [Algebra Z₀ C] [Algebra V C] [IsScalarTower Z₀ V C]
    (μ : A) (w : C) (hA : algebraMap V A ϖ = 1 - μ) (hC : algebraMap V C ϖ = 1 - w) :
    ∃ e : ((A ⊗[Z₀] C) ⧸ Ideal.span {(μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w)}) ≃+* (C ⊗[V] A),
      ∀ (a : A) (c : C), e (Ideal.Quotient.mk _ (a ⊗ₜ[Z₀] c)) = c ⊗ₜ[V] a :=
  nonempty_ringEquiv_quotient_span_tmul_sub_tmul_of_adjoin_singleton_eq_top
    Z₀ V ϖ hgen A C μ w hA hC

/-- The quotient imposes exactly the displayed relation. -/
example (Z₀ : Type) [CommRing Z₀] (A : Type) [CommRing A] [Algebra Z₀ A]
    (C : Type) [CommRing C] [Algebra Z₀ C] (μ : A) (w : C) :
    Ideal.Quotient.mk (Ideal.span {(μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w)})
        ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

end Algebra.TensorProduct
