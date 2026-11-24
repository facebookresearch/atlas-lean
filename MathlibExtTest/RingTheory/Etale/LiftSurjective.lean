/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.LiftSurjective

@[expose] public section

open scoped TensorProduct

universe u v w

/-- Consumer with the original binders, now universe-polymorphic: the witness
lies in the universe of `C`. -/
example {C : Type u} {C₀ : Type v} [CommRing C] [CommRing C₀] [Algebra C C₀]
    (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type w) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧
      Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) :=
  Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective hC S₀

/-- Higher-universe consumer: carriers in `Type 1`, `Type 2`, and `Type 3`. -/
example {C : Type 1} {C₀ : Type 2} [CommRing C] [CommRing C₀] [Algebra C C₀]
    (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type 3) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type 1) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧
      Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) :=
  Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective hC S₀
