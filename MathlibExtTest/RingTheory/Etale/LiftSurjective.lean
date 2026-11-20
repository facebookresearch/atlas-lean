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

/-- Consumer with the original binders. -/
example {C C₀ : Type} [CommRing C] [CommRing C₀] [Algebra C C₀]
    (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧
      Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) :=
  Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective hC S₀
