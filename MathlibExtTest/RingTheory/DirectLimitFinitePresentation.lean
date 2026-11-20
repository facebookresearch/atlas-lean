/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DirectLimitFinitePresentation

@[expose] public section

open scoped TensorProduct

universe u v w w'

-- Consumer with the original binders.
example {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀),
      Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) :=
  Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    G f R hR A

-- The direct-limit hypothesis is what supplies a stage: with no cocone
-- compatibility there is no reason for the coefficients of a presentation
-- to lie in the range of a single stage map.  This records that the class
-- unfolds to exactly surjectivity, the stated injectivity up to a later
-- stage, and compatibility.
example {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
    (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] (h : IsDirectLimit f g) :
    (∀ m : P, ∃ i, ∃ mi : M i, g i mi = m) ∧
      (∀ i j hij x, g j (f i j hij x) = g i x) :=
  ⟨h.surj, h.compatibility⟩
