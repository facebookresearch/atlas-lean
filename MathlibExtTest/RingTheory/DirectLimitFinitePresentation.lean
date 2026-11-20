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

-- This records that the direct-limit class unfolds to exactly
-- surjectivity, the stated injectivity up to a later stage, and
-- compatibility: all three clauses are exercised here.
example {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
    (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] (h : IsDirectLimit f g) :
    (∀ m : P, ∃ i, ∃ mi : M i, g i mi = m) ∧
      (∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj →
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
          f i k hik mi = f j k hjk mj) ∧
      (∀ i j hij x, g j (f i j hij x) = g i x) :=
  ⟨h.surj, h.inj, h.compatibility⟩
