/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Smooth.NilpotentComparison

@[expose] public section

universe u v w x

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {A : Type v} {A' : Type w} {A₀ : Type x} [CommRing A] [CommRing A'] [CommRing A₀]
    [Algebra R A] [Algebra R A'] [Algebra R A₀]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
    (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
    (hg : Function.Surjective g) (hg' : Function.Surjective g')
    (hkg : RingHom.ker g = I.map (algebraMap R A))
    (hkg' : RingHom.ker g' = I.map (algebraMap R A')) :
    ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g :=
  Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
    I hI g g' hg hg' hkg hkg'

-- Higher-universe consumer: the base and algebras live in `Type 1`.
example
    {R : Type 1} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {A A' A₀ : Type 1} [CommRing A] [CommRing A'] [CommRing A₀]
    [Algebra R A] [Algebra R A'] [Algebra R A₀]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
    (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
    (hg : Function.Surjective g) (hg' : Function.Surjective g')
    (hkg : RingHom.ker g = I.map (algebraMap R A))
    (hkg' : RingHom.ker g' = I.map (algebraMap R A')) :
    ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g :=
  Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
    I hI g g' hg hg' hkg hkg'

-- Boundary: when the common ideal is zero, the two maps themselves are
-- isomorphisms, and the comparison is the expected composite.
example
    {R : Type u} [CommRing R]
    {A : Type v} {A' : Type w} {A₀ : Type x} [CommRing A] [CommRing A'] [CommRing A₀]
    [Algebra R A] [Algebra R A'] [Algebra R A₀]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
    (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
    (hg : Function.Surjective g) (hg' : Function.Surjective g')
    (hkg : RingHom.ker g = (⊥ : Ideal R).map (algebraMap R A))
    (hkg' : RingHom.ker g' = (⊥ : Ideal R).map (algebraMap R A')) :
    ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g :=
  Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
    ⊥ ⟨1, pow_one ⊥⟩ g g' hg hg' hkg hkg'
