/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus

@[expose] public section

/-!
# Hilbert class fields of number fields

This file introduces the predicate `NumberField.IsHilbertClassField K L`, expressing the
finite number-field characterization of the Hilbert class field of `K`: `L / K` is a
finite-dimensional abelian Galois extension, unramified at every finite height-one prime of
`𝓞 K` and at every infinite place, and maximal with this property.

Maximality means that every finite-dimensional abelian Galois number field `M / K` which is
unramified at every finite height-one prime of `𝓞 K` and at infinite places admits a
`K`-algebra embedding `M →ₐ[K] L`.

The maximality quantifier ranges over competitors `M` in the same universe as `K` and `L`.
This keeps the predicate a single `Prop` without an extra universe parameter while remaining
faithful to the informal characterization. No existence, uniqueness, ray-class-field
equivalence, or concrete instances are asserted here.
-/

open scoped NumberField

namespace NumberField

universe u

/-- **Hilbert class field of a number field.** Let $K$ and $L$ be number fields with $L$ an
extension of $K$. Then $L$ is a Hilbert class field of $K$ if $L/K$ is a finite-dimensional
abelian Galois extension, every nonzero prime ideal of the ring of integers $\mathcal{O}_K$ is
unramified in $\mathcal{O}_L$, every infinite place of $L$ is unramified over $K$, and $L$ is
maximal with these properties: every number field $M$ that is a finite-dimensional abelian Galois
extension of $K$, such that every nonzero prime ideal of $\mathcal{O}_K$ is unramified in
$\mathcal{O}_M$ and every infinite place of $M$ is unramified over $K$, admits a $K$-algebra
homomorphism $M \to L$. -/
structure IsHilbertClassField (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] : Prop where
  /-- `L / K` is finite-dimensional. -/
  finiteDimensional : FiniteDimensional K L
  /-- `L / K` is abelian Galois. -/
  isAbelianGalois : IsAbelianGalois K L
  /-- Every finite height-one prime of `𝓞 K` is unramified in `𝓞 L`. -/
  isUnramified_finite :
    ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal
  /-- `L / K` is unramified at every infinite place. -/
  isUnramified_infinite : IsUnramifiedAtInfinitePlaces K L
  /-- Maximality: every admissible competitor `M / K` embeds into `L` over `K`. -/
  maximal : ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M],
    FiniteDimensional K M →
    IsAbelianGalois K M →
    (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal) →
    IsUnramifiedAtInfinitePlaces K M →
    Nonempty (M →ₐ[K] L)

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- **Abelian unramified extensions embed in the Hilbert class field.** Let $K$ and $L$ be number
fields with $L$ an extension of $K$ that is a Hilbert class field of $K$. If $M$ is a number field
that is a finite-dimensional abelian Galois extension of $K$, such that every nonzero prime ideal
of the ring of integers $\mathcal{O}_K$ is unramified in $\mathcal{O}_M$ and every infinite place
of $M$ is unramified over $K$, then there is a $K$-algebra homomorphism $M \to L$. -/
theorem IsHilbertClassField.apply_maximal {M : Type u} [Field M] [NumberField M]
    [Algebra K M] (h : IsHilbertClassField K L)
    (hfin : FiniteDimensional K M)
    (hgal : IsAbelianGalois K M)
    (hfinU : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal)
    (hinfU : IsUnramifiedAtInfinitePlaces K M) : Nonempty (M →ₐ[K] L) :=
  h.maximal M hfin hgal hfinU hinfU

end NumberField

end
