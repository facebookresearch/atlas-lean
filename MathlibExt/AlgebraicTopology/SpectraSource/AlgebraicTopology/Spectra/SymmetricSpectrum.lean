/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/SymmetricSpectrum.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SmashPow
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Module
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Closed
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Symmetric

/-!
# The sphere symmetric sequence and symmetric spectra

The sphere sequence `n ↦ S^n = (S¹)^∧n`, with the coordinate-permutation actions of `Σ_n` and the
block-concatenation maps `S^p ∧ S^q → S^(p+q)`, is a braided monoidal functor out of the
finite-bijection groupoid (`PointedSSet.smashPowFunctor PointedSSet.circle`). Regarded as a
symmetric sequence, it is the monoid `SymmetricSequence.smashPow PointedSSet.circle` of smash
powers of the circle, and so a commutative monoid for the Day convolution product: its
multiplication `S ⊗ S ⟶ S` is induced by block concatenation of sphere coordinates
(`SymmetricSequence.smashPow_mul_app_smashMk`) and its unit by `S⁰ ≅ S^0`. Following Hovey,
Shipley and Smith, a symmetric spectrum is a module over this commutative monoid.

Unwinding the universal property of the Day convolution, a symmetric spectrum `X` amounts to a
symmetric sequence of pointed simplicial sets `X_n` with based `Σ_p × Σ_q`-equivariant structure
maps `S^p ∧ X_q → X_(p+q)`, compatible with the unit `S⁰ ≅ S^0` and with block concatenation of
spheres. These iterated structure maps and their laws are developed in
`MathlibExt.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Module`, through the generic
`CategoryTheory.Mod.dayStructureMap` API.

As the sphere monoid is commutative and Day convolution is closed, symmetric spectra have internal
function spectra `Hom_S(X, Y) = (Mod.internalHom X).obj Y`: the equalizer of the two maps
`Hom(X, Y) ⇉ Hom(S ⊗ X, Y)` of internal homs of symmetric sequences given by the actions on `X`
and on `Y`, with the sphere acting through `X`. Spectrum maps `X ⊗ K ⟶ Y` out of the Day
convolution of `X` with a symmetric sequence `K` are the maps of symmetric sequences
`K ⟶ Hom_S(X, Y)` (`Mod.ihomAdjunction`).

The commutative sphere action also gives a native sphere bimodule via
`CategoryTheory.Mod.toBimod`: the right action is obtained by swapping the sphere and
spectrum factors before applying the left action. This adapter is fully faithful.

Through this adapter, symmetric spectra carry the smash product `X ∧ Y`, the balanced tensor
product over the sphere: the coequalizer of the two actions of `S` on the Day convolution `X ⊗ Y`,
with `S` acting through `X`. This is the generic monoidal structure
`CategoryTheory.Mod.monoidalCategory` on modules over a commutative monoid object, with quotient
map `CategoryTheory.Mod.tensorπ : X ⊗ Y ⟶ X ∧ Y`. Its unit is the sphere spectrum
`Mod.regular SymmetricSequence.sphere`. As symmetric sequences form a symmetric monoidal category,
the smash product is symmetric monoidal (`CategoryTheory.Mod.symmetricCategory`), with the twist
`X ∧ Y ≅ Y ∧ X` induced by the symmetry of the Day convolution; commutative monoids for it are
commutative symmetric ring spectra. This is the point-set smash product; deriving it requires
a model structure. It is monoidal closed: `Mod.internalHomAdjunction X` identifies spectrum
maps `X ∧ Y ⟶ Z` with spectrum maps `Y ⟶ Hom_S(X, Z)`. Its counit evaluates function spectra
on representatives of the balanced smash product.

## Main definitions

* `SymmetricSequence.sphere`: the sphere symmetric sequence. Its commutative monoid structure is
  the instance `DayFunctor.monObj`, with commutativity `DayFunctor.isCommMonObj`.
* `SymmetricSpectrum`: symmetric spectra of pointed simplicial sets, the modules over
  `SymmetricSequence.sphere`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

open scoped DayFunctor

/-- The sphere symmetric sequence `n ↦ S^n = (S¹)^∧n`, with the coordinate-permutation actions.
Block concatenation `S^p ∧ S^q → S^(p+q)` and `S⁰ ≅ S^0` make it a commutative monoid for the Day
convolution product, through the instances `DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev SymmetricSequence.sphere : SymmetricSequence.{0} :=
  smashPow PointedSSet.circle

/- The sphere symmetric sequence is a commutative monoid for the Day convolution product. -/
noncomputable example : IsCommMonObj SymmetricSequence.sphere := inferInstance

/-- Symmetric spectra of pointed simplicial sets: the modules over the commutative monoid
`SymmetricSequence.sphere` of symmetric sequences. A symmetric spectrum is a symmetric sequence
`X` with an action `S ⊗ X ⟶ X` for the Day convolution product, satisfying the unit and
associativity laws. -/
abbrev SymmetricSpectrum := Mod SymmetricSequence.{0} SymmetricSequence.sphere

/- The function spectrum `Hom_S(X, Y)` of symmetric spectra, through `Mod.internalHom`. -/
noncomputable example (X Y : SymmetricSpectrum) : SymmetricSpectrum := (Mod.internalHom X).obj Y

/- Spectrum maps `X ⊗ K ⟶ Y` are the maps of symmetric sequences `K ⟶ Hom_S(X, Y)`. -/
noncomputable example (X : SymmetricSpectrum) : Mod.tensorLeft X ⊣ Mod.ihom X :=
  Mod.ihomAdjunction X

/- Symmetric spectra form a monoidal category under the smash product over the sphere. Day
convolution of symmetric sequences preserves colimits on both sides, so the balanced coequalizer
exists and is preserved by smashing. -/
noncomputable example : MonoidalCategory SymmetricSpectrum := inferInstance

/- Function spectra are right adjoint to smashing with a spectrum. -/
noncomputable example (X : SymmetricSpectrum) : tensorLeft X ⊣ Mod.internalHom X :=
  Mod.internalHomAdjunction X

/- The point-set smash and function spectra give the native closed structure. -/
noncomputable example : MonoidalClosed SymmetricSpectrum := inferInstance

/- The unit of the smash product is the sphere spectrum. -/
example : 𝟙_ SymmetricSpectrum = Mod.regular SymmetricSequence.sphere := rfl

/- The smash product of symmetric spectra is symmetric monoidal. -/
noncomputable example : SymmetricCategory SymmetricSpectrum := inferInstance

/- The native bimodule adapter applies to the actual sphere-module carrier. -/
noncomputable example :
    (Mod.toBimod (C := SymmetricSequence.{0}) (A := SymmetricSequence.sphere)).FullyFaithful :=
  Mod.fullyFaithfulToBimod

end MathlibExt.SpectraSource
