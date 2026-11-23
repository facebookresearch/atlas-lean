/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.InvertibleBaseScalar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.DescentCharacter

universe u v

/-- Consumer with the original binders. -/
theorem exactSource
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c :=
  existsUnique_isBaseScalar_of_isInvertible_of_bijective f hH0 hM σ

/-- The same statement one universe higher. -/
theorem exactSourceHigher
    {X : Scheme.{v}} {R : Type v} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c :=
  existsUnique_isBaseScalar_of_isInvertible_of_bijective f hH0 hM σ

/-- Boundary: without bijectivity the scalar need not be unique: over
`X = Spec (R × R)` with `f` the first projection composed with the
diagonal identification, distinct scalars can act identically. Here
the cheap algebraic shadow: the map `R → R × R` is not surjective,
so a section of the product need not come from the base. -/
example : ¬ Function.Surjective (fun c : ℤ => (c, c + 1)) := by
  intro h
  obtain ⟨c, hc⟩ := h (0, 0)
  have h1 : c = 0 := congrArg Prod.fst hc
  have h2 : c + 1 = 0 := congrArg Prod.snd hc
  omega
