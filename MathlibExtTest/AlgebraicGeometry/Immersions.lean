/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Immersions

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

example {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [IsClosedImmersion f]
    [IsClosedImmersion g] [IsReduced A] [IsReduced B]
    (h : Set.range f.base = Set.range g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f :=
  AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq f g h

example {Z X Y : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsClosedImmersion i] [Etale g]
    [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
    IsOpenImmersion i ∧ Etale (i ≫ g) :=
  AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale i g

example {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g :=
  AlgebraicGeometry.IsClosedImmersion.of_isPullback i hg

example {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    Surjective g :=
  AlgebraicGeometry.Surjective.of_isPullback i hg

example {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [UniversallyClosed f₀] : UniversallyClosed f :=
  AlgebraicGeometry.UniversallyClosed.of_isPullback i hg

example {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [IsSeparated f₀] : IsSeparated f :=
  AlgebraicGeometry.IsSeparated.of_isPullback i hg

example {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i)
    [IsProper f₀] [LocallyOfFiniteType f] : IsProper f :=
  AlgebraicGeometry.IsProper.of_isPullback i hg
