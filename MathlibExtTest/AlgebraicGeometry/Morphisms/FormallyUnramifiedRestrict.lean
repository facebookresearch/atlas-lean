/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Morphisms.FormallyUnramifiedRestrict

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- Consumer with explicit universes: the restriction of a composite over `U` is formally
unramified when both restrictions are. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    [FormallyUnramified (g ∣_ U)] [FormallyUnramified (f ∣_ g ⁻¹ᵁ U)] :
    FormallyUnramified ((f ≫ g) ∣_ U) :=
  FormallyUnramified.morphismRestrict_comp f g U

/-- Over the whole target, the restrictions are formally unramified when `f` and `g` are. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyUnramified f]
    [FormallyUnramified g] : FormallyUnramified ((f ≫ g) ∣_ ⊤) := by
  have : FormallyUnramified (g ∣_ ⊤) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict g ⊤).flip ‹_›
  have : FormallyUnramified (f ∣_ g ⁻¹ᵁ ⊤) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f (g ⁻¹ᵁ ⊤)).flip ‹_›
  exact FormallyUnramified.morphismRestrict_comp f g ⊤
