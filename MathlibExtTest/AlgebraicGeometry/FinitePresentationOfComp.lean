/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FinitePresentationOfComp

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

-- Consumer with the original binders.
example {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType h hg

-- Higher-universe consumer.
example {X Y Z : Scheme.{v}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType h hg

-- Boundary: with the second morphism the identity, finite presentation of
-- the composite is finite presentation of the first morphism itself.
example {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : LocallyOfFinitePresentation (f ≫ 𝟙 Y)) : LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType (g := 𝟙 Y)
    (by rw [Category.comp_id] at h; exact h) inferInstance
