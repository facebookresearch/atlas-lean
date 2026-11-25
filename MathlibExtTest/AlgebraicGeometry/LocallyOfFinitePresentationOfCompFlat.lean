/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LocallyOfFinitePresentationOfCompFlat

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

-- `exactSource` consumer with the original binders: the conclusion is
-- local finite presentation of `g`, from local finite presentation of
-- the composite `f ≫ g` along a flat surjective quasi-compact locally
-- finitely presented cover `f`.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] [QuasiCompact f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g

-- The same consumer in a different universe.
example {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] [QuasiCompact f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g

-- Boundary consumer: when the cover is the identity, the hypothesis on
-- the composite is the conclusion itself, and no flatness argument is
-- needed beyond the identity cover being flat, surjective and
-- quasi-compact.
example {Y Z : Scheme.{u}} (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective (𝟙 Y) g
