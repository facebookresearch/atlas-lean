/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothRelDimSub

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v

-- Consumer with the original binders, at a higher universe.
example {X Y Z : Scheme.{v}} [Nonempty X] (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ)
    [SmoothOfRelativeDimension a (f ≫ g)] [SmoothOfRelativeDimension b f] [Surjective f]
    [Smooth g] :
    SmoothOfRelativeDimension (a - b) g ∧ b ≤ a :=
  AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
    f g a b
