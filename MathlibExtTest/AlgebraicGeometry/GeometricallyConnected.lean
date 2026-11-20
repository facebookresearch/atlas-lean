/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricallyConnected

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f :=
  AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected f

/-- The exact composite-descent statement, with no added hypothesis. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g :=
  AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective f g
