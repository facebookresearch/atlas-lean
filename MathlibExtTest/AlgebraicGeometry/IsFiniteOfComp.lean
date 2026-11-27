/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IsFiniteOfComp

/-! # Consumers for finiteness descending along a composite -/

namespace IsFiniteOfCompTest

universe u

open CategoryTheory AlgebraicGeometry

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g]
    [IsSeparated g] : IsFinite g :=
  AlgebraicGeometry.IsFinite.of_comp_of_surjective f g

end IsFiniteOfCompTest
