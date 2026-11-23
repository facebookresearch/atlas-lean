/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DerivedSelfIntersections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.DerivedSelfIntersections

universe u

attribute [local instance] HasDerivedCategory.standard

-- The conormal sheaf is the pullback of the ideal sheaf, for a closed immersion.
example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] :
    conormalModule i = (Scheme.Modules.pullback i).obj (idealModule i) := rfl

-- The formal model of a derived object has the cohomology sheaves of the object in each
-- degree and zero differentials.
example {X : Scheme.{u}} (M : D X) (n : ℤ) :
    (formalCohomologyComplex M).X n = (DerivedCategory.homologyFunctor X.Modules n).obj M :=
  rfl

example {X : Scheme.{u}} (M : D X) (n m : ℤ) : (formalCohomologyComplex M).d n m = 0 := rfl

-- Formality is an isomorphism to that formal model.
example {X : Scheme.{u}} (M : D X)
    (e : M ≅ DerivedCategory.Q.obj (formalCohomologyComplex M)) : IsFormal M := ⟨e⟩

-- A first neighborhood of `i` factors `i` through the thickening.
example {X Y : Scheme.{u}} (i : X ⟶ Y) (N : FirstNeighborhood i) :
    N.reduction ≫ N.inclusion = i := N.factorization

-- A conormal extension restricts to the conormal sheaf, so a closed immersion admitting one
-- has a conormal sheaf isomorphic to a restriction of a finite locally free sheaf.
example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (N : ConormalExtension i) :
    Nonempty ((Scheme.Modules.pullback N.neighborhood.reduction).obj N.bundle ≅
      conormalModule i) := ⟨N.restriction⟩
