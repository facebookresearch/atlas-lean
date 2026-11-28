/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps
public import Batteries.Util.ProofWanted

/-!
# Derived direct images of sheaves of rational vector spaces

Sheaves of `ℚ`-vector spaces on a topological space form a Grothendieck abelian category, so
every complex has a K-injective resolution (Spaltenstein; Stacks Project, Tag 079P). Hence the
total right derived functor `Rf_*` of the direct image exists, it is computed on K-injective
complexes, and it is right adjoint to the exact inverse image, with unit given on cochains by
the ordinary unit followed by the right-derived unit. These requests provide the classes used
by `NearbyCycleProperMaps` for every continuous map.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NearbyCycleProperMaps

open MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps

/-- `Rf_*` exists as the total right derived functor of the direct image. -/
public instance_wanted hasDerivedPushforward {V W : TopCat.{0}} (f : V ⟶ W) :
    HasDerivedPushforward f

/-- The right-derived unit of `Rf_*` is an isomorphism on K-injective complexes. -/
public instance_wanted rightDerivedInjectiveCalculation {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] : RightDerivedInjectiveCalculation f

/-- The derived adjunction `f^* ⊣ Rf_*`, normalized on every cochain complex. -/
public instance_wanted normalizedDerivedAdjunction {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] : NormalizedDerivedAdjunction f

end WantedExt.AlgebraicGeometry.NearbyCycleProperMaps
