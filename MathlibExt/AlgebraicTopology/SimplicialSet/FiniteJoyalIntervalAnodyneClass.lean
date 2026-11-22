/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGenerators

/-!
# The auxiliary anodyne class

This is the chosen double lifting closure of the actual inner horns and
finite-interval endpoint corners. Its right lifting class is exactly the
right lifting class of that generator family, by the native lifting
Galois identity. The geometric properties and identification with the
smallest saturated class are separate results.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet.joyalInterval

/-- Maps with the left lifting property against every map with the right
lifting property against the actual auxiliary generator family. -/
def auxiliaryAnodyneExtensions : MorphismProperty SSet.{u} :=
  auxiliaryGenerators.rlp.llp

/-- Right lifting against the auxiliary anodyne class is exactly right
lifting against its actual specified generators. -/
@[simp]
lemma auxiliaryAnodyneExtensions.rlp_eq :
    auxiliaryAnodyneExtensions.{u}.rlp = auxiliaryGenerators.{u}.rlp :=
  MorphismProperty.rlp_llp_rlp auxiliaryGenerators

end SSet.joyalInterval
