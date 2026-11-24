/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

/-!
# Cores of trivial Kan fibrations

The equivalence-edge core sends any simplicial map with right lifting against
all monomorphisms to another map with the same lifting property. This statement
holds for arbitrary simplicial sets; neither source nor target needs to be a
quasicategory.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MorphismProperty

namespace SSet

/-- The core of a map with right lifting against all monomorphisms again has
right lifting against all monomorphisms. No quasicategory hypothesis is
required. -/
theorem core_map_mem_rlp_monomorphisms {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (monomorphisms SSet.{u}).rlp (core.map p) := by
  let _ : (mapHomotopyCategory p).IsEquivalence :=
    mapHomotopyCategory_isEquivalence_of_rlp_monomorphisms hp
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (core.isPullback_of_reflectsIsomorphisms p) hp

end SSet
