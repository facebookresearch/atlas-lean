/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreTrivialFibration

/-!
# Tests for cores of trivial Kan fibrations
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MorphismProperty

namespace SSet

/-- The theorem applies to arbitrary simplicial sets, without quasicategory
instances on either endpoint. -/
example {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (monomorphisms SSet.{u}).rlp (core.map p) :=
  core_map_mem_rlp_monomorphisms hp

end SSet
