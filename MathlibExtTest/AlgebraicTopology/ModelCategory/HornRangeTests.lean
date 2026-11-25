/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Horn

@[expose] public section

/-!
# Horn range client test

Minimal downstream client for public `SSet.horn.toTop_map_ι_range_eq_iUnion`.
Restates its exact set-range union equality; not a filling, anodyne, retract,
product, or model-category claim.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.HornRangeTests

universe u

theorem horn_range_client (n : ℕ) (k : Fin (n + 2)) :
    Set.range (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι) =
      ⋃ (j : Fin (n + 2)) (_hj : j ≠ k),
        Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n + 1) {j}ᶜ).ι) :=
  SSet.horn.toTop_map_ι_range_eq_iUnion n k

#check SSet.horn.toTop_map_ι_range_eq_iUnion
#print axioms SSet.horn.toTop_map_ι_range_eq_iUnion

end MathlibExtTest.AlgebraicTopology.ModelCategory.HornRangeTests
