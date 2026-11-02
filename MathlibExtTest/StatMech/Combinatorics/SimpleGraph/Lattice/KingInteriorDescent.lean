/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorDescent

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorDescent`

* `kif_not_forall_kingSegmentDown` instantiated with the fjord; the king segment-down condition
  fails at some interior seed of the fjord (`kif_fjord_kingSegmentDown_false`).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingInteriorDescent

example : ¬ ∀ seed : Site 2, kif_KingSegmentDown sdc_fjord seed :=
  kif_not_forall_kingSegmentDown sdc_fjord sdc_fjord_mem_interior_51

example : ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧
    ¬ kif_KingSegmentDown sdc_fjord seed :=
  kif_fjord_kingSegmentDown_false

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingInteriorDescent
