/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RowLinkedDescent
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RowLinkedDescent`

* `rlc_offSupportInterior_finite` and `rlc_exists_lexMin_seed` for the fjord walk `sdc_fjord`
  (from `SegmentDownCounterexample`), seeded at its interior site `(5, 1)`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RowLinkedDescent

/-- The off-support interior of the fjord is finite. -/
example : (jil_offSupportInterior sdc_fjord).Finite := rlc_offSupportInterior_finite sdc_fjord

/-- The fjord's off-support interior has a lexicographically least site. -/
example : ∃ seed ∈ jil_offSupportInterior sdc_fjord, ∀ z ∈ jil_offSupportInterior sdc_fjord,
    rlc_lexMeasure 10 seed ≤ rlc_lexMeasure 10 z :=
  rlc_exists_lexMin_seed sdc_fjord sdc_fjord_mem_interior_51 10

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RowLinkedDescent
