/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample`

* The fjord walk `sdc_fjord`: two off-support interior sites, `(5, 1)` and `(1, 1)`.
* The segment-down condition fails for the fjord at some interior seed (`sdc_segmentDown_false`),
  and for every walk with nonempty off-support interior it fails for some seed
  (`sdc_not_forall_segmentDown`, instantiated with the fjord).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

example : (![5, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord ∧
    (![1, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord :=
  ⟨sdc_fjord_mem_interior_51, sdc_fjord_mem_interior_11⟩

example : ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧
    ¬ rlc_SegmentDown sdc_fjord seed :=
  sdc_segmentDown_false

example : ¬ ∀ seed : Site 2, rlc_SegmentDown sdc_fjord seed :=
  sdc_not_forall_segmentDown sdc_fjord sdc_fjord_mem_interior_51

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample
