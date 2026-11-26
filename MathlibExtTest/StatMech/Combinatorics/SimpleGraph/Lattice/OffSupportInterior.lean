/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportInterior
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportInterior`

* `jil_floodFill_subset_leftRegion`, `jil_floodFill_eq_offSupportComponent`: instantiated with the
  fjord walk `sdc_fjord` (from `SegmentDownCounterexample`) and its off-support interior site `(5, 1)`.
* `jil_hsegment_subset_leftRegion`: a one-site segment at an interior site.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportInterior

/-- The flood fill of the fjord from its interior site `(5, 1)` stays inside the fjord. -/
example : ffc_floodFill {p | p ∈ sdc_fjord.support} (![5, 1] : Site 2) ⊆ jec_leftRegion sdc_fjord :=
  jil_floodFill_subset_leftRegion sdc_fjord sdc_fjord_off_51 sdc_fjord_interior_51

/-- The flood fill avoiding a walk is the off-support component. -/
example : ffc_floodFill {p | p ∈ sdc_fjord.support} (![5, 1] : Site 2) =
    offSupportComponent sdc_fjord (![5, 1] : Site 2) :=
  jil_floodFill_eq_offSupportComponent sdc_fjord _

/-- A degenerate horizontal segment `[5, 5] × {1}` at an interior site. -/
example : (![5, 1] : Site 2) ∈ jec_leftRegion sdc_fjord :=
  jil_hsegment_subset_leftRegion sdc_fjord (lo := 5) (hi := 5) le_rfl le_rfl le_rfl le_rfl
    (fun t h1 h2 => by rw [show t = 5 by omega]; exact sdc_fjord_off_51) sdc_fjord_interior_51

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportInterior
