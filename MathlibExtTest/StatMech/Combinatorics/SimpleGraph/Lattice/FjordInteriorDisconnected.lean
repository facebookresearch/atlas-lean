/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FjordInteriorDisconnected

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.FjordInteriorDisconnected`

* `iwc_interior_disconnected`: the fjord interior sites `(5, 1)` and `(1, 1)` are not joined by a
  lattice walk avoiding the fjord.
* `iwc_exists_rowLinked_seed_false`: the fjord has no row-linked interior seed.
* Membership of `(5, 1)` (not `(1, 1)`) in the right pocket.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FjordInteriorDisconnected

example : ¬ ∃ p : (hypercubicLattice 2).Walk (![5, 1] : Site 2) (![1, 1] : Site 2),
    ∀ w ∈ p.support, w ∉ sdc_fjord.support :=
  iwc_interior_disconnected.2.2

example : ¬ ∃ seed ∈ jil_offSupportInterior sdc_fjord, jil_RowLinked sdc_fjord seed :=
  iwc_exists_rowLinked_seed_false

example : (![5, 1] : Site 2) ∈ iwc_RightPocket ∧ (![1, 1] : Site 2) ∉ iwc_RightPocket :=
  ⟨iwc_mem_rightPocket_51, iwc_not_rightPocket_11⟩

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FjordInteriorDisconnected
