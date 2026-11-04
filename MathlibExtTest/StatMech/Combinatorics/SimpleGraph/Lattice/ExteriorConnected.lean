/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorConnected

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorConnected`

* `exc_SupportOddInK` holds for the unit cell; the site `(0, -1)` outside the unit cell lies on its
  loop.
* The refutation `exc_oldExteriorConnected_false` is restated.
* `exc_exterior_reaches_farLeft` is applied with `F = box 2 0` at the exterior site `(5, 0)`.
* Not covered: `exc_OffSupportReachesExterior` for a concrete set (needs explicit lattice paths
  around the loop; more than the test budget).
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorConnected

example : exc_SupportOddInK unitCell ucBase := exc_unitCell_supportOddInK

example : (![0, -1] : Site 2) ∈ (mpl_orbitLoop unitCell ucBase).support :=
  exc_unitCell_offK_on_support

example : ¬ ior_ExteriorConnected unitCell ucBase := exc_oldExteriorConnected_false

example (hz : (![5, 0] : Site 2) ∈ exterior 2 0) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk ![5, 0] z0,
      (∀ w ∈ p.support, w ∉ box 2 0) ∧ (∀ q ∈ box 2 0, z0 0 ≤ q 0) :=
  exc_exterior_reaches_farLeft (box 2 0) 0 le_rfl ![5, 0] hz

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorConnected
