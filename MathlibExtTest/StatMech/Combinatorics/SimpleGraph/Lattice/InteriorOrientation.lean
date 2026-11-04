/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InteriorOrientation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorConnected

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.InteriorOrientation`

* `ior_interiorSubset_iff_leftRegion_subset` turns `eaw_unitCell_interiorSubset` into "the inside
  of the unit-cell loop is contained in the unit cell".
* `ior_ExteriorConnected` fails for the unit cell (restated from ExteriorConnected).
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.InteriorOrientation

example : jec_leftRegion (mpl_orbitLoop unitCell ucBase) ⊆ unitCell :=
  (ior_interiorSubset_iff_leftRegion_subset unitCell ucBase).1 eaw_unitCell_interiorSubset

example : ¬ ior_ExteriorConnected unitCell ucBase := exc_oldExteriorConnected_false

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.InteriorOrientation
