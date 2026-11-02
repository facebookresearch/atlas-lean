/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitWinds

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitWinds`

* `wwc2_leftRegion_nonempty` on the unit-cell face loop; the origin lies inside it.
* `wwc2_unitCell_primalLoop_isCycle`.
* Not covered: the `p_c(ℤ²) < 1` statements need their hypotheses for every configuration.
-/

@[expose] public section

open StatMech.Lattice
open StatMech.Percolation (origin)

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitOrbitWinds

example : (mpl_orbitLoop unitCell ucBase).IsCycle := wwc2_unitCell_primalLoop_isCycle

example : (jec_leftRegion (mpl_orbitLoop unitCell ucBase)).Nonempty :=
  wwc2_leftRegion_nonempty _ wwc2_unitCell_primalLoop_isCycle

example : origin 2 ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) :=
  wwc2_unitCell_originInside

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitOrbitWinds
