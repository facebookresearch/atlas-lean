/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle`

* `pcy_fig8_not_cycle`: the figure-eight walk is not a cycle.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle

example : ¬ wpc_fig8.IsCycle := pcy_fig8_not_cycle

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle
