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

* `pcy_fig8_structural_fix`: the figure-eight is not a cycle and satisfies `pcy_CrossArcThick`
  only vacuously.
* `pcy_CrossArcThick` holds for the staircase walks and the fjord.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle

example : ¬ wpc_fig8.IsCycle := pcy_fig8_not_cycle

example : pcy_CrossArcThick wpc_fig8 (![1, 1] : Site 2) ∧
    ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) :=
  ⟨pcy_fig8_crossArcThick, pcy_fig8_structural_fix.1⟩

example : pcy_CrossArcThick ksd_stair (![1, 1] : Site 2) ∧
    pcy_CrossArcThick kda_stairDR (![3, 1] : Site 2) :=
  ⟨pcy_ksd_crossArcThick, pcy_kda_crossArcThick⟩

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationCycle
