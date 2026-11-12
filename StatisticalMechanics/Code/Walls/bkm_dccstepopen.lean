/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Percolation.HrouteDisjointPaths

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

variable {d : ℕ}












theorem bkm_dcc_step_open (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (hmem : s(x, y) ∈ G)
    (h0 : (0 : Site d) ∉ s(x, y)) :
    StatMech.Lattice.IsOpenEdge d (StatMech.Percolation.removeSite 0
      (StatMech.Percolation.forceOpenFinset G ω)) x y := by
  
  refine ⟨hadj, ?_⟩
  
  
  rw [StatMech.Percolation.removeSite_apply_of_notMem h0]
  
  exact StatMech.Percolation.forceOpenFinset_of_mem hmem ω




theorem bkm_dcc_step_open_eq_true (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hmem : s(x, y) ∈ G) (h0 : (0 : Site d) ∉ s(x, y)) :
    StatMech.Percolation.removeSite 0 (StatMech.Percolation.forceOpenFinset G ω)
      s(x, y) = true := by
  rw [StatMech.Percolation.removeSite_apply_of_notMem h0]
  exact StatMech.Percolation.forceOpenFinset_of_mem hmem ω

end Walls

end StatMech
