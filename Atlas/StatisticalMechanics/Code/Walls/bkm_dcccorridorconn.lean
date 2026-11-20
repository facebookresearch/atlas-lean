/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Percolation.HrouteDisjointPaths

open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}
















theorem bkm_dcc_corridor_conn (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {p q : Site d}
    (h : Relation.ReflTransGen (CorridorStep G) p q) :
    Connected d (removeSite 0 (forceOpenFinset G ω)) p q := by
  induction h with
  | refl => exact connected_rfl
  | tail _ hstep ih =>
    obtain ⟨hadj, hmem, h0⟩ := hstep
    exact ih.trans
      (IsOpenEdge.connected (isOpenEdge_removeSite_forceOpen_step ω G hadj hmem h0))

end Walls

end StatMech
