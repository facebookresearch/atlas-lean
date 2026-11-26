/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkLeftRegion

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkLeftRegion`

* `latticeDualWalkHasBdEdgeRegion_of_edgeless`: the matching hypothesis holds for the edgeless
  dual graph `⊥`, so `LatticeDualWalkHasBdEdgeRegion` is satisfiable;
* `dualWalkBoundsRegion_lattice_of_bdEdgeMatch` then gives `DualWalkBoundsRegion` for `⊥`;
* `dualWalkBoundsRegion_iff_closedDualWalkParity` on the one-vertex graph `Fin 1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.DualWalkLeftRegion

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

/-- The edgeless graph satisfies the boundary-edge matching hypothesis. -/
theorem bot_hasBdEdgeRegion : LatticeDualWalkHasBdEdgeRegion (⊥ : SimpleGraph (Site 2)) :=
  latticeDualWalkHasBdEdgeRegion_of_edgeless (by simp)

-- The lattice reduction applied to the edgeless dual graph.
example : DualWalkBoundsRegion (hypercubicLattice 2) (⊥ : SimpleGraph (Site 2)) crossEdge :=
  dualWalkBoundsRegion_lattice_of_bdEdgeMatch bot_hasBdEdgeRegion

-- Region boundary ↔ cycle parity on the one-vertex graph.
example : DualWalkBoundsRegion (⊥ : SimpleGraph (Fin 1)) ⊥ (Equiv.refl _) ↔
    ClosedDualWalkParity (⊥ : SimpleGraph (Fin 1)) ⊥ (Equiv.refl _) :=
  dualWalkBoundsRegion_iff_closedDualWalkParity
    (fun u v => by rw [Subsingleton.elim u v]) (Equiv.refl _) (by simp)

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.DualWalkLeftRegion
