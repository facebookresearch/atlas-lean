/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Corridor steps are open after forcing

An edge of a forced set that avoids the origin is open after forcing and removing the origin.

## i. Overview

An edge of `G` not containing the origin is open in `removeSite 0 (forceOpenFinset G ω)`.

## ii. Key results

- `bkm_dcc_step_open_eq_true` : forced edges avoiding the origin are open.

## iii. Table of contents

- A. Open corridor steps

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Open corridor steps -/

lemma bkm_dcc_step_open_eq_true (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hmem : s(x, y) ∈ G) (h0 : (0 : Site d) ∉ s(x, y)) :
    StatMech.Percolation.removeSite 0 (StatMech.Percolation.forceOpenFinset G ω)
      s(x, y) = true := by
  rw [StatMech.Percolation.removeSite_apply_of_notMem h0]
  exact StatMech.Percolation.forceOpenFinset_of_mem hmem ω

end Walls

end StatMech
