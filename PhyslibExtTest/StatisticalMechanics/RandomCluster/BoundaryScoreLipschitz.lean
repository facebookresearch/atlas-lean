/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryScoreLipschitz

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryScoreLipschitz`

On the one-edge graph `⊤` on `Fin 2`:
* `bcScore_le_add_configHammingCount` between the all-open and all-closed configurations, with the
  empty wiring;
* `bcScore_le_add_configHammingCount_add_boundaryGap` across the wirings `⊤` and `⊥`, with the
  boundary gap witnessed by `M = numClustersBC ⊤ ⊤ η` (so `hgap` holds by `Nat.le_add_left`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryScoreLipschitz

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

-- The score changes by at most the Hamming distance.
example : openCount G2 allOpen + 2 * numClustersBC G2 ⊥ allOpen ≤
    openCount G2 allClosed + 2 * numClustersBC G2 ⊥ allClosed +
      configHammingCount G2 allOpen allClosed :=
  bcScore_le_add_configHammingCount G2 ⊥ _ _

-- The two-wiring version with an explicit boundary gap.
example : openCount G2 allOpen + 2 * numClustersBC G2 ⊤ allOpen ≤
    openCount G2 allClosed + 2 * numClustersBC G2 ⊥ allClosed +
      configHammingCount G2 allOpen allClosed + 2 * numClustersBC G2 ⊤ allClosed :=
  bcScore_le_add_configHammingCount_add_boundaryGap G2 ⊤ ⊥ _ _ _ (Nat.le_add_left _ _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryScoreLipschitz
