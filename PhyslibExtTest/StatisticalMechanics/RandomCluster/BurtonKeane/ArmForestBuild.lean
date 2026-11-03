/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestBuild

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestBuild`

* `bfk_isCoarseTrif`: in the upper-lines configuration every `bc57_pt m h₀` (`h₀ ≥ 0`) is a
  coarse trifurcation, here at scale `L = 3` and the point `(0, 0)`;
* `bfk_coarseTcount_lower` at `L = 3`, `R = 2`;
* `bfk_rightArm_infinite` for a concrete arm;
* `bfk_perConfigForest_false` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestBuild

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- A concrete coarse trifurcation of the upper-lines configuration.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (bc57_pt 0 0) :=
  bfk_isCoarseTrif le_rfl le_rfl

-- The coarse trifurcation count at `R = 2` is at least `3 * 5`.
example : (2 + 1) * (2 * 2 + 1) ≤ bc61_coarseTcount bc60_upperLines 3 2 :=
  bfk_coarseTcount_lower le_rfl 2

-- The right arm at height `1` is infinite after removing the box.
example : (cluster 2 (removeSites (bc61_boxAround 2 3 (bc57_pt 0 0)) bc60_upperLines)
    (bc57_pt (0 + ((3 : ℕ) : ℤ) + 1) 1)).Infinite :=
  bfk_rightArm_infinite le_rfl

-- A per-configuration forest with vanishing leaf density is impossible.
example (F : ℕ → Finset (Sym2 (Site 2)))
    (hdens : Filter.Tendsto
      (fun R => ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0)) :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
        bpe_CoarseForestNoBnd ω 3 R (bel_leafOpenCount (F R) ω)) :=
  bfk_perConfigForest_false le_rfl F hdens

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestBuild
