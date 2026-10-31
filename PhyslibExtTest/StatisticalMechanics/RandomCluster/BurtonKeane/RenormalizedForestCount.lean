/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RenormalizedForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RenormalizedForestCount`

* `bc25_bridge_nonvacuous`: some configuration of `ℤ²` has a coarse trifurcation at scale zero,
  which `bc25_isTrifurcation_of_coarseTrif_zero` turns into a trifurcation at the origin;
* `bc25_Tcount_zero_le_box` applied;
* refutation: the forest hypothesis `∀ ω n, 1 ≤ n → aed_GlobalForestArms ω n` of
  `bc25_burton_keane_uniqueness_of_forest` is false for `d ≥ 1` (via
  `aed_Tcount_le_boundary_of_globalForestArms` and `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RenormalizedForestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory

variable {d : ℕ}

-- The scale-zero bridge is non-vacuous: some configuration has a trifurcation at the origin.
example : ∃ ω : ConfigSpace (Sym2 (Site 2)), IsTrifurcation 2 ω (0 : Site 2) := by
  obtain ⟨ω, h, -⟩ := bc25_bridge_nonvacuous
  exact ⟨ω, bc25_isTrifurcation_of_coarseTrif_zero h⟩

-- The trifurcation count at `n = 0` is at most the volume.
example (ω : ConfigSpace (Sym2 (Site d))) : Tcount d ω 0 ≤ (boxFinsetBK d 0).card :=
  bc25_Tcount_zero_le_box ω

-- The coarse-to-classical chain at scale zero.
example (ω : ConfigSpace (Sym2 (Site d))) (h : IsCanonicalTrifurcation d ω (0 : Site d)) :
    IsTrifurcation d ω (0 : Site d) :=
  bc25_coarseTrif_zero_chain.2 (bc25_coarseTrif_zero_chain.1 h)

-- The configuration-wide forest hypothesis is unsatisfiable in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    aed_Tcount_le_boundary_of_globalForestArms ω n hn (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RenormalizedForestCount
