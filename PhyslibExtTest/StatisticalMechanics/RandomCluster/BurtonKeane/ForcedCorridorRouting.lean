/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedCorridorRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedCorridorRouting`

* `bc2_corridorChain_in_union` for the axis-`0` corridor inside a larger planar edge set;
* `bc2_PairwiseSeparated` is satisfiable: in `Site 3` the empty configuration separates the three
  unit ray points (`bc2_pairwiseSeparated_zero_of_cutDisconnected`);
* `bc2_csc_of_forcedCorridorRouting` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedCorridorRouting

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Percolation.DisjointPaths _root_.StatMech.Walls

-- A corridor chain inside any edge set containing the corridor.
example (H : Finset (Sym2 (Site 2))) :
    Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges (0 : Fin 2) (3 + 1) ∪ H))
      (hrHD_rayPt 0 1) (hrHD_rayPt 0 (((3 : ℕ) : ℤ) + 1)) :=
  bc2_corridorChain_in_union 0 3 _ Finset.subset_union_left

/-- In the empty configuration with the origin removed, only a site reaches itself. -/
theorem bot_conn_eq {a b : Site 3} (h : Connected 3 (removeSite 0 ⊥) a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [removeSite])

/-- Distinct unit ray points are not connected in the empty configuration. -/
theorem bot_sep {i j : Fin 3} (hij : i ≠ j) :
    ¬ Connected 3 (removeSite 0 ⊥) (hrHD_rayPt i 1) (hrHD_rayPt j 1) := fun h => by
  have := congrFun (bot_conn_eq h) i
  simp [hrHD_rayPt, hij] at this

-- The empty configuration separates the three corridor mouths.
example : bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site 3))) 0 1 2 0 0 0 :=
  bc2_pairwiseSeparated_zero_of_cutDisconnected _ 0 1 2 (bot_sep (by decide))
    (bot_sep (by decide)) (bot_sep (by decide))

-- Forced corridor routing gives distinct-cluster corridors.
example (ω : ConfigSpace (Sym2 (Site 3))) (h : bc2_ForcedCorridorRouting ω) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedCorridorRouting
