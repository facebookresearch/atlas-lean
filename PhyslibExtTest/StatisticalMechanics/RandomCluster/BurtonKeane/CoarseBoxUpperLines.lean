/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoxUpperLines

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoxUpperLines`

In the plane:
* `bc61_wholeBox_severs_upperLines`: the upper lines are a coarse trifurcation at `L = 3`;
* the all-closed configuration is not, so `bc61_coarseTcount` vanishes on it;
* `bc61_pt_outside_boxAround` and `bc61_upperLines_arm_disconnected` at explicit points;
* `bc61_status` gives the upper-lines contrast clause at `L = 3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoxUpperLines

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The all-closed configuration has no coarse trifurcation. -/
theorem closed_not_coarseTrif (L : ℕ) (y : Site 2) : ¬ bc61_IsCoarseTrifurcation closed2 L y := by
  rintro ⟨_, _, _, ⟨_, _, hb⟩, -⟩
  exact absurd hb.2 (by simp [closed2])

-- The upper lines are a coarse trifurcation at the origin for `L = 3`.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines le_rfl

-- The coarse count of the all-closed configuration is zero.
example (L R : ℕ) : bc61_coarseTcount closed2 L R = 0 := by
  rw [bc61_coarseTcount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  exact closed_not_coarseTrif L y (bc61_mem_coarseTrifFinset.mp hy).2

-- The site `(4, 0)` is outside the radius-3 box at the origin.
example : bc57_pt 4 0 ∉ bc61_boxAround 2 3 0 :=
  bc61_pt_outside_boxAround (by norm_num)

-- The arms at heights `1` and `2` are disconnected once the box is removed.
example : ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines)
    (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) (bc57_pt (((3 : ℕ) : ℤ) + 1) 2) :=
  bc61_upperLines_arm_disconnected (by norm_num)

-- After removing the origin, infinite low clusters of the forced upper lines are connected.
example (G : Finset (Sym2 (Site 2))) (a a' : Site 2) (ha : a 1 ≤ 1) (ha' : a' 1 ≤ 1)
    (hi : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
    (hi' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' :=
  bc61_status.2.1 (L := 3) le_rfl G a a' ha ha' hi hi'

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoxUpperLines
