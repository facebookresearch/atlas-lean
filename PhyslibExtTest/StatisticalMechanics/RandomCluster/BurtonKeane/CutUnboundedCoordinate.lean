/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutUnboundedCoordinate

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutUnboundedCoordinate`

In the plane:
* `bc_cutUnbounded_coord` shows no cut cluster of the all-closed configuration is infinite (the
  far site it provides would equal the start);
* `bc_cutUnbounded_iff` and `bc_cutUnbounded_converse` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutUnboundedCoordinate

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration only a site is connected to itself. -/
theorem closed_connected_eq {a b : Site 2} (h : Connected 2 closed2 a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [closed2])

/-- Distinct sites have distinct clusters in the all-closed configuration. -/
theorem closed_cluster_ne {a b : Site 2} (hab : a ≠ b) :
    cluster 2 closed2 a ≠ cluster 2 closed2 b := by
  intro h
  have hb : b ∈ cluster 2 closed2 b := SimpleGraph.Reachable.refl b
  rw [← h] at hb
  exact hab (closed_connected_eq hb)

-- No cut cluster of the all-closed configuration is infinite.
example (x : Site 2) : ¬ (cluster 2 (removeSite 0 closed2) x).Infinite := by
  intro h
  obtain ⟨y, ⟨i, hi⟩, hxy⟩ := bc_cutUnbounded_coord closed2 x h ((x 0).natAbs + (x 1).natAbs)
  have hrm : removeSite 0 closed2 = closed2 := by
    funext e; simp [removeSite, closed2]
  rw [hrm] at hxy
  obtain rfl := closed_connected_eq hxy
  fin_cases i <;> simp at hi

-- An infinite cut cluster reaches outside every box.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2)
    (h : (cluster 2 (removeSite 0 ω) x).Infinite) :
    ∃ y, y ∉ box 2 9 ∧ Connected 2 (removeSite 0 ω) x y :=
  (bc_cutUnbounded_iff ω x).mp h 9

-- Reaching outside every box makes the cut cluster infinite.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2)
    (h : ∀ n : ℕ, ∃ y, y ∉ box 2 n ∧ Connected 2 (removeSite 0 ω) x y) :
    (cluster 2 (removeSite 0 ω) x).Infinite :=
  bc_cutUnbounded_converse ω x h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutUnboundedCoordinate
