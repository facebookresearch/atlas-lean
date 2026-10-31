/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing`

In the plane:
* `bc8_noCrossing` for the all-closed configuration at `(1,0)` and `(0,1)`;
* `bc8_cut_ne_iff_disconnected`: their cut clusters differ, so they are disconnected;
* `bc8_threeArms_noCrossing` in conditional form on `threeMeetBox 2 6`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing

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

-- The no-crossing package holds for any two sites.
example : bc8_NoCrossing closed2 ![1, 0] ![0, 1] :=
  bc8_noCrossing closed2 _ _

-- Distinct cut clusters are disconnected.
example : ¬ Connected 2 (removeSite 0 closed2) ![1, 0] ![0, 1] := by
  have hrm : removeSite 0 closed2 = closed2 := by
    funext e; simp [removeSite, closed2]
  refine bc8_cut_ne_iff_disconnected.mp ?_
  rw [hrm]
  exact closed_cluster_ne fun h => by simpa using congrFun h 0

-- Any configuration meeting a box in three infinite clusters has three non-crossing cut clusters.
example (ω : ConfigSpace (Sym2 (Site 2))) (hω : ω ∈ threeMeetBox 2 6) : ∃ x₁ x₂ x₃ : Site 2,
    (cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧
    (cluster 2 (removeSite 0 ω) x₃).Infinite ∧
    bc8_NoCrossing ω x₁ x₂ ∧ bc8_NoCrossing ω x₁ x₃ ∧ bc8_NoCrossing ω x₂ x₃ :=
  bc8_threeArms_noCrossing 6 ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing
