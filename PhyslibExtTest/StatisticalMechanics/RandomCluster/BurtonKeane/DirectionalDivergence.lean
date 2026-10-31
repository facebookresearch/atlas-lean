/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DirectionalDivergence

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DirectionalDivergence`

In the plane, with the all-closed configuration (no trifurcations):
* `fpc_DirectionalChosenArmDivergence` is satisfiable via `fpc_directionalDivergence_of_noTrif`;
* `fpc_pairwiseCutSeparation_of_directionalDivergence` and
  `fpc_Tcount_le_boundary_of_directionalDivergence` apply to it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DirectionalDivergence

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

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

/-- The all-closed configuration has no trifurcation. -/
theorem closed_not_trif (x : Site 2) : ¬ IsTrifurcation 2 closed2 x := by
  rintro ⟨a₁, a₂, -, ⟨h12, -, -⟩, ⟨c1, c2, -⟩, -⟩
  exact h12 ((closed_connected_eq c1).symm.trans (closed_connected_eq c2))

/-- Directional arm divergence for the all-closed configuration. -/
theorem closed_div (n : ℕ) : fpc_DirectionalChosenArmDivergence closed2 n :=
  fpc_directionalDivergence_of_noTrif closed2 n fun x _ => closed_not_trif x

-- Pairwise cut separation follows.
example (n : ℕ) : fac_PairwiseCutSeparation closed2 n :=
  fpc_pairwiseCutSeparation_of_directionalDivergence closed2 n (closed_div n)

-- So does the count bound.
example : Tcount 2 closed2 3 ≤ boxSV_boundaryCard 2 3 :=
  fpc_Tcount_le_boundary_of_directionalDivergence closed2 3 (by norm_num) (closed_div 3)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DirectionalDivergence
