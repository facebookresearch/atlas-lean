/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DownArmForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DownArmForest`

In the plane, with the all-closed configuration (no trifurcations):
* `bc30_GlobalCutDownArmData` is satisfiable (`bc30_globalCutDownArmData_of_noTrif`);
* `bc30_Tcount_le_boundary_of_data` and `bc30_rootedArmDivergence_of_data` apply to it;
* `bc30_upArmFunneling_clauses_consistent` on `Site 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DownArmForest

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

/-- The all-closed configuration has no trifurcation. -/
theorem closed_not_trif (x : Site 2) : ¬ IsTrifurcation 2 closed2 x := by
  rintro ⟨a₁, a₂, -, ⟨h12, -, -⟩, ⟨c1, c2, -⟩, -⟩
  exact h12 ((closed_connected_eq c1).symm.trans (closed_connected_eq c2))

/-- A constant rank. -/
def rk : Site 2 → ℕ ×ₗ ℕ := fun _ => toLex (0, 0)

/-- Global-cut down-arm data for the all-closed configuration. -/
theorem closed_data (n : ℕ) : bc30_GlobalCutDownArmData closed2 n rk :=
  bc30_globalCutDownArmData_of_noTrif closed2 n rk fun x _ => closed_not_trif x

-- The count bound from the data (rank injectivity holds vacuously).
example : Tcount 2 closed2 2 ≤ boxSV_boundaryCard 2 2 :=
  bc30_Tcount_le_boundary_of_data closed2 2 (by norm_num) rk
    (fun x _ h => absurd h (closed_not_trif x)) (closed_data 2)

-- The data give rooted arm divergence.
example (n : ℕ) : rfp_RootedArmDivergence closed2 n :=
  bc30_rootedArmDivergence_of_data closed2 n rk (fun x _ h => absurd h (closed_not_trif x))
    (closed_data n)

-- The up-arm funneling clauses are jointly consistent.
example : ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y by' uy bx₁ bx₂ : Site 1),
    ¬ Connected 1 (removeSite y ω) by' uy ∧ Connected 1 (removeSite y ω) bx₁ uy ∧
    ¬ Connected 1 (removeSite y ω) by' bx₂ ∧ Connected 1 (removeSite y ω) bx₂ uy :=
  bc30_upArmFunneling_clauses_consistent

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DownArmForest
