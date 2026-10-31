/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.EscapingArmForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.EscapingArmForest`

In the plane:
* `bc32_escapingClause_nonvacuous`, with `bc32_pos_edge_open` and `bc32_arc_outside` at explicit
  values;
* `bc32_EscapingDownArmData` is satisfiable for the all-closed configuration (no trifurcations),
  and `bc32_Tcount_le_boundary_of_escapingDownArmData` applies.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.EscapingArmForest

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

-- The escaping clause is non-vacuous.
example : ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2) (T : Finset (Site 2)),
    a ∉ T ∧ x ∈ T ∧ (∀ m : ℕ, ∃ z, z ∉ box 2 m ∧
      ∃ w : (openSubgraph 2 (removeSite x ω)).Walk a z, ∀ v ∈ w.support, v ∉ T) :=
  bc32_escapingClause_nonvacuous

-- The ray configuration's edge `1 – 2` is open, and the ray leaves the radius-3 box.
example : (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj (arc_p 1) (arc_p (1 + 1))
    ∧ arc_p (1 + ((3 : ℕ) : ℤ)) ∉ box 2 3 :=
  ⟨bc32_pos_edge_open 1 le_rfl, bc32_arc_outside 3⟩

/-- Escaping down-arm data for the all-closed configuration. -/
theorem closed_esc (n : ℕ) : bc32_EscapingDownArmData closed2 n fun _ => toLex (0, 0) :=
  ⟨id, fun x _ h => absurd h (closed_not_trif x), fun x _ h => absurd h (closed_not_trif x)⟩

-- The count bound from escaping data.
example : Tcount 2 closed2 2 ≤ boxSV_boundaryCard 2 2 :=
  bc32_Tcount_le_boundary_of_escapingDownArmData closed2 2 (by norm_num) _
    (fun x _ h => absurd h (closed_not_trif x)) (closed_esc 2)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.EscapingArmForest
