/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount`

In the plane, with the all-closed configuration:
* `dfc_canonTcount_le_boundary_succ` (unconditional) at `n = 2`;
* `dfc_Tcount_le_boundary_succ_of_canonical`, whose canonicity hypothesis holds vacuously (no
  trifurcations);
* `dfc_canonArmForestReachingSucc` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount

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

-- The canonical count is bounded by the next boundary.
example : ctc2_canonTcount 2 closed2 2 ≤ boxSV_boundaryCard 2 (2 + 1) :=
  dfc_canonTcount_le_boundary_succ closed2 2 (by norm_num)

-- The all-closed configuration satisfies the canonical route's hypothesis vacuously.
example (n : ℕ) (hn : 1 ≤ n) : Tcount 2 closed2 n ≤ boxSV_boundaryCard 2 (n + 1) :=
  dfc_Tcount_le_boundary_succ_of_canonical closed2 n hn fun x _ h => absurd h (closed_not_trif x)

-- A canonical trifurcation in the box gives a reaching arm forest.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (hn : 1 ≤ n)
    (hex : ∃ x, x ∈ box 2 n ∧ IsCanonicalTrifurcation 2 ω x) :
    dfc_CanonArmForestReachingSucc ω n :=
  dfc_canonArmForestReachingSucc ω n hn hex

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount
