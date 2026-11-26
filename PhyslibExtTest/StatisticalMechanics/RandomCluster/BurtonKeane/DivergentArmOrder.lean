/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder`

In the plane:
* refutations: `fsp_not_forall_divergentArmOrder` and `fsp_not_forall_treeSelector`;
* `fsp_RootedArmOrder` is satisfiable: `fsp_rootedArmOrder_of_noTrif` for the all-closed
  configuration, and `fsp_Tcount_le_boundary_of_rootedArmOrder` and
  `fsp_treeSelector_of_rootedArmOrder` apply;
* `fsp_inSomeArm_of_connected` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder

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

-- Divergent arm orders do not exist for every configuration and box.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n :=
  fsp_not_forall_divergentArmOrder (by norm_num)

-- Nor do tree selectors.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
    daep2_SingleCutBranchSeparation ω n :=
  fsp_not_forall_treeSelector (by norm_num)

/-- The all-closed configuration has a rooted arm order. -/
theorem closed_order (n : ℕ) : fsp_RootedArmOrder closed2 n :=
  fsp_rootedArmOrder_of_noTrif closed2 n fun x _ => closed_not_trif x

-- The count bound and the tree selector for the all-closed configuration.
example : Tcount 2 closed2 2 ≤ boxSV_boundaryCard 2 2 ∧
    daep2_SingleCutBranchSeparation closed2 2 :=
  ⟨fsp_Tcount_le_boundary_of_rootedArmOrder closed2 2 (by norm_num) (closed_order 2),
    fsp_treeSelector_of_rootedArmOrder closed2 2 (closed_order 2)⟩

-- A site connected to `x` lies in an arm of `x`.
example (ω : ConfigSpace (Sym2 (Site 2))) (x v : Site 2) (h : Connected 2 ω x v) (hne : x ≠ v) :
    ∃ a, (openSubgraph 2 ω).Adj x a ∧ Connected 2 (removeSite x ω) a v :=
  fsp_inSomeArm_of_connected ω h hne

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
