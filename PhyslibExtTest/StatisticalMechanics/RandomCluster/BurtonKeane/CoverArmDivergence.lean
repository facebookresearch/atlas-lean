/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence`

* the explicit path configuration `rfp_ωpath` on `Site 1`: `rfp_consistency_crossed` and
  `rfp_armGeometry_consistent`;
* `rfp_RootedArmDivergence` is satisfiable: `rfp_rootedArmDivergence_of_noTrif` for the all-closed
  planar configuration;
* refutation: `rfp_not_forall_coverArmDivergence` in the plane.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence

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

-- In the path configuration, removing the middle site disconnects the ends.
example : ¬ Connected 1 (removeSite rfp_p1 rfp_ωpath) rfp_p2 rfp_p0 :=
  rfp_consistency_crossed

-- The arm geometry is consistent.
example : ∃ (ω : ConfigSpace (Sym2 (Site 1))) (x₀ z w : Site 1),
    Connected 1 (removeSite x₀ ω) w z ∧ ¬ Connected 1 (removeSite z ω) w x₀ :=
  rfp_armGeometry_consistent

-- With no trifurcations, rooted arm divergence holds.
example (n : ℕ) : rfp_RootedArmDivergence closed2 n :=
  rfp_rootedArmDivergence_of_noTrif closed2 n fun x _ => closed_not_trif x

-- Cover plus divergence cannot hold for every configuration and box.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
    fcc_ThreeArmCover ω n ∧ rfp_RootedArmDivergence ω n :=
  rfp_not_forall_coverArmDivergence (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence
