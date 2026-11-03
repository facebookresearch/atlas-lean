/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerGapThreeArms

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerGapThreeArms`

* `bc101_gnTrif_three_incident_arms` on the coarse trifurcation of `bc60_upperLines` at the
  origin for `L = 3` (instance).
* The second conjunct of `bc101_status`: the box condition `bc56_BoxClusterReachesNbr 2 3` fails
  (refutation).
* The third conjunct as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerGapThreeArms

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Three separated incident arms of the upper-lines coarse trifurcation.
example : ∃ a₁ a₂ a₃ : Site 2,
    (bc67_GnIncident bc60_upperLines 3 0 a₁ ∧ bc67_GnIncident bc60_upperLines 3 0 a₂ ∧
      bc67_GnIncident bc60_upperLines 3 0 a₃) ∧
    ((cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁).Infinite ∧
     (cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂).Infinite ∧
     (cluster 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₃).Infinite) ∧
    (¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₂ ∧
     ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₃ ∧
     ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₂ a₃) :=
  bc101_gnTrif_three_incident_arms _ 3 0 (bc61_wholeBox_severs_upperLines le_rfl)

-- The box cluster condition fails.
example : ¬ bc56_BoxClusterReachesNbr 2 3 :=
  ((bc101_status (d := 2)).2.1 (L := 3) le_rfl).2

-- A boundary injection bounds the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (z₀ z₁ : Site 2)
    (h₀ : z₀ ∈ vertexBoundary 2 R) (h₁ : z₁ ∈ vertexBoundary 2 R) (hne : z₀ ≠ z₁)
    (h : bc64_CoarseBoundaryInjection ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  (bc101_status (d := 2)).2.2 ω L R z₀ z₁ h₀ h₁ hne h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerGapThreeArms
