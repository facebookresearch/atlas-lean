/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms`

* `bc24_coarseTrif_nonvacuous`: `IsCoarseTrifurcation 2 0` has a witness, and
  `bc24_coarseTrif_armClusters_distinct_after_boxRemoval` and `bc24_box_hub_routes_armEnds`
  apply to it;
* `bc24_box_zero` and `bc24_removeSites_box_zero` in the plane.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Scale-zero coarse trifurcations exist in the plane.
example : ∃ ω : ConfigSpace (Sym2 (Site 2)), IsCoarseTrifurcation 2 0 ω :=
  bc24_coarseTrif_nonvacuous

-- A coarse trifurcation has three distinct infinite arm clusters after removing the box.
example : ∃ ω : ConfigSpace (Sym2 (Site 2)), ∃ a₁ a₂ _a₃ : Site 2,
    (cluster 2 (removeSites (boxFinsetBK 2 0) ω) a₁).Infinite ∧
    cluster 2 (removeSites (boxFinsetBK 2 0) ω) a₁
      ≠ cluster 2 (removeSites (boxFinsetBK 2 0) ω) a₂ := by
  obtain ⟨ω, h⟩ := bc24_coarseTrif_nonvacuous
  obtain ⟨a₁, a₂, a₃, h₁, -, -, h₁₂, -, -⟩ :=
    bc24_coarseTrif_armClusters_distinct_after_boxRemoval h
  exact ⟨ω, a₁, a₂, a₃, h₁, h₁₂⟩

-- Opening the box connects the arm ends.
example : ∃ ω : ConfigSpace (Sym2 (Site 2)), ∃ a₁ a₂ : Site 2,
    a₁ ≠ a₂ ∧ Connected 2 (forceOpenFinset (boxEdges 2 0) ω) a₁ a₂ := by
  obtain ⟨ω, h⟩ := bc24_coarseTrif_nonvacuous
  obtain ⟨a₁, a₂, _, ⟨h₁₂, -⟩, hc, -⟩ := bc24_box_hub_routes_armEnds h
  exact ⟨ω, a₁, a₂, h₁₂, hc⟩

/-- The all-open configuration of the planar lattice. -/
def open2 : ConfigSpace (Sym2 (Site 2)) := fun _ => true

-- The radius-zero box is the origin, and removing it removes the origin.
example : box 2 0 = {(0 : Site 2)} ∧
    removeSites (boxFinsetBK 2 0) open2 = removeSite (0 : Site 2) open2 :=
  ⟨bc24_box_zero 2, bc24_removeSites_box_zero _⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms
