/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseArmForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseArmForestCount`

In the plane `Site 2`, with the all-closed configuration and the upper-lines configuration:
* the all-closed configuration has no coarse trifurcation, so `bc63_coarseForestLeafCount_of_noTrif`
  gives a coarse arm embedding (`bc63_CoarseArmEmbedding` is satisfiable) and
  `bc63_coarseTcount_le_boundary_of_armEmbedding` bounds its coarse count;
* `bc63_upperLines_arm_reaches_boundary` applies at `L = 3`, `R = 4`, height `1`;
* `bc63_status` gives the upper-lines configuration as a coarse precursor at `L = 3`;
* `bc63_coarseTrifExistence_of_precursor_pos` applies to a Bernoulli product measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseArmForestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The all-closed configuration has no coarse trifurcation. -/
theorem closed_not_coarseTrif (L : ℕ) (y : Site 2) :
    ¬ bc61_IsCoarseTrifurcation closed2 L y := by
  rintro ⟨_, _, _, ⟨_, _, hb⟩, -⟩
  exact absurd hb.2 (by simp [closed2])

/-- Two distinct sites of the boundary of the radius-one box. -/
theorem bdry_one : (![1, 0] : Site 2) ∈ vertexBoundary 2 1 ∧
    (![0, 1] : Site 2) ∈ vertexBoundary 2 1 ∧ (![1, 0] : Site 2) ≠ ![0, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [vertexBoundary, box, Fin.forall_fin_two]
  · simp [vertexBoundary, box, Fin.forall_fin_two]
  · intro h; simpa using congrFun h 0

/-- The all-closed configuration has a coarse arm embedding. -/
theorem closed_armEmbedding (L : ℕ) : bc63_CoarseArmEmbedding closed2 L 1 :=
  bc63_coarseForestLeafCount_of_noTrif _ L 1 bdry_one.1 bdry_one.2.1 bdry_one.2.2
    (fun y _ => closed_not_coarseTrif L y)

-- The coarse count of the all-closed configuration is bounded by the boundary size.
example (L : ℕ) : bc61_coarseTcount closed2 L 1 ≤ boxSV_boundaryCard 2 1 :=
  bc63_coarseTcount_le_boundary_of_armEmbedding _ L 1 (closed_armEmbedding L)

-- The right arm at height `1` of the upper lines reaches the boundary of the radius-4 box.
example : ∃ z ∈ vertexBoundary 2 4,
    Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines)
      (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) z :=
  bc63_upperLines_arm_reaches_boundary (L := 3) (by norm_num) le_rfl
    (by simp [box, Fin.forall_fin_two, bc57_pt])

-- The upper lines are a coarse precursor at `L = 3`.
example : bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 3
    (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) (bc57_pt (((3 : ℕ) : ℤ) + 1) 2)
    (bc57_pt (((3 : ℕ) : ℤ) + 1) 3) (bc57_pt ((3 : ℕ) : ℤ) 1) (bc57_pt ((3 : ℕ) : ℤ) 2)
    (bc57_pt ((3 : ℕ) : ℤ) 3) :=
  (bc63_status (d := 2)).2.2.2 le_rfl

-- A positive-probability precursor for Bernoulli(1/2) gives the coarse trifurcation step.
example (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2)
    (hpre : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2)
      (by norm_num)) L :=
  bc63_coarseTrifExistence_of_precursor_pos _
    (bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)) L _ _ _ _ _ _ hpre

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseArmForestCount
