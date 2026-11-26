/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding`

* the explicit star `bc64_starG`: centre degree `3`, and `bc64_starForest` is acyclic with leaf
  degree `1` (here over `Unit`);
* `bc64_CoarseBoundaryInjection` is satisfiable: the all-closed planar configuration has one
  (no coarse trifurcations), so `bc64_coarseTcount_le_boundary_of_boundaryInjection` applies;
* the upper-lines facts `bc64_line1_connected` and `bc64_disjointBoxes_sublattice` at explicit
  values.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The all-closed configuration has no coarse trifurcation. -/
theorem closed_not_coarseTrif (L : ℕ) (y : Site 2) : ¬ bc61_IsCoarseTrifurcation closed2 L y := by
  rintro ⟨_, _, _, ⟨_, _, hb⟩, -⟩
  exact absurd hb.2 (by simp [closed2])

/-- Two distinct sites of the boundary of the radius-one box. -/
theorem bdry_one : (![1, 0] : Site 2) ∈ vertexBoundary 2 1 ∧
    (![0, 1] : Site 2) ∈ vertexBoundary 2 1 ∧ (![1, 0] : Site 2) ≠ ![0, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [vertexBoundary, box, Fin.forall_fin_two]
  · simp [vertexBoundary, box, Fin.forall_fin_two]
  · intro h; simpa using congrFun h 0

-- The star has a degree-three centre.
example : bc64_starG.degree 0 = 3 :=
  bc64_starG_centre_deg

-- The star forest over `Unit` is acyclic, and its leaves have degree one.
example : (bc64_starForest Unit).IsAcyclic ∧ (bc64_starForest Unit).degree ((), 1) = 1 :=
  ⟨bc64_starForest_acyclic Unit, (bc64_starForest_deg1_iff () 1).mpr (by decide)⟩

/-- The all-closed configuration has a coarse boundary injection (its trifurcation set is empty). -/
theorem closed_boundaryInjection (L R : ℕ) : bc64_CoarseBoundaryInjection closed2 L R :=
  ⟨fun _ => 0,
    fun p _ => absurd (bc61_mem_coarseTrifFinset.mp p.1.2).2 (closed_not_coarseTrif L _),
    fun p _ _ _ _ => absurd (bc61_mem_coarseTrifFinset.mp p.1.2).2 (closed_not_coarseTrif L _)⟩

-- The coarse count bound from the boundary injection.
example (L : ℕ) : bc61_coarseTcount closed2 L 1 ≤ boxSV_boundaryCard 2 1 :=
  bc64_coarseTcount_le_boundary_of_boundaryInjection _ L 1 bdry_one.1 bdry_one.2.1 bdry_one.2.2
    (closed_boundaryInjection L 1)

-- The height-one line of the upper lines is connected.
example : Connected 2 bc60_upperLines (bc57_pt (-2) 1) (bc57_pt 5 1) :=
  bc64_line1_connected _ _

-- Sublattice boxes at different multiples are disjoint.
example : Disjoint (bc61_boxAround 2 3 (bc57_pt ((2 * ((3 : ℕ) : ℤ) + 1) * 0) 0))
    (bc61_boxAround 2 3 (bc57_pt ((2 * ((3 : ℕ) : ℤ) + 1) * 1) 0)) :=
  bc64_disjointBoxes_sublattice 3 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding
