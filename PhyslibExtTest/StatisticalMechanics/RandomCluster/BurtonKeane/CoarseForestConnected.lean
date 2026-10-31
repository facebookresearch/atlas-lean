/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected`

In the plane:
* the explicit caterpillars: `bc65_caterpillar2_savings` and `bc65_cat3G_leafCount`;
* `bc65_ConnectedCoarseForest` is satisfiable: the all-closed configuration has one (via
  `bc65_connectedCoarseForest_iff_armEmbedding`), and
  `bc65_coarseTcount_le_boundary_of_connectedForest` bounds its coarse count;
* `bc65_infiniteClusters_top_null_of_connectedForest_route` applied to Bernoulli(1/2).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected

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

/-- The Bernoulli(1/2) bond percolation measure on the planar lattice. -/
noncomputable abbrev bern2 : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)

/-- `bern2` has finite energy. -/
theorem bern2_fe : HasFiniteEnergyMerge bern2 :=
  bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)

/-- `bern2` is translation invariant. -/
theorem bern2_inv : IsTranslationInvariant (G := Multiplicative (Site 2)) bern2 :=
  (bkc_bernoulli_isErgodic (d := 2) (by norm_num) _ _).isTranslationInvariant

-- The two-branch caterpillar has fewer than three leaves per branch vertex.
example : (Finset.univ.filter (fun v => bc65_cat2G.degree v = 1)).card
    < 3 * (Finset.univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card :=
  bc65_caterpillar2_savings

-- The three-branch caterpillar has `3` branch vertices and `5` leaves.
example : (Finset.univ.filter (fun v => 3 ≤ bc65_cat3G.degree v)).card = 3 ∧
    (Finset.univ.filter (fun v => bc65_cat3G.degree v = 1)).card = 5 :=
  bc65_cat3G_leafCount

/-- The all-closed configuration has a connected coarse forest. -/
theorem closed_connectedForest (L : ℕ) : bc65_ConnectedCoarseForest closed2 L 1 :=
  (bc65_connectedCoarseForest_iff_armEmbedding _ _ _).mpr
    (bc63_coarseForestLeafCount_of_noTrif _ L 1 bdry_one.1 bdry_one.2.1 bdry_one.2.2
      (fun y _ => closed_not_coarseTrif L y))

-- The coarse count bound for the all-closed configuration.
example (L : ℕ) : bc61_coarseTcount closed2 L 1 ≤ boxSV_boundaryCard 2 1 :=
  bc65_coarseTcount_le_boundary_of_connectedForest _ L 1 (closed_connectedForest L)

-- The conditional route applied to Bernoulli(1/2).
example (L : ℕ)
    (hconn : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
    (hroute : 0 < bern2 {ω | numInfiniteClusters 2 ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2, 0 < bern2 (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc65_infiniteClusters_top_null_of_connectedForest_route bern2 (by norm_num) bern2_inv bern2_fe
    L hconn hroute

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected
