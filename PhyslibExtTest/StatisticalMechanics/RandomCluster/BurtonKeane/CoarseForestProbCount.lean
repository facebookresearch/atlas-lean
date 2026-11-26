/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount`

In the plane:
* `bpe_CoarseForestNoBnd` is satisfiable: the two-vertex path is such a forest for the
  all-closed configuration with leaf bound `2`;
* `bpe_coarseTcount_le_leafCard` then bounds its coarse count by `2`;
* `bpe_status` and `bpe_top_null_of_probForest` applied to Bernoulli(1/2) bond percolation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The all-closed configuration has no coarse trifurcation. -/
theorem closed_not_coarseTrif (L : ℕ) (y : Site 2) : ¬ bc61_IsCoarseTrifurcation closed2 L y := by
  rintro ⟨_, _, _, ⟨_, _, hb⟩, -⟩
  exact absurd hb.2 (by simp [closed2])

/-- The Bernoulli(1/2) bond percolation measure on the planar lattice. -/
noncomputable abbrev bern2 : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)

/-- `bern2` has finite energy. -/
theorem bern2_fe : HasFiniteEnergyMerge bern2 :=
  bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)

/-- `bern2` is translation invariant. -/
theorem bern2_inv : IsTranslationInvariant (G := Multiplicative (Site 2)) bern2 :=
  (bkc_bernoulli_isErgodic (d := 2) (by norm_num) _ _).isTranslationInvariant

/-- The two-vertex path is a coarse forest without boundary for the all-closed configuration. -/
theorem closed_noBnd (L R : ℕ) : bpe_CoarseForestNoBnd closed2 L R 2 := by
  classical
  refine ⟨Fin 2, inferInstance, ⟨0⟩, inferInstance, Flc2Witness.pathG, inferInstance,
    fun _ => 0, Flc2Witness.pathG_isTree.isAcyclic, fun v => by rw [Flc2Witness.pathG_deg v],
    fun y _ h => absurd h (closed_not_coarseTrif L y),
    fun y _ h => absurd h (closed_not_coarseTrif L y), ?_⟩
  exact (Finset.card_filter_le _ _).trans (by simp)

-- The coarse count of the all-closed configuration is at most `2`.
example (L R : ℕ) : bc61_coarseTcount closed2 L R ≤ 2 :=
  bpe_coarseTcount_le_leafCard _ L R 2 (closed_noBnd L R)

-- The leaf-count clause of `bpe_status` for Bernoulli(1/2).
example (L R : ℕ) : bc61_coarseTcount closed2 L R ≤ 2 :=
  (bpe_status bern2 bern2_inv (by norm_num) L (fun _ => 0)).2.1 closed2 R 2 (closed_noBnd L R)

-- The probabilistic forest route applied to Bernoulli(1/2).
example (L : ℕ) (bdry : ℕ → ℕ) (leafBd : ConfigSpace (Sym2 (Site 2)) → ℕ → ℕ)
    (hforest : ∀ ω R, bpe_CoarseForestNoBnd ω L R (leafBd ω R))
    (hExpLeaf : ∀ R, ∫⁻ ω, (leafBd ω R : ENNReal) ∂bern2 ≤ (bdry R : ENNReal))
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence bern2 L) :
    bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bpe_top_null_of_probForest bern2 bern2_inv (by norm_num) L bdry leafBd hforest hExpLeaf hdens
    hexist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount
