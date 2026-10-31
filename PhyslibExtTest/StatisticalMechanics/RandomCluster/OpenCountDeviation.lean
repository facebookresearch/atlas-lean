/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.OpenCountDeviation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.OpenCountDeviation`

On the one-edge graph `⊤` on `Fin 2` (`|E| = 1`) at `p = 1/2`, `q = 2`:
* `fkMeanOpenCount_le` and `fkMeanOpenCount_ge`: the mean open count lies in
  `[1/3, 1/2]`;
* `den_openCount_upper_deviation` with `ε = 1/4`;
* `den_openCount_lower_deviation` with `ε = 1/4 ≤ 1/3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.OpenCountDeviation

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The test graph has exactly one edge. -/
theorem card_edges : G2.edgeFinset.card = 1 := by
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rfl

/-- The edge count is positive. -/
theorem card_pos : 0 < (G2.edgeFinset.card : ℝ) := by rw [card_edges]; norm_num

-- The mean open count is between `p / (p + q(1 - p)) |E|` and `p |E|`.
example : 1 / 2 / (1 / 2 + 2 * (1 - 1 / 2)) * (G2.edgeFinset.card : ℝ) ≤
      fkMeanOpenCount G2 (1 / 2) 2 ∧
    fkMeanOpenCount G2 (1 / 2) 2 ≤ 1 / 2 * (G2.edgeFinset.card : ℝ) :=
  ⟨fkMeanOpenCount_ge G2 (by norm_num) (by norm_num) one_le_two,
   fkMeanOpenCount_le G2 (by norm_num) (by norm_num) one_le_two⟩

-- Upper deviation.
example : (1 / 4 : ℝ) ≤
    fkOpenCountLeProb G2 (1 / 2) 2 ((1 / 2 + 1 / 4) * (G2.edgeFinset.card : ℝ)) :=
  den_openCount_upper_deviation G2 (by norm_num) (by norm_num) one_le_two (by norm_num)
    (by norm_num) card_pos

-- Lower deviation.
example : (1 / 4 : ℝ) ≤ fkOpenCountGeProb G2 (1 / 2) 2
    ((1 / 2 / (1 / 2 + 2 * (1 - 1 / 2)) - 1 / 4) * (G2.edgeFinset.card : ℝ)) :=
  den_openCount_lower_deviation G2 (by norm_num) (by norm_num) one_le_two (by norm_num)
    (by norm_num) card_pos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.OpenCountDeviation
