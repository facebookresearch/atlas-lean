/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.FiniteMoments

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.FiniteMoments`

* `hammingToSet_le_card`: the distance to any event on `Fin 2` is at most `2`;
* `expect_const` at `p = 1/2` on `Fin 2`;
* `hammingMoment_le_one` on the one-edge space `Fin 1` (every moment is at most `1`);
* `exp_hammingMoment_le` at `t = 1` on `Fin 3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.FiniteMoments

open _root_.StatMech _root_.StatMech.BeffaraDC

-- The distance to an event is at most the number of edges.
example (A : Set (ConfigSpace (Fin 2))) (ω : ConfigSpace (Fin 2)) : hammingToSet A ω ≤ 2 := by
  simpa using hammingToSet_le_card A ω

-- The expectation of a constant is the constant.
example : expect (1 / 2) (fun _ : ConfigSpace (Fin 2) => (3 : ℝ)) = 3 := expect_const _ _

-- On a single edge every Hamming moment is at most `1`.
example (A : Set (ConfigSpace (Fin 1))) (d : ℕ) : hammingMoment (1 / 2) A d ≤ 1 :=
  hammingMoment_le_one (by norm_num) (by norm_num) A (by simp) d

-- The exponential moment at `t = 1` on three edges is at most `e ^ 3`.
example (A : Set (ConfigSpace (Fin 3))) : expHammingMoment (1 / 3) A 1 ≤ Real.exp 3 := by
  simpa using exp_hammingMoment_le (p := 1 / 3) (by norm_num) (by norm_num) A zero_le_one

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.FiniteMoments
