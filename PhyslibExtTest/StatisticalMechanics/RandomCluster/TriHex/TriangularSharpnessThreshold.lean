/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpnessThreshold

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpnessThreshold`

* `triangularSharpConstant_le_one` at `β₀ = 1`, and `triangularOuterInnerTheta_le_one` at
  `n = 3`, `q = 1`, `β = 1`;
* `triangularThresholdTheta_of_pos`: the extension agrees with the normalized `θ` at `β = 1`;
* `triangularThreshold_decay_hypotheses_false_of_thresholdSet_empty`: with an empty threshold set
  the decay hypotheses are contradictory (the documented vacuity);
* `triangularOuterInner_subcritical_decay_of_threshold`, conditional on `1 < β₁`, at `q = 1`,
  `β = β₀ = 1`, `δ = 1 / 4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpnessThreshold

open _root_.StatMech.OSSS _root_.StatMech.FK.PeriodicPlanar

-- Bounds at concrete parameters.
example : triangularSharpConstant 1 ≤ 1 :=
  triangularSharpConstant_le_one 1 zero_le_one

example : triangularOuterInnerTheta 1 1 3 ≤ 1 :=
  triangularOuterInnerTheta_le_one 3 1 1 le_rfl one_pos

-- For positive `β` the threshold extension is the normalized crossing probability.
example (n : ℕ) : triangularThresholdTheta 1 1 n 1 = triangularNormalizedTheta 1 1 n 1 :=
  triangularThresholdTheta_of_pos n 1 1 1 one_pos

-- With an empty threshold set the decay theorem's hypotheses cannot hold.
example (hempty : BetaThresholdBound.thresholdSet
      (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta 1 1) n b) = ∅) :
    ¬ (0 < (1 : ℝ) - 2 * (1 / 4) ∧ (1 : ℝ) < BetaThresholdBound.beta1
      (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta 1 1) n b)) :=
  triangularThreshold_decay_hypotheses_false_of_thresholdSet_empty 1 1 (1 / 4) 1
    (by norm_num) hempty

-- Exponential decay below the threshold, assuming `1 < β₁`.
example (hlt : (1 : ℝ) < BetaThresholdBound.beta1
      (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta 1 1) n b)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      triangularOuterInnerTheta 1 (1 - 2 * (1 / 4)) n ≤ Real.exp (-(((n : ℝ) / Q) * (1 / 4))) :=
  triangularOuterInner_subcritical_decay_of_threshold 1 (1 / 4) 1 1 le_rfl le_rfl
    (by norm_num) (by norm_num) hlt

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpnessThreshold
