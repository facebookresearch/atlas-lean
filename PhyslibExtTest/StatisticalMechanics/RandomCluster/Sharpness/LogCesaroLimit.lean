/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LogCesaroLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LogCesaroLimit`

* `harmonicReal` at `n = 2` via `harmonicReal_eq`;
* `logCesaro_tendsto` for a constant sequence;
* `logRatio_partialSum_tendsto_one` for the constant sequence `1`;
* `meanField_lower_at_threshold` on the explicit function `f x = x` with `β₁ = 0`, `β = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LogCesaroLimit

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.LogCesaroLimit Filter

-- `H₂ = 1 + 1/2`.
example : harmonicReal 2 = 3 / 2 := by
  rw [harmonicReal_eq]
  norm_num [harmonic, Finset.sum_range_succ]

-- Logarithmic Cesàro averages of a constant sequence converge to the constant.
example : Tendsto (fun n => logCesaro (fun _ => (3 : ℝ)) n) atTop (nhds 3) :=
  logCesaro_tendsto tendsto_const_nhds

-- `log(∑_{k<n} 1) / log n → 1`.
example :
    Tendsto (BetaThresholdBound.logRatio (fun n => ∑ _k ∈ Finset.range n, (1 : ℝ)))
      atTop (nhds 1) :=
  logRatio_partialSum_tendsto_one tendsto_const_nhds one_pos

-- The mean-field lower bound for `f x = x` above the threshold `β₁ = 0`, at `β = 1`.
example : (1 : ℝ) - 0 ≤ (fun x : ℝ => x) 1 :=
  meanField_lower_at_threshold (f := fun x => x) one_pos (fun _ h _ => h.le)
    (fun _ _ _ => le_refl _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LogCesaroLimit
