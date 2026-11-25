/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumber
import Mathlib.Tactic.NormNum

open Filter Topology MeasureTheory unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumberWanted

namespace MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphChromaticNumber

private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

-- At edge probability one half the normalizing logarithm is base two.
example {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => half)).real
      {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) / (n / (2 * Real.logb 2 n)) - 1| ≤ ε})
      atTop (𝓝 1) := by
  have hbase : 1 / (1 - (half : ℝ)) = 2 := by norm_num [half]
  simpa only [hbase] using tendsto_measureReal_chromaticNumber_near half
    (by norm_num [half]) (by norm_num [half]) hε

end MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphChromaticNumber
