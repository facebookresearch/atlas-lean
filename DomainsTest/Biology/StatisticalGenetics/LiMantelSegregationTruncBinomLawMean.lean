/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.StatisticalGenetics.LiMantelSegregationTruncBinomLawMean
import Mathlib.Tactic.NormNum

/-!
# Tests for the zero-truncated binomial law

The theorem gives normalization and mean `4/3` for size two with probability `1/2`,
and mean one for size one. The definition vanishes outside its support.

Sources: C. C. Li and N. Mantel, "A simple method of estimating the segregation ratio under
complete ascertainment", Am. J. Hum. Genet. 20 (1968) 61–81; R. A. Fisher, "The effect of
methods of ascertainment upon the estimation of frequencies", Ann. Eugen. 6 (1934) 13–25.
-/

open Finset WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted

namespace DomainsTest.Biology.StatisticalGenetics.LiMantelSegregationTruncBinomLawMean

example : ∑ k ∈ range 3, truncBinom 2 (1 / 2) k = 1 :=
  (truncBinom_law_mean 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)).2.1

example : ∑ k ∈ range 3, (k : ℝ) * truncBinom 2 (1 / 2) k = 4 / 3 := by
  convert (truncBinom_law_mean 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)).2.2 using 1
  norm_num

example (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∑ k ∈ range 2, (k : ℝ) * truncBinom 1 p k = 1 := by
  simpa [ne_of_gt hp₀] using (truncBinom_law_mean 1 (by decide) p hp₀ hp₁).2.2

example (s : ℕ) (p : ℝ) : truncBinom s p 0 = 0 := by
  simp [truncBinom]

example (s : ℕ) (p : ℝ) : truncBinom s p (s + 1) = 0 := by
  simp [truncBinom]

end DomainsTest.Biology.StatisticalGenetics.LiMantelSegregationTruncBinomLawMean
