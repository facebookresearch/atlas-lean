/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexHStar

/-! # Regression tests for the stabilized $h^*$-formula -/

open MetaMathlibExt

-- For `q = [3, 10, 15]` the first stabilization has one extra weight, equal to `1`.
example : hStarFormula [1, 3, 10, 15] = hStarFormula [3, 10, 15] + Polynomial.X ^ 4 := by
  have hrs : reflexiveStabilization [3, 10, 15] = [1, 3, 10, 15] := by
    rw [← almostIDPWeights_eq_reflexiveStabilization 1 le_rfl]
    decide
  have hrsn : reflexiveStabilizationNumber [3, 10, 15] = 1 := by
    have h := congrArg List.length hrs
    simp only [reflexiveStabilization, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] at h
    omega
  have hell : listEll (reflexiveStabilization [3, 10, 15]) = 1 := by
    rw [hrs]
    decide
  simpa only [hrs, List.length_cons, List.length_nil] using
    stabilization_hStar_add_monomial [3, 10, 15] hrsn hell

-- The old endpoint keeps its exponent; the new endpoint has exponent `4`.
example : weightStatistic [3, 10, 15] 28 = weightStatistic [1, 3, 10, 15] 28 ∧
    weightStatistic [1, 3, 10, 15] 29 = 4 := by
  decide
