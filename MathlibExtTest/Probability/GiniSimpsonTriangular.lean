/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.GiniSimpsonTriangular
import Mathlib.Tactic.NormNum

open MathlibExt.Probability.DiversityStatisticsWanted

-- At the empty sample the triangular lower bound meets the upper bound.
example : giniSimpsonCount 0 = 1 := by
  have hlo := giniSimpsonCount_ge_triangular 0 0 0 rfl le_rfl
  have hhi := giniSimpsonCount_le 0
  norm_num at hlo hhi
  exact_mod_cast le_antisymm hhi hlo

-- The last remainder before the next triangular number, and the triangular number itself.
example : 18 ≤ giniSimpsonCount 9 := by
  have h := giniSimpsonCount_ge_triangular 9 3 3 rfl le_rfl
  norm_num at h
  exact_mod_cast h

example : 21 ≤ giniSimpsonCount 10 := by
  have h := giniSimpsonCount_ge_triangular 10 4 0 rfl (Nat.zero_le _)
  norm_num at h
  exact_mod_cast h
