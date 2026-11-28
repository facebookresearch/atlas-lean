/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Inequality.GiniReplication
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open MathlibExt.Economics.Inequality

-- Compute both population coefficients directly, independently of replication invariance.
example : gini ![0, 1] = 1 / 2 ∧ gini ![0, 0, 1, 1] = 1 / 2 := by
  constructor <;> norm_num [gini, Fin.sum_univ_succ]

-- The literal four-entry example also computes the correction on the product population.
example : biasCorrectedGini (fun p : Fin 2 × Fin 2 => ![0, 1] p.1) (by decide) =
    biasCorrectedGini ![0, 0, 1, 1] (by decide) := by
  rw [biasCorrectedGini_duplication_example.2]
  norm_num [biasCorrectedGini, Fintype.sum_prod_type, Fin.sum_univ_succ, Fintype.card_prod]

-- Three copies and a change of units, with tied incomes and several distinct nonzero gaps.
example : gini (fun p : Fin 4 × Fin 3 => ((5 : ℝ) • ![1, 1, 2, 5]) p.1) = 13 / 36 := by
  rw [gini_replicate _ (by decide), gini_smul _ (by norm_num)]
  norm_num [gini, Fin.sum_univ_succ]

-- A single person has a well-defined population Gini but admits no bias correction.
example (v : ℝ) : gini (fun _ : Fin 1 => v) = 0 := by simp [gini]

-- A failure of replication invariance need not be a change for every distribution.
example (v : ℝ) : biasCorrectedGini (fun _ : Fin 2 × Fin 3 => v) (by decide) =
    biasCorrectedGini (fun _ : Fin 2 => v) (by decide) := by simp [biasCorrectedGini]

-- Zero total income gives the totalized value, even when not all differences vanish.
example : biasCorrectedGini ![-1, 1] (by decide) = 0 := by
  norm_num [biasCorrectedGini, Fin.sum_univ_succ]
