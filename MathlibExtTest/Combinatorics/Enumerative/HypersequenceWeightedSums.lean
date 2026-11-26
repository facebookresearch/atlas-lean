/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.HypersequenceWeightedSums

open Finset MetaMathlibExt

-- At degree zero the lower-degree sum is empty, even when the index starts at zero.
example (a : ℕ → ℂ) (r n : ℕ) :
    ∑ k ∈ range (n + 1), hypersequence a r k = hypersequence a (r + 1) n := by
  simpa using sum_pow_mul_hypersequence_recurrence a 0 r n

-- A quadratic weight at positive generation involves both lower-degree sums.
example :
    ∑ k ∈ range 3, (k : ℂ) ^ 2 * hypersequence (fun _ => (1 : ℂ)) 1 k = 14 := by
  rw [sum_pow_mul_hypersequence_recurrence (fun _ => 1) 2 1 2]
  norm_num [hypersequence, sum_range_succ, Nat.choose]
