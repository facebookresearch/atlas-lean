/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ChaoLowerBound
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open WantedExt.Biology.StatisticalGenetics.ChaoLowerBoundWanted

-- Two classes with different positive rates give a positive expected doubleton count.
example :
    (2 - expectedFreq (fun i : Fin 2 => (i.val : ℝ) + 1) 0) +
      expectedFreq (fun i : Fin 2 => (i.val : ℝ) + 1) 1 ^ 2 /
        (2 * expectedFreq (fun i : Fin 2 => (i.val : ℝ) + 1) 2) ≤ (2 : ℝ) := by
  apply chao_lower_bound
  · intro i
    positivity
  · norm_num [expectedFreq, Fin.sum_univ_two, Nat.factorial_succ]
    positivity

-- The empty family has no positive expected doubleton count.
example (rate : Fin 0 → ℝ) : expectedFreq rate 2 = 0 := by
  simp [expectedFreq]
