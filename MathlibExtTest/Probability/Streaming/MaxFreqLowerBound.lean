/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Streaming.MaxFreqLowerBound
import Mathlib.Tactic.NormNum

open MathlibExt.Probability.Streaming

-- Even on a one-symbol alphabet, zero bits cannot achieve the required accuracy.
example (R : Type) [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin 1) R 0) :
    ¬ ∀ l : List (Fin 1), l ≠ [] → l.length ≤ 2 →
      A.failProb (fun l y => |y - maxFreq l| < (maxFreq l : ℝ) / 3) l < 1 / 4 := by
  intro h
  obtain ⟨c, hc, bound⟩ := space_lower_bound_maxFreq (1 / 4) (by norm_num) (by norm_num)
  have := bound 1 0 R A (by simpa using h)
  exact hc.not_ge (by simpa using this)

-- At the shared endpoint, neither multiplicity counts as a successful approximation.
example :
    ∀ l ∈ [([0] : List (Fin 1)), [0, 0]],
      ¬ |(4 : ℝ) / 3 - maxFreq l| < (maxFreq l : ℝ) / 3 := by
  have hone : maxFreq ([0] : List (Fin 1)) = 1 := by decide
  have htwo : maxFreq ([0, 0] : List (Fin 1)) = 2 := by decide
  simp [hone, htwo]
  norm_num
