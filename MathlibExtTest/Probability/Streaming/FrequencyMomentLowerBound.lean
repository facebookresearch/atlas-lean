/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Streaming.FrequencyMomentLowerBound
import Mathlib.Tactic.NormNum

namespace MathlibExt.Probability.Streaming

-- At the smallest allowed moment and alphabet, the empty stream and singleton require a bit.
example (R : Type) [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin 1) R 0) :
    ¬ ∀ l : List (Fin 1), l.length ≤ 1 →
      A.failProb (fun l z => |z - freqMoment 6 l| ≤ 0.1 * (freqMoment 6 l : ℝ)) l < 1 / 3 := by
  intro hA
  obtain ⟨c, hc, h⟩ := space_lower_bound_freqMoment 6 (by decide) (1 / 3) (by norm_num)
    (by norm_num)
  have bound := h 1 0 R A hA
  exact hc.not_ge (by simpa using bound)

-- A one-bit estimator can meet the guarantee with equality at the upper accuracy endpoint.
private noncomputable def endpointEstimator : StreamingAlgorithm (Fin 1) Unit 1 where
  init _ := 0
  step _ _ _ := 1
  out _ q := (q.val : ℝ) * (11 / 10)

example (l : List (Fin 1)) (hl : l.length ≤ 1) :
    endpointEstimator.failProb (fun l z => |z - freqMoment 6 l| ≤ 0.1 * (freqMoment 6 l : ℝ))
      l = 0 := by
  cases l with
  | nil =>
    norm_num [StreamingAlgorithm.failProb, StreamingAlgorithm.output, endpointEstimator, freqMoment]
  | cons a l =>
    have h : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst l
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have hF : freqMoment 6 ([0] : List (Fin 1)) = 1 := by decide
    norm_num [StreamingAlgorithm.failProb, StreamingAlgorithm.output, endpointEstimator, hF]

end MathlibExt.Probability.Streaming
