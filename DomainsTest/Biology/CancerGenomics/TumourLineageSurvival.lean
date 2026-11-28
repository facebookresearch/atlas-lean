/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.CancerGenomics.TumourLineageSurvival
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Tests for the survival probability of a tumour lineage: the offspring law encodes division
and death probabilities whose difference is the growth coefficient, a concrete growth coefficient
gives the closed forms, and the survival probability lies strictly between `0` and `2 a`. -/

namespace DomainsTest.Biology.CancerGenomics.TumourLineageSurvival

open MeasureTheory MathlibExt.Probability.GaltonWatson
  Domains.Biology.CancerGenomics.TumourLineageSurvival

/-- The offspring law `binaryOffspring ((1 + a) / 2)` lets a cell die with probability
`(1 - a) / 2` and divide with probability `(1 + a) / 2`. -/
example (a : ℝ) :
    binaryOffspring ((1 + a) / 2) {0} = ENNReal.ofReal ((1 - a) / 2) ∧
      binaryOffspring ((1 + a) / 2) {2} = ENNReal.ofReal ((1 + a) / 2) := by
  refine ⟨?_, binaryOffspring_apply_two⟩
  rw [binaryOffspring_apply_zero]
  congr 1
  ring

/-- The growth coefficient is the division probability minus the death probability. -/
example {a : ℝ} (ha0 : -1 ≤ a) (ha1 : a ≤ 1) :
    (binaryOffspring ((1 + a) / 2)).real {2} - (binaryOffspring ((1 + a) / 2)).real {0} = a := by
  rw [measureReal_def, measureReal_def, binaryOffspring_apply_two, binaryOffspring_apply_zero,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

/-- For `0 < a < 1` the offspring law is a probability measure, so the model is not vacuous. -/
example {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsProbabilityMeasure (binaryOffspring ((1 + a) / 2)) :=
  binaryOffspring_isProbabilityMeasure (by linarith) (by linarith)

/-- At growth coefficient `a = 1 / 3` a cell divides with probability `2 / 3`, and its lineage
goes extinct with probability `1 / 2` and survives with probability `1 / 2`. -/
example :
    extinctionProb (binaryOffspring ((1 + 1 / 3 : ℝ) / 2)) = 1 / 2 ∧
      1 - extinctionProb (binaryOffspring ((1 + 1 / 3 : ℝ) / 2)) = 1 / 2 := by
  obtain ⟨hq, hs⟩ := tumourLineage_survival.1 (1 / 3) (by norm_num) (by norm_num)
  rw [hs, hq]
  norm_num

/-- The survival probability is positive and at most `2 a`: the approximation `2 a` is an upper
bound. -/
example {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < 1 - extinctionProb (binaryOffspring ((1 + a) / 2)) ∧
      1 - extinctionProb (binaryOffspring ((1 + a) / 2)) ≤ 2 * a := by
  rw [(tumourLineage_survival.1 a ha0 ha1).2]
  have h1a : 0 < 1 + a := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h1a]
  nlinarith

end DomainsTest.Biology.CancerGenomics.TumourLineageSurvival
