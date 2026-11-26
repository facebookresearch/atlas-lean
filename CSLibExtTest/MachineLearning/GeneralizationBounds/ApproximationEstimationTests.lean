/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.ApproximationEstimation
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Tests for the approximation–estimation decomposition

A constant classifier predicts a Boolean label which is true with probability `1/4`.
Even the better of the two classifiers has positive risk. In a second model, positive real
predictions against a point mass at zero have risks tending to zero but never attain it.
-/

open MeasureTheory Set ProbabilityTheory
open CSLibExt.MachineLearning.GeneralizationBounds

namespace ApproximationEstimationTests

private noncomputable abbrev labels :=
  bernoulliMeasure true false ⟨(1 / 4 : ℝ), by constructor <;> norm_num⟩

private def miss (h y : Bool) : ℝ := if h = y then 0 else 1

private theorem risk_miss (h : Bool) : risk miss labels h = if h then 3 / 4 else 1 / 4 := by
  rw [risk, integral_bernoulliMeasure]
  cases h <;> norm_num [miss, smul_eq_mul]

private theorem bounded (H : Set Bool) : BddBelow (risk miss labels '' H) := by
  refine ⟨0, mem_lowerBounds_risk_image (fun h _ => integrable_bernoulliMeasure _ _ _ (miss h)) ?_⟩
  intro h _
  exact ae_of_all _ fun y => by unfold miss; split <;> norm_num

private theorem best : approximationError miss labels univ = 1 / 4 := by
  calc
    _ = risk miss labels false := (approximationError_eq_risk_iff (mem_univ _) (bounded _)).2
      (isMinOn_univ_iff.mpr fun h => by cases h <;> norm_num [risk_miss])
    _ = 1 / 4 := risk_miss false

-- A learner predicts the single label it saw. The class error stays at 1/4 for both samples.
private def predictSample (y : Bool) : (univ : Set Bool) := ⟨y, mem_univ _⟩

example : estimationError miss labels (predictSample false) = 0 ∧
    estimationError miss labels (predictSample true) = 1 / 2 := by
  simp only [estimationError, predictSample, best, risk_miss]
  norm_num

example (y : Bool) : risk miss labels (predictSample y) =
    1 / 4 + estimationError miss labels (predictSample y) ∧
    0 ≤ estimationError miss labels (predictSample y) := by
  simpa only [best] using risk_approximation_estimation_decomposition (bounded _) predictSample y

-- Adding the other constant classifier strictly improves the best available risk.
example : approximationError miss labels univ < approximationError miss labels {true} := by
  have hsingle : approximationError miss labels {true} = risk miss labels true := by
    simp [approximationError]
  apply lt_of_le_of_ne (approximationError_le_of_subset (singleton_nonempty true)
    (subset_univ _) (bounded _))
  rw [best, hsingle, risk_miss]
  norm_num

-- With absolute loss and strictly positive predictions the class infimum is not a minimum.
example : approximationError (fun h z : ℝ => |h - z|) (Measure.dirac 0) (Ioi 0) = 0 ∧
    ∀ h ∈ Ioi 0, 0 < risk (fun h z : ℝ => |h - z|) (Measure.dirac 0) h := by
  have hr (h : ℝ) (hh : h ∈ Ioi 0) : risk (fun h z : ℝ => |h - z|) (Measure.dirac 0) h = h := by
    simp [risk, abs_of_pos hh]
  refine ⟨?_, fun h hh => (hr h hh).symm ▸ hh⟩
  have himage : risk (fun h z : ℝ => |h - z|) (Measure.dirac 0) '' Ioi 0 = id '' Ioi 0 :=
    image_congr hr
  rw [approximationError, himage, image_id, csInf_Ioi]

end ApproximationEstimationTests
