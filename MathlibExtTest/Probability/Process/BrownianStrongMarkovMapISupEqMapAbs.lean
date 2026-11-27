/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.BrownianStrongMarkovMapISupEqMapAbs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Tests for the law of the running maximum of Brownian motion

The equality of laws gives an expectation identity for measurable functions.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.Process.BrownianStrongMarkovMapISupEqMapAbs

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) {t : ℝ≥0} (ht : 0 < t)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂P.map (fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω)) =
      ∫ ω, f |B t ω| ∂P := by
  rw [MathlibExt.Probability.BrownianStrongMarkovWanted.IsBrownianReal.map_iSup_eq_map_abs
    hB hBm hcont ht]
  exact integral_map ((continuous_abs.measurable.comp (hBm t)).aemeasurable)
    hf.aestronglyMeasurable

end MathlibExtTest.Probability.Process.BrownianStrongMarkovMapISupEqMapAbs
