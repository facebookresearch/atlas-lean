/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LDPSpeed

/-!
# Tests for large deviation principles at a general speed
-/

open MeasureTheory MathlibExt.Probability.LargeDeviationPrinciple

namespace MathlibExtTest.Probability.LDPSpeed

/-- At speed `n` the general definition is the usual one, in both directions. -/
example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : ℕ → Measure X) (I : X → ENNReal) (h : SatisfiesLDP μ I) :
    SatisfiesLDPAtSpeed (fun n => (n : ℝ)) μ I :=
  (satisfiesLDPAtSpeed_natCast_iff μ I).2 h

/-- The speed of a large deviation principle tends to infinity, e.g. `N²` for random matrices. -/
example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : ℕ → Measure X) (I : X → ENNReal)
    (h : SatisfiesLDPAtSpeed (fun N => (N : ℝ) ^ 2) μ I) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
  h.tendsto_speed

end MathlibExtTest.Probability.LDPSpeed
