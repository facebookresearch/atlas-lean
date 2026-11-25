/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.WassersteinTotalVariation
public import Mathlib.Topology.UnitInterval

@[expose] public section

open MeasureTheory
open scoped ENNReal unitInterval
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.Probability.TotalVariationDistance (totalVariationDist)

namespace MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinTotalVariation

-- The unit interval has diameter at most `1`.
private lemma edist_le_one_unitInterval (x y : I) : edist x y ≤ ((1 : NNReal) : ℝ≥0∞) := by
  rw [edist_dist, ENNReal.coe_one, ENNReal.ofReal_le_one, Subtype.dist_eq, Real.dist_eq,
    abs_sub_le_iff]
  have hx := x.2; have hy := y.2
  simp only [Set.mem_Icc] at hx hy
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- On the unit interval, `W_1` is at most the total variation distance. -/
example (μ ν : ProbabilityMeasure I) :
    wasserstein 1 μ ν ≤ ENNReal.ofReal (totalVariationDist (μ : Measure I) (ν : Measure I)) := by
  simpa using wasserstein_one_le_mul_totalVariationDist edist_le_one_unitInterval μ ν

end MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinTotalVariation
