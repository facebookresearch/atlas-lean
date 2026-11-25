/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.FunctionalInequalities.OttoVillani
import Mathlib.Tactic.NormNum

open MeasureTheory InformationTheory
open scoped ENNReal

open MathlibExt.Probability.OttoVillaniWanted (satisfiesTalagrand_of_satisfiesLogSobolev)
open MathlibExt.Probability.LogSobolevTalagrand (satisfiesLogSobolev_dirac)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein)

namespace MathlibExtTest.Probability.FunctionalInequalities.OttoVillani

private noncomputable def pointMass (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac x, inferInstance⟩

/-- Applying the theorem with the reference measure as the competitor gives a zero cost bound. -/
example (x : ℝ) : wasserstein 2 (pointMass x) (pointMass x) ^ (2 : ℝ) ≤ 0 := by
  have h := satisfiesTalagrand_of_satisfiesLogSobolev (pointMass x)
    (hα := zero_lt_one) (hm := satisfiesLogSobolev_dirac x 1) (pointMass x)
  simpa only [klDiv_self, mul_zero] using h

/-- A probability measure singular to the reference measure is still in the quantified domain. -/
example :
    wasserstein 2 (pointMass 1) (pointMass 0) ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 / 3) * klDiv (pointMass 1 : Measure ℝ) (pointMass 0 : Measure ℝ) :=
  satisfiesTalagrand_of_satisfiesLogSobolev (pointMass 0)
    (hα := by norm_num) (hm := satisfiesLogSobolev_dirac 0 3) (pointMass 1)

end MathlibExtTest.Probability.FunctionalInequalities.OttoVillani
