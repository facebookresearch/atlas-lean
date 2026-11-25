/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContractionPrinciple
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Tests for the contraction principle

Non-vacuity checks on the Dirac large deviation principle on `ℝ`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.ContractionPrinciple

namespace MathlibExtTest.Probability.ContractionPrinciple

/-- Pushing the Dirac LDP at `0` forward by `x ↦ 2x + 1` gives an LDP on `ℝ`. -/
example : SatisfiesLDP (fun _ => (Measure.dirac (0 : ℝ)).map (fun x => 2 * x + 1))
    (pushforwardRate (fun x : ℝ => 2 * x + 1) (diracRate 0)) :=
  satisfiesLDP_map (satisfiesLDP_dirac (0 : ℝ)) (isGoodRateFunction_diracRate 0) (by fun_prop)

/-- The push-forward of the good rate function `|x|` by `x ↦ x ^ 2` is good. -/
example : IsGoodRateFunction
    (pushforwardRate (fun x : ℝ => x ^ 2) (fun x : ℝ => ENNReal.ofReal |x|)) :=
  isGoodRateFunction_pushforwardRate (by fun_prop) isGoodRateFunction_abs

/-- The push-forward rate is `∞` off the range: no `x` has `x ^ 2 = -1`. -/
example : pushforwardRate (fun x : ℝ => x ^ 2) (fun x : ℝ => ENNReal.ofReal |x|) (-1) = ⊤ := by
  simp only [pushforwardRate]
  refine iInf₂_eq_top.mpr fun x hx => ?_
  have : x ^ 2 = -1 := hx
  nlinarith [sq_nonneg x]

/-- The contraction infimum is attained for a good rate function. -/
example : ∃ x : ℝ, x ^ 2 = 4 ∧ ENNReal.ofReal |x| =
    pushforwardRate (fun x : ℝ => x ^ 2) (fun x : ℝ => ENNReal.ofReal |x|) 4 := by
  have hne : pushforwardRate (fun x : ℝ => x ^ 2) (fun x : ℝ => ENNReal.ofReal |x|) 4 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le (2 : ℝ) ?_)
    show (2 : ℝ) ^ 2 = 4
    norm_num
  exact exists_eq_pushforwardRate (by fun_prop) isGoodRateFunction_abs hne

end MathlibExtTest.Probability.ContractionPrinciple
