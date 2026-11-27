/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LDPProduct

/-! Non-vacuity tests for superexponential tightness and the product LDP (Dirac masses). -/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.LDPProduct

namespace MathlibExtTest.Probability.LDPProduct

/-- Superexponential tightness for the Dirac LDP at `0` on `ℝ`. -/
example (ℓ : ℝ) : ∃ K : Set ℝ, IsCompact K ∧
    ∀ n : ℕ, Measure.dirac (0 : ℝ) Kᶜ ≤ ENNReal.ofReal (Real.exp (-(n * ℓ))) :=
  exists_isCompact_measure_compl_le (μ := fun _ => Measure.dirac (0 : ℝ))
    (satisfiesLDP_dirac (0 : ℝ)) (isGoodRateFunction_diracRate (0 : ℝ)) ℓ

/-- The product of the Dirac LDPs at `0` and `1` on `ℝ` is an LDP on `ℝ × ℝ`. -/
example : SatisfiesLDP (fun _ => (Measure.dirac (0 : ℝ)).prod (Measure.dirac (1 : ℝ)))
    (fun z : ℝ × ℝ => diracRate (0 : ℝ) z.1 + diracRate (1 : ℝ) z.2) :=
  satisfiesLDP_prod (μ := fun _ => Measure.dirac (0 : ℝ)) (ν := fun _ => Measure.dirac (1 : ℝ))
    (satisfiesLDP_dirac (0 : ℝ)) (isGoodRateFunction_diracRate (0 : ℝ))
    (satisfiesLDP_dirac (1 : ℝ)) (isGoodRateFunction_diracRate (1 : ℝ))

/-- The product rate function of two Dirac rate functions is good. -/
example : IsGoodRateFunction
    (fun z : ℝ × ℝ => diracRate (0 : ℝ) z.1 + diracRate (1 : ℝ) z.2) :=
  isGoodRateFunction_prod (isGoodRateFunction_diracRate (0 : ℝ))
    (isGoodRateFunction_diracRate (1 : ℝ))

end MathlibExtTest.Probability.LDPProduct
