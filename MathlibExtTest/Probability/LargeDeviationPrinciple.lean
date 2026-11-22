/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LargeDeviationPrinciple
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple

namespace MathlibExtTest.Probability.LargeDeviationPrinciple

/-- The Dirac mass at `0` on `ℝ` satisfies the LDP with its Dirac rate
function, restated with its exact public signature. -/
example : SatisfiesLDP (fun _ => Measure.dirac (0 : ℝ)) (diracRate 0) :=
  satisfiesLDP_dirac 0

/-- The Borel-form LDP bounds for the Dirac mass at `0`, applied to
the set `{x | x ≤ 1}`. -/
example := (satisfiesLDP_dirac (0 : ℝ)).borel_bounds (Set.Iic 1)

/-- The Borel-form bounds imply the open/closed form: the Dirac LDP
can be recovered from its Borel bounds. -/
example : SatisfiesLDP (fun _ => Measure.dirac (0 : ℝ)) (diracRate 0) :=
  satisfiesLDP_of_borel_bounds (satisfiesLDP_dirac 0).isRateFunction
    (fun Γ _hΓ => (satisfiesLDP_dirac (0 : ℝ)).borel_bounds Γ)

/-- `x ↦ ENNReal.ofReal |x|` is a good rate function on `ℝ`. -/
example : IsGoodRateFunction (fun x : ℝ => ENNReal.ofReal |x|) :=
  isGoodRateFunction_abs

/-- A good rate function is a rate function. -/
example : IsRateFunction (fun x : ℝ => ENNReal.ofReal |x|) :=
  isGoodRateFunction_abs.isRateFunction

/-- The Dirac rate function vanishes at its center and is infinite
elsewhere. -/
example : diracRate (0 : ℝ) 0 = 0 := diracRate_apply_self 0

example : diracRate (0 : ℝ) 1 = ⊤ := diracRate_apply_of_ne one_ne_zero

/-- The infimum of the Dirac rate function over `[0, 1]` is `0`,
since the center lies in the interval. -/
example : (⨅ x ∈ Set.Icc (0 : ℝ) 1, ((diracRate (0 : ℝ) x : ℝ≥0∞) : EReal)) = 0 :=
  iInf_diracRate_of_mem (by simp)

/-- The infimum of the Dirac rate function over `(0, 1]` is `∞`,
since the center does not lie in the interval. -/
example : (⨅ x ∈ Set.Ioc (0 : ℝ) 1, ((diracRate (0 : ℝ) x : ℝ≥0∞) : EReal)) = ⊤ :=
  iInf_diracRate_of_notMem (by simp)

/-- A caller with bounds only for measurable sets can use the converse. -/
example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞} (hRate : IsRateFunction I)
    (hBorel : ∀ Γ : Set X, MeasurableSet Γ →
      - (⨅ x ∈ interior Γ, (I x : EReal)) ≤
          liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ∧
        limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ≤
          - (⨅ x ∈ closure Γ, (I x : EReal))) :
    SatisfiesLDP μ I :=
  satisfiesLDP_of_borel_bounds hRate hBorel

#print axioms satisfiesLDP_dirac
#print axioms isGoodRateFunction_abs
#print axioms SatisfiesLDP.borel_bounds
#print axioms satisfiesLDP_of_borel_bounds

end MathlibExtTest.Probability.LargeDeviationPrinciple

end
