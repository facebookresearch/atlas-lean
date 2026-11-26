/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LargeDeviationPrinciple

/-!
# Large deviation principles at a general speed

`MathlibExt.Probability.LargeDeviationPrinciple.SatisfiesLDP` is the large deviation principle at
speed `n`. Many large deviation principles run at other speeds: the empirical spectral measure of
a Gaussian random matrix of size `N` deviates at speed `N²` (Ben Arous and Guionnet), and moderate
deviations run at speeds `o(n)`. This file defines the principle at a speed `a : ℕ → ℝ` tending to
infinity, as in Guionnet's survey (Definition 2.1), and shows that speed `n` recovers
`SatisfiesLDP`.

## Main definitions

* `MathlibExt.Probability.LargeDeviationPrinciple.SatisfiesLDPAtSpeed a μ I`.

## Main results

* `satisfiesLDPAtSpeed_natCast_iff`: at speed `a N = N` the definition is `SatisfiesLDP`.

## References

* A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, arXiv:math/0409277, Definition 2.1.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace MathlibExt.Probability.LargeDeviationPrinciple

/-- **Large deviation principle at speed `a`** (Guionnet, "Large deviations and stochastic calculus
for large random matrices", *Probability Surveys* 1 (2004), Definition 2.1). A sequence of measures
`μ N` on `X` satisfies the LDP with rate function `I` at speed `a N → ∞` if `I` is lower
semicontinuous and, for open `U` and closed `F`,
`liminf (a N)⁻¹ log μ N U ≥ - inf_U I` and `limsup (a N)⁻¹ log μ N F ≤ - inf_F I`.
With `a N = N` this is `SatisfiesLDP` (`satisfiesLDPAtSpeed_natCast_iff`). -/
structure SatisfiesLDPAtSpeed {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (a : ℕ → ℝ) (μ : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  tendsto_speed : Tendsto a atTop atTop
  isRateFunction : IsRateFunction I
  lower_bound : ∀ U : Set X, IsOpen U →
    - (⨅ x ∈ U, (I x : EReal)) ≤
      liminf (fun n => ((a n : ℝ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun n => ((a n : ℝ) : EReal)⁻¹ * ENNReal.log (μ n F)) atTop ≤
      - (⨅ x ∈ F, (I x : EReal))

/-- **Speed `n` is the usual large deviation principle**: `SatisfiesLDPAtSpeed (fun n => n) μ I`
holds exactly when `SatisfiesLDP μ I` does. -/
theorem satisfiesLDPAtSpeed_natCast_iff {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (I : X → ℝ≥0∞) :
    SatisfiesLDPAtSpeed (fun n => (n : ℝ)) μ I ↔ SatisfiesLDP μ I := by
  have hc : ∀ n : ℕ, (((n : ℝ)) : EReal) = ((n : ℕ) : EReal) := fun n => by simp
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, fun U hU => by simpa only [hc] using h2 U hU,
      fun F hF => by simpa only [hc] using h3 F hF⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨tendsto_natCast_atTop_atTop, h1, fun U hU => by simpa only [hc] using h2 U hU,
      fun F hF => by simpa only [hc] using h3 F hF⟩

end MathlibExt.Probability.LargeDeviationPrinciple
