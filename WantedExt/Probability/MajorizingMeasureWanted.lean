/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.GenericChaining
public import MathlibExt.Probability.GenericChainingGaussian
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# The majorizing measure theorem and Sudakov's minoration: wanted

For a centred Gaussian process `(X_t)_{t ∈ T}` with its canonical distance
`d(s, t) = (E(X_s - X_t)²)^{1/2}`, the generic chaining bound `E sup_t X_t ≤ L γ₂(T, d)`
(`MathlibExt.Probability.GenericChaining.integral_iSup_le_gammaTwo`; for Gaussian processes
`integral_iSup_le_gammaTwo_canonicalDist`, stated with the canonical distance
`MathlibExt.Probability.GenericChaining.canonicalDist` used below) can be reversed: Fernique and
Talagrand's majorizing measure theorem says `γ₂(T, d) / L ≤ E sup_t X_t ≤ L γ₂(T, d)`. The lower
bound rests on Sudakov's minoration, recorded below. Both are stated for a finite index set,
which is the setting of the source (its (2.2) defines the supremum over an infinite set through
finite subsets).

A Gaussian process is encoded by its law on `T → ℝ`, which must be a Gaussian measure
(`ProbabilityTheory.IsGaussian`: every continuous linear functional has a Gaussian image law), and
"centred" by `E X_t = 0` (the source's convention, its (2.1)).

## References

* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes: Decomposition Theorems*,
  2nd ed., Ergebnisse 60, Springer 2021, Theorem 2.10.1 and Lemma 2.10.2.
-/

@[expose] public section

namespace MathlibExt.Probability.MajorizingMeasureWanted

open MeasureTheory ProbabilityTheory MathlibExt.Probability.GenericChaining
open scoped ENNReal

/-- **Majorizing measure theorem** (Fernique–Talagrand; Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, Theorem 2.10.1). There is a universal constant `L > 0`
such that for every centred Gaussian process `(X_t)_{t ∈ T}` indexed by a finite nonempty set,
with canonical distance `d`, `γ₂(T, d) / L ≤ E sup_{t ∈ T} X_t ≤ L γ₂(T, d)`. The right-hand
inequality is the generic chaining bound; the left-hand one is the content of the theorem. -/
theorem_wanted majorizing_measure :
    ∃ L : ℝ, 0 < L ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (T : Type*) [Fintype T] [Nonempty T] (X : T → Ω → ℝ),
      (∀ t, Measurable (X t)) → IsGaussian (P.map fun ω t => X t ω) →
      (∀ t, ∫ ω, X t ω ∂P = 0) →
        gammaFunctional 2 (canonicalDist P X) ≤
            ENNReal.ofReal L * ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ∧
          ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤
            ENNReal.ofReal L * gammaFunctional 2 (canonicalDist P X)

/-- **Sudakov minoration** (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, Lemma 2.10.2). There is a universal constant `L₁ > 0` such that for every centred
Gaussian process `(X_t)_{t ∈ T}` on a finite nonempty set whose points are pairwise `a`-separated
for the canonical distance (`d(s, t) ≥ a` whenever `s ≠ t`), `E sup_{t ∈ T} X_t ≥
(a / L₁) √(log card T)`. -/
theorem_wanted sudakov_minoration :
    ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (T : Type*) [Fintype T] [Nonempty T] (X : T → Ω → ℝ) (a : ℝ),
      (∀ t, Measurable (X t)) → IsGaussian (P.map fun ω t => X t ω) →
      (∀ t, ∫ ω, X t ω ∂P = 0) → 0 ≤ a →
      (∀ s t, s ≠ t → ENNReal.ofReal a ≤ canonicalDist P X s t) →
        a / L₁ * Real.sqrt (Real.log (Fintype.card T)) ≤ ∫ ω, ⨆ t, X t ω ∂P

end MathlibExt.Probability.MajorizingMeasureWanted
