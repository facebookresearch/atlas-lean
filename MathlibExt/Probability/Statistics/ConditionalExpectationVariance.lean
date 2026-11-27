/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CondVar
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic.Linarith

/-!
# Variance of a conditional expectation

Conditioning cannot increase variance: for a sub-σ-algebra `m` on a probability space and
a square-integrable payoff `X`, `Var[E[X | m]] ≤ Var[X]`. This is the law of total
variance (`ProbabilityTheory.integral_condVar_add_variance_condExp`),
`E[Var[X | m]] + Var[E[X | m]] = Var[X]`, plus the nonnegativity of the first term: a
conditional variance is a conditional expectation of a square. The law of total variance
is cited, not reproved.

## Main results

* `variance_condExp_le`: `Var[μ[X | m]; μ] ≤ Var[X; μ]`.

## References

* Law of total variance (standard; see e.g. J. H. Cochrane, *Asset Pricing* (2005),
  discussion of conditioning).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Finance.ConditionalExpectationVariance

/-- **Variance of a conditional expectation is no larger than the variance of the payoff.**
For a sub-σ-algebra `m` of `m₀` on a probability space and `X` square-integrable,
`Var[E[X | m]] ≤ Var[X]`. Conditioning (partial information) cannot increase variance. -/
theorem variance_condExp_le {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : m ≤ m₀) (hX : MemLp X 2 μ) :
    Var[μ[X | m]; μ] ≤ Var[X; μ] := by
  have h := ProbabilityTheory.integral_condVar_add_variance_condExp hm hX
  have hsq : (0 : Ω → ℝ) ≤ᵐ[μ] (X - μ[X | m]) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hcond : (0 : Ω → ℝ) ≤ᵐ[μ] Var[X; μ | m] := by
    unfold ProbabilityTheory.condVar
    exact MeasureTheory.condExp_nonneg hsq
  have hnonneg : 0 ≤ μ[Var[X; μ | m]] := integral_nonneg_of_ae hcond
  linarith

end MathlibExt.Probability.Finance.ConditionalExpectationVariance
