/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue

/-!
# A binomial upper-tail test with a random total

Conditionally on each total of positive probability, the observed count has a binomial law.
Averaging the fixed-total validity bounds gives an unconditional bound at the observed total.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting
open scoped unitInterval

namespace MathlibExt.Probability.Statistics.ExactTests

/-- The upper tail of `Bin(D, p)` at the observed count is a valid p-value if the count
has law `Bin(d, p)` conditionally on each positive-probability total `D = d`. -/
theorem isValidPValue_binomialUpperTail_total_of_cond {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D B : Ω → ℕ} {p : I} (hDm : Measurable D)
    (hcond : ∀ d, μ {ω | D ω = d} ≠ 0 → HasLaw B Bin(d, p) (μ[|{ω | D ω = d}])) :
    IsValidPValue μ (fun ω => upperTailPValue Bin(D ω, p) B ω) :=
  isValidPValue_of_forall_cond_of_ne_zero (q := fun d => upperTailPValue Bin(d, p) B) hDm
    (ae_of_all μ fun _ => rfl) fun d hd => isValidPValue_upperTailPValue (hcond d hd)

end MathlibExt.Probability.Statistics.ExactTests
