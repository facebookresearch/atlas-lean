/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent

/-!
# Tests for Beta-coalescent merger rates

The total rate `λ_{2,2}` is `1` for every admissible `α`, and at `α = 1` the rate
`λ_{3,2}` is `1/2`.
-/

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.BetaCoalescent

open MeasureTheory ProbabilityTheory unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent

/-! ### Boundary and non-vacuity checks -/

/-- `λ_{2,2} = 1` for every `0 < α < 2` (total mass of a probability `Λ`), from the closed form,
matching Atlas `mergerRate_two_two`. -/
example {α : ℝ} (h0 : 0 < α) (h2 : α < 2) [IsFiniteMeasure (betaLambda α)] :
    mergerRate (betaLambda α) 2 2 = 1 := by
  rw [mergerRate_betaLambda h0 h2 le_rfl le_rfl]
  have hB := (beta_pos (by linarith : (0 : ℝ) < 2 - α) h0).ne'
  push_cast
  rw [show (2 : ℝ) - 2 + α = α by ring]
  exact div_self hB

example {α : ℝ} (h0 : 0 < α) (h2 : α < 2) :
    have := isProbabilityMeasure_betaLambda h0 h2
    mergerRate (betaLambda α) 2 2 = (betaLambda α).real Set.univ := by
  have := isProbabilityMeasure_betaLambda h0 h2
  exact mergerRate_two_two _

/-- At `α = 1`, `b = 3`, `k = 2`: `λ_{3,2} = 0! 1! / 2! = 1/2`. -/
example : haveI := isProbabilityMeasure_betaLambda (α := 1) one_pos one_lt_two
    mergerRate (betaLambda 1) 3 2 = 1 / 2 := by
  have := isProbabilityMeasure_betaLambda (α := 1) one_pos one_lt_two
  rw [mergerRate_betaLambda_one (by norm_num) (by norm_num), mergerRate_volume (by norm_num)
    (by norm_num)]
  norm_num [Nat.factorial]

#print axioms isProbabilityMeasure_betaLambda
#print axioms mergerRate_betaLambda
#print axioms betaLambda_one
#print axioms beta_consistent

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.BetaCoalescent
