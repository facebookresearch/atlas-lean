/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.QuantMutationSelection

/-!
# Tests for the continuum-of-alleles model

The examples evaluate the one-generation map on Dirac masses and on a centred Gaussian.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Nat

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.QuantMutationSelection

open MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection

/-- The hypotheses are satisfiable (`Vs = 1`, `μ = 1/2`, `γ = 1`). -/
noncomputable example : Params := ⟨1, 1 / 2, 1, one_pos, by norm_num, by norm_num, one_pos⟩

/-- Monomorphic optimum `δ₀` is symmetric: one generation gives mean 0 and variance `μ γ²`. -/
example (P : Params) : ∫ x, x ∂(P.step (Measure.dirac 0)) = 0 :=
  P.integral_id_step_eq_zero_of_map_neg _ (by simp [Measure.map_dirac' measurable_neg])

example (P : Params) : Var[id; P.step (Measure.dirac 0)] = P.mu * P.gamma ^ 2 := by
  rw [P.variance_step]
  have := P.isProbabilityMeasure_select (Measure.dirac 0)
  rw [variance_eq_sub (P.memLp_id_select _)]
  have e1 := P.integral_id_select (Measure.dirac 0)
  have e2 := P.integral_sq_select (Measure.dirac 0)
  simp only [integral_dirac] at e1 e2
  change (∫ x, x ^ 2 ∂P.select (Measure.dirac 0)) - (∫ x, x ∂P.select (Measure.dirac 0)) ^ 2
    + P.mu * P.gamma ^ 2 = P.mu * P.gamma ^ 2
  rw [e1, e2]; simp

/-- Without symmetry the mean need not vanish: `δ_a` stays at mean `a` after one step. -/
example (P : Params) (a : ℝ) : ∫ x, x ∂(P.step (Measure.dirac a)) = a := by
  rw [P.integral_id_step, P.integral_id_select, integral_dirac, integral_dirac,
    mul_div_assoc, div_self (P.fitness_pos a).ne', mul_one]

/-- A symmetric Gaussian allelic distribution also gives mean 0. -/
example (P : Params) (v : ℝ≥0) : ∫ x, x ∂(P.step (gaussianReal 0 v)) = 0 :=
  P.integral_id_step_eq_zero_of_map_neg _ (by simpa using gaussianReal_map_neg (μ := 0) (v := v))

#print axioms MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection.Params.isProbabilityMeasure_step
#print axioms MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection.Params.variance_step
#print axioms MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection.Params.integral_id_step_eq_zero_of_map_neg

end MathlibExtTest.Biology.PopulationGenetics.Classical.QuantMutationSelection
