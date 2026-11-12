/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Policy invariance counterexample (Lucas critique example)

The structural equation `y = θ * πe` is the same in every regime; the policy rule
`πe = λ * m` varies by regime. The reduced-form coefficient `θ * λ` is therefore not
policy invariant: one finite numerical example, not a general Lucas-critique theorem.

## Main results

* `MathlibExt.Economics.Macro.PolicyInvariance.policyOutcome_eq_reducedCoeff`: reduced form.
* `MathlibExt.Economics.Macro.PolicyInvariance.lucas_notInvariant`: two-regime counterexample.
-/

namespace MathlibExt.Economics.Macro.PolicyInvariance

/-- A policy regime: the policy rule mapping money growth `m` to expected inflation
`πe = expectationCoeff * m`. The structural parameter `θ` below is the same in every
regime; only the policy-rule coefficient varies. -/
structure PolicyRegime where
  expectationCoeff : ℝ

/-- The reduced-form coefficient of money growth on the outcome: the structural response
`θ` times the regime's policy-rule coefficient. -/
def reducedFormCoeff (θ : ℝ) (regime : PolicyRegime) : ℝ :=
  θ * regime.expectationCoeff

/-- The outcome under a regime: the structural equation `y = θ * πe` composed with the
regime's policy rule `πe = expectationCoeff * m`. -/
def policyOutcome (θ : ℝ) (regime : PolicyRegime) (m : ℝ) : ℝ :=
  θ * (regime.expectationCoeff * m)

/-- **Reduced form (MA06.T04).** The outcome equals the reduced-form coefficient times
money growth: `policyOutcome θ regime m = reducedFormCoeff θ regime * m`. -/
theorem policyOutcome_eq_reducedCoeff (θ : ℝ) (regime : PolicyRegime) (m : ℝ) :
    policyOutcome θ regime m = reducedFormCoeff θ regime * m := by
  simp [policyOutcome, reducedFormCoeff]
  ring

/-- **Two-regime counterexample (MA06.T04, Lucas critique example).** With the same
structural parameter `θ = 2`, the reduced-form coefficient is `2` under the regime with
policy-rule coefficient `1` and `6` under the regime with coefficient `3`: the
reduced-form coefficient is not policy invariant. This is a finite numerical example,
not a general Lucas-critique theorem. -/
theorem lucas_notInvariant :
    reducedFormCoeff (2 : ℝ) ⟨1⟩ = 2 ∧ reducedFormCoeff (2 : ℝ) ⟨3⟩ = 6 ∧
      reducedFormCoeff (2 : ℝ) ⟨1⟩ ≠ reducedFormCoeff (2 : ℝ) ⟨3⟩ := by
  norm_num [reducedFormCoeff]

end MathlibExt.Economics.Macro.PolicyInvariance
