/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Identifiability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.Identifiability

/-- Duplicate parameter labels with equal estimand values are allowed: a constant estimand is
identified by any family, including one that is not injective. -/
example : IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ)) (fun _ => (1 : ℝ)) := by
  exact fun _ _ _ => rfl

/-- Two indistinguishable laws with different latent means are not identified. -/
example : ¬ IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) := by
  exact not_isIdentifiedBy_of_eq_of_ne (θ := true) (θ' := false) rfl (by norm_num)

/-- Strict separation matters: at the boundary `2ε = |τ θ - τ θ'|` (`τ θ = 0`, `τ θ' = 2`,
`ε = 1`) the constant estimator `δ ≡ 1` succeeds at both parameters, so the success
probabilities sum to `2`. -/
example : (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 0| ≤ 1} +
    (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 2| ≤ 1} = 2 := by
  rw [Measure.dirac_real_apply_of_mem (by norm_num),
    Measure.dirac_real_apply_of_mem (by norm_num)]
  norm_num

/-- `ε = 0` is admitted: exact recovery fails with probability at least `1/2` at one of two
indistinguishable parameters with distinct estimand values. -/
example {δ : ℝ → ℝ} (hδ : Measurable δ) :
    1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 0|} ∨
      1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 1|} := by
  exact exists_measureReal_failure_ge_half (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) (θ := false) (θ' := true) rfl hδ le_rfl (by norm_num)

end MathlibExtTest.Probability.Statistics.Identifiability
