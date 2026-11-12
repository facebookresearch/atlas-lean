/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Education as an investment

A fixed finite-horizon model of the schooling decision: horizon `T`, per-period interest rate
`r`, wage stream `wE` with education (forgone earnings during schooling are inside `wE`),
wage stream `wN` without, and direct cost stream `c`. The lifetime value of each path is the
present value of its wages net of its costs, and education is preferred when its lifetime
value is larger.

Linearity of the finite present value gives the investment rule: education is (weakly)
preferred exactly when the present value of the incremental wage stream `wE - wN` exceeds (is
at least) the present value of the costs (`prefersEducation_iff`,
`valueWithout_le_valueWith_iff`). No sign or interest-rate restriction is needed; credit
constraints and endogenous schooling length are outside the model.

## Main results

* `MathlibExt.Economics.EducationInvestment.prefersEducation_iff`
* `MathlibExt.Economics.EducationInvestment.valueWithout_le_valueWith_iff`

Atlas roadmap target AP04.T02.
-/

namespace MathlibExt.Economics.EducationInvestment

open Finset

/-- Present value of the finite cash-flow stream `f 0, f 1, …, f (T - 1)` discounted at
the per-period interest rate `r`: `∑_{t < T} f t / (1 + r) ^ t`. The economic model takes
`-1 < r`. At `r = -1` Lean's convention `a / 0 = 0` makes every term after period `0`
vanish, so the value is not a present value there; the investment rules below are identities
that hold for every `r`, and so carry no rate hypothesis. -/
noncomputable def presentValue (r : ℝ) (T : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range T, f t / (1 + r) ^ t

/-- Lifetime value of the education path: present value of the wage stream `wE` earned with
education (zero, or a reduced wage, in schooling periods, so forgone earnings are inside
`wE`) minus the present value of the direct schooling costs `c`. -/
noncomputable def valueWithEducation (r : ℝ) (T : ℕ) (wE c : ℕ → ℝ) : ℝ :=
  presentValue r T wE - presentValue r T c

/-- Lifetime value of the no-education path: present value of the wage stream `wN`. -/
noncomputable def valueWithoutEducation (r : ℝ) (T : ℕ) (wN : ℕ → ℝ) : ℝ :=
  presentValue r T wN

/-- Under the fixed model (horizon `T`, rate `r`, wage streams `wE`, `wN`, cost stream `c`),
education is strictly preferred when its lifetime value exceeds the no-education value. -/
def PrefersEducation (r : ℝ) (T : ℕ) (wE wN c : ℕ → ℝ) : Prop :=
  valueWithoutEducation r T wN < valueWithEducation r T wE c

/-- Present value of the incremental stream `wE - wN` is the difference of present values. -/
theorem presentValue_sub (r : ℝ) (T : ℕ) (wE wN : ℕ → ℝ) :
    presentValue r T (fun t => wE t - wN t) =
      presentValue r T wE - presentValue r T wN := by
  simp only [presentValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [sub_div]

/-- **Education investment rule.** Education is strictly preferred exactly when the present
value of the incremental wage stream `wE - wN` exceeds the present value of its costs. -/
theorem prefersEducation_iff (r : ℝ) (T : ℕ) (wE wN c : ℕ → ℝ) :
    PrefersEducation r T wE wN c ↔
      presentValue r T c < presentValue r T (fun t => wE t - wN t) := by
  unfold PrefersEducation valueWithoutEducation valueWithEducation
  rw [presentValue_sub]
  constructor <;> intro h <;> linarith

/-- Weak form: education is weakly preferred exactly when the incremental wage present value
is at least the present value of its costs. -/
theorem valueWithout_le_valueWith_iff (r : ℝ) (T : ℕ) (wE wN c : ℕ → ℝ) :
    valueWithoutEducation r T wN ≤ valueWithEducation r T wE c ↔
      presentValue r T c ≤ presentValue r T (fun t => wE t - wN t) := by
  unfold valueWithoutEducation valueWithEducation
  rw [presentValue_sub]
  constructor <;> intro h <;> linarith

end MathlibExt.Economics.EducationInvestment
