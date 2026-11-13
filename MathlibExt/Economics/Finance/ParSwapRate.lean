/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Par swap rate for a fixed-for-floating interest-rate swap

Frozen convention (unit accrual, notional 1, payment dates `1, …, T`): the
fixed leg pays the rate `s` at each payment date, and the floating leg's
present value at date `t` is `D (t - 1) - D t`, the forward-rate payment over
`[t - 1, t]` discounted. The floating leg telescopes to `1 - D T` when
`D 0 = 1`, and the par rate `(1 - D T) / ∑_{t∈Icc 1 T} D t` equates the legs.

## Main results

* `MathlibExt.Economics.Finance.swapFloatingLeg_eq`: the floating leg
  telescopes (`Finset.sum_Ico_eq_sum_range`, `Finset.sum_range_sub'`).
* `MathlibExt.Economics.Finance.parSwapRate_eq_fixed_eq_floating`: the fixed
  leg at the par rate equals the floating leg, when the annuity denominator
  is nonzero.

No positivity or monotonicity of the discount curve is assumed.

## References

SOA Exam FM syllabus (interest-rate swaps); Hull, *Options, Futures and Other
Derivatives*, par swap rate. Atlas roadmap target FI03.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Present value of the fixed leg of a unit-notional swap paying rate `s` at
each payment date `t = 1, …, T`, under discount factors `D` with unit accrual
(source clause: "fixed leg = `s * Σ_t D_t`"). -/
noncomputable def swapFixedLeg (s : ℝ) (D : ℕ → ℝ) (T : ℕ) : ℝ :=
  s * ∑ t ∈ Finset.Icc 1 T, D t

/-- Present value of the floating leg: at payment date `t` the floating
payment's present value is `D (t - 1) - D t` (source clause: "floating payment
at `t` is the forward rate over `[t-1, t]`, discounted"). -/
noncomputable def swapFloatingLeg (D : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (D (t - 1) - D t)

/-- Par swap rate: `(1 - D T) / ∑_{t∈Icc 1 T} D t` (source clause: "par rate
equates fixed and floating legs"). Unit accrual is frozen in the convention. -/
noncomputable def parSwapRate (D : ℕ → ℝ) (T : ℕ) : ℝ :=
  (1 - D T) / ∑ t ∈ Finset.Icc 1 T, D t

/-- The floating leg telescopes to `1 - D T` when `D 0 = 1`
(Atlas roadmap FI03.T04). -/
theorem swapFloatingLeg_eq (D : ℕ → ℝ) (T : ℕ) (hD0 : D 0 = 1) :
    swapFloatingLeg D T = 1 - D T := by
  unfold swapFloatingLeg
  rw [← Finset.Ico_add_one_right_eq_Icc 1 T, Finset.sum_Ico_eq_sum_range]
  have hT : T + 1 - 1 = T := by omega
  rw [hT]
  have hsimp : ∀ k : ℕ, (D (1 + k - 1) - D (1 + k)) = (D k - D (k + 1)) := by
    intro k
    have e1 : 1 + k - 1 = k := by omega
    have e2 : 1 + k = k + 1 := by omega
    rw [e1, e2]
  simp_rw [hsimp]
  rw [Finset.sum_range_sub' D T, hD0]

/-- The fixed leg at the par rate equals the floating leg, when the annuity
denominator is nonzero (Atlas roadmap FI03.T04). -/
theorem parSwapRate_eq_fixed_eq_floating (D : ℕ → ℝ) (T : ℕ) (hD0 : D 0 = 1)
    (hden : (∑ t ∈ Finset.Icc 1 T, D t) ≠ 0) :
    swapFixedLeg (parSwapRate D T) D T = swapFloatingLeg D T := by
  unfold swapFixedLeg parSwapRate
  rw [swapFloatingLeg_eq D T hD0]
  exact div_mul_cancel₀ _ hden

end MathlibExt.Economics.Finance
