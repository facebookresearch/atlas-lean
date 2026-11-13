/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Level annuity-immediate

`annuityImmediate r n` is the present value of one unit paid at each of the dates `1, …, n` at
the constant per-period rate `r`, stated with the FI01 present value
`presentValue (discountFactor r) (Finset.Icc 1 n) (fun _ => 1)`.

## Main results

* `MathlibExt.Economics.Finance.annuityImmediate_eq_of_ne_zero`: for `r ≠ 0` and `1 + r ≠ 0`,
  `a_n = (1 - (1 + r)⁻ⁿ) / r` (Mathlib `geom_sum_eq` at `(1 + r)⁻¹`).
* `MathlibExt.Economics.Finance.annuityImmediate_zero_rate`: the zero-rate branch `a_n = n`.

`1 + r ≠ 0` is weaker than the usual `r > -1`; at `r = -1` the closed form fails (the
discount factor takes its junk value `0`), so the hypothesis cannot be dropped.

## References

SOA Exam FM syllabus (annuities); OpenStax, *Principles of Finance*, time value of money.
Atlas roadmap target FI01.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Present value of a level annuity-immediate: one unit paid at each of the dates
`1, …, n`, discounted at the constant per-period rate `r` (source clause:
"`a_n = Σ_{t=1}^n v^t`, `v = (1 + r)⁻¹`"). -/
noncomputable def annuityImmediate (r : ℝ) (n : ℕ) : ℝ :=
  presentValue (discountFactor r) (Finset.Icc 1 n) (fun _ => 1)

/-- Geometric closed form of the level annuity for a nonzero rate with `1 + r ≠ 0`:
`a_n = (1 - (1 + r)⁻ⁿ) / r` (Atlas roadmap FI01.T02). -/
theorem annuityImmediate_eq_of_ne_zero (r : ℝ) (n : ℕ) (hr : r ≠ 0) (h1r : 1 + r ≠ 0) :
    annuityImmediate r n = (1 - ((1 + r) ^ n)⁻¹) / r := by
  have hterm : ∀ t : ℕ, discountFactor r t * 1 = ((1 + r)⁻¹) ^ t := by
    intro t
    simp only [discountFactor, mul_one, ← inv_pow]
  have hvr : (1 + r)⁻¹ ≠ 1 := by
    intro hcon
    apply hr
    have hmul : (1 + r)⁻¹ * (1 + r) = (1 : ℝ) * (1 + r) := by rw [hcon]
    rw [inv_mul_cancel₀ h1r, one_mul] at hmul
    have h2 : (1:ℝ) + r = 1 + 0 := by rw [add_zero]; exact hmul.symm
    exact add_left_cancel h2
  have hann : annuityImmediate r n = ∑ t ∈ Finset.Icc 1 n, ((1 + r)⁻¹) ^ t := by
    simp [annuityImmediate, presentValue, hterm]
  have hgen : ∀ m : ℕ, (∑ t ∈ Finset.Icc 1 m, ((1 + r)⁻¹) ^ t)
      = (1 + r)⁻¹ * ∑ i ∈ Finset.range m, ((1 + r)⁻¹) ^ i := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1le : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have hIcc := Finset.sum_Icc_succ_top h1le (fun t => ((1 + r)⁻¹) ^ t)
      rw [hIcc, ihm, Finset.sum_range_succ, mul_add, pow_succ']
  rw [hann, hgen, geom_sum_eq hvr n, inv_pow]
  have hv1 : (1 + r)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hvr
  have hpow : (1 + r) ^ n ≠ 0 := pow_ne_zero n h1r
  field_simp
  rw [show (1:ℝ) - (1 + r) = -r by ring]
  field_simp
  ring

/-- Zero-rate branch of the level annuity: `a_n = n` (Atlas roadmap FI01.T02). -/
theorem annuityImmediate_zero_rate (n : ℕ) : annuityImmediate 0 n = n := by
  simp only [annuityImmediate, presentValue, discountFactor]
  simp only [add_zero, one_pow, inv_one, mul_one]
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_one]

end MathlibExt.Economics.Finance
