/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Net present value and internal rate of return

A project has dated cash flows `c 0, …, c N` (`c 0` today, `c k` at the end of period `k`).
Its net present value at rate `r` is the FI01 present value over the dates `0, …, N`, and an
internal rate of return is a rate above `-1` at which the net present value is zero.

## Main results

* `MathlibExt.Economics.Finance.strictAntiOn_npv`: with later flows nonnegative and at least
  one positive, NPV is strictly decreasing in the rate on `(-1, ∞)`.
* `MathlibExt.Economics.Finance.npv_pos_iff_lt_irr`: for such a project with an IRR `ρ`, the
  NPV at a rate `r > -1` is positive exactly when `r < ρ` (`StrictAntiOn.lt_iff_gt`).

The conventional-project condition `c 0 < 0` is what makes an IRR exist (roadmap FI02.T01);
the equivalence needs only the IRR hypothesis, so `c 0 < 0` is not assumed here.

## References

OpenStax, *Principles of Finance*, capital budgeting; SOA Exam FM and IFM syllabi. Atlas
roadmap target FI02.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Net present value at rate `r` of a project with dated cash flows `c 0, c 1, …, c N`
(`c 0` today, `c k` at the end of period `k`), as the FI01 present value over the dates
`0, …, N` (source clause: "NPV(r) = Σ_{k=0}^N c_k (1 + r)⁻ᵏ"). Meaningful for `r > -1`. -/
noncomputable def npv (c : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  presentValue (discountFactor r) (Finset.range (N + 1)) c

/-- `r` is an internal rate of return of the cash flows `c 0, …, c N`: a rate above `-1`
at which the net present value is zero (source clause: "IRR: NPV(IRR) = 0"). -/
def IsIRR (c : ℕ → ℝ) (N : ℕ) (r : ℝ) : Prop :=
  -1 < r ∧ npv c N r = 0

/-- With nonnegative later cash flows, at least one positive, the NPV is strictly
decreasing in the rate on `(-1, ∞)`. -/
theorem strictAntiOn_npv {c : ℕ → ℝ} {N : ℕ} (hnn : ∀ k ∈ Finset.Icc 1 N, 0 ≤ c k)
    (hpos : ∃ k ∈ Finset.Icc 1 N, 0 < c k) : StrictAntiOn (npv c N) (Set.Ioi (-1)) := by
  -- Split off `k = 0` (Finset.sum_range_succ'); strict decrease by Finset.sum_lt_sum
  -- (pointwise: pow_le_pow_left₀, inv_anti₀; strict: pow_lt_pow_left₀, inv_lt_inv₀).
  intro r hr s hs hrs
  simp only [Set.mem_Ioi] at hr hs
  have h1r : (0:ℝ) < 1 + r := by linarith
  have h1s : (0:ℝ) < 1 + s := by linarith
  have hlt : (1:ℝ) + r < 1 + s := by linarith
  unfold npv presentValue discountFactor
  simp only [Finset.sum_range_succ', pow_zero, inv_one, one_mul]
  apply add_lt_add_left
  refine Finset.sum_lt_sum ?_ ?_
  · intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hmem : k + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hpow : (1 + r) ^ (k + 1) ≤ (1 + s) ^ (k + 1) :=
      pow_le_pow_left₀ h1r.le hlt.le (k + 1)
    have hinv : ((1 + s) ^ (k + 1))⁻¹ ≤ ((1 + r) ^ (k + 1))⁻¹ :=
      inv_anti₀ (pow_pos h1r (k + 1)) hpow
    exact mul_le_mul_of_nonneg_right hinv (hnn (k + 1) hmem)
  · obtain ⟨k₀, hk₀mem, hk₀pos⟩ := hpos
    obtain ⟨hk₀lo, hk₀hi⟩ := Finset.mem_Icc.mp hk₀mem
    have hk₀ne : k₀ ≠ 0 := by omega
    have hjmem : k₀ - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    refine ⟨k₀ - 1, hjmem, ?_⟩
    rw [Nat.sub_add_cancel hk₀lo]
    have hpow : (1 + r) ^ k₀ < (1 + s) ^ k₀ :=
      pow_lt_pow_left₀ hlt h1r.le hk₀ne
    have hinv : ((1 + s) ^ k₀)⁻¹ < ((1 + r) ^ k₀)⁻¹ :=
      (inv_lt_inv₀ (pow_pos h1s k₀) (pow_pos h1r k₀)).mpr hpow
    exact mul_lt_mul_of_pos_right hinv hk₀pos

/-- For a project with nonnegative later cash flows, at least one positive, and an
internal rate of return `ρ`, the NPV at any rate `r > -1` is positive exactly when
`r < ρ` (Atlas roadmap FI02.T02). -/
theorem npv_pos_iff_lt_irr {c : ℕ → ℝ} {N : ℕ} {ρ r : ℝ}
    (hnn : ∀ k ∈ Finset.Icc 1 N, 0 ≤ c k) (hpos : ∃ k ∈ Finset.Icc 1 N, 0 < c k)
    (hρ : IsIRR c N ρ) (hr : -1 < r) :
    0 < npv c N r ↔ r < ρ := by
  -- Order transfer via StrictAntiOn.lt_iff_gt (cf. StrictAntiOn.injOn).
  have hmemρ : ρ ∈ Set.Ioi (-1) := hρ.1
  have hmemr : r ∈ Set.Ioi (-1) := hr
  rw [← hρ.2]
  exact (strictAntiOn_npv hnn hpos).lt_iff_gt hmemρ hmemr

end MathlibExt.Economics.Finance
