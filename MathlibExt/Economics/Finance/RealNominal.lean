/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow

import Mathlib.Tactic

@[expose] public section

/-!
# Real and nominal present values agree

Dated cash flows and present values are those of `MathlibExt.Economics.Finance.DatedCashFlow`. If
each real cash flow `c t` is inflated by a price index `I t ≠ 0` and discounted by the matching
nominal factor `D t / I t`, where `D` is the real term structure, the nominal present value equals
the real present value: the index cancels date by date. With constant inflation `π` and the
Fisher relation `1 + i = (1 + r)(1 + π)`, nominal flows discounted at the nominal rate `i` have the
real present value at the real rate `r`. Mixing conventions (nominal flows, real rate) changes the
value.

## Main results

* `presentValue_nominal_eq_real`: consistent deflation of flows and factors preserves NPV.
* `presentValue_nominal_eq_real_const`: the constant-inflation (Fisher) case.

## References

* R. A. Brealey, S. C. Myers and F. Allen, *Principles of Corporate Finance*, McGraw-Hill,
  chapter on making investment decisions with the NPV rule (inflation and capital budgeting).
* I. Fisher, *The Theory of Interest*, Macmillan (1930).
-/

namespace MathlibExt.Economics.Finance.RealNominal

open MathlibExt.Economics.Finance

/-- **Real and nominal NPV agree.** If each real cash flow `c t` is inflated by the price index
`I t ≠ 0` (nominal flow `I t * c t`) and discounted by the corresponding nominal factor
`D t / I t`, where `D` is the real term structure, the nominal present value equals the real
present value. -/
theorem presentValue_nominal_eq_real (D I : ℕ → ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hI : ∀ t ∈ s, I t ≠ 0) :
    presentValue (fun t => D t / I t) s (fun t => I t * c t) = presentValue D s c := by
  unfold presentValue
  apply Finset.sum_congr rfl
  intro t ht
  have h : I t ≠ 0 := hI t ht
  field_simp

/-- **Constant inflation and the Fisher relation.** With constant inflation `π` (`1 + π ≠ 0`),
nominal flows `(1 + π)ᵗ c t` discounted at the nominal rate `i` with `1 + i = (1 + r)(1 + π)` have
the same present value as the real flows `c t` discounted at the real rate `r`. -/
theorem presentValue_nominal_eq_real_const {r π : ℝ} (hπ : 1 + π ≠ 0) (s : Finset ℕ)
    (c : ℕ → ℝ) :
    presentValue (discountFactor ((1 + r) * (1 + π) - 1)) s (fun t => (1 + π) ^ t * c t) =
      presentValue (discountFactor r) s c := by
  have hI : ∀ t ∈ s, (1 + π) ^ t ≠ 0 := fun t _ => pow_ne_zero t hπ
  have hDF : ∀ t ∈ s,
      discountFactor ((1 + r) * (1 + π) - 1) t = discountFactor r t / (1 + π) ^ t := by
    intro t _
    unfold discountFactor
    have h1 : (1 : ℝ) + ((1 + r) * (1 + π) - 1) = (1 + r) * (1 + π) := by ring
    rw [h1, mul_pow, mul_inv, div_eq_mul_inv]
  have hPV : presentValue (discountFactor ((1 + r) * (1 + π) - 1)) s
        (fun t => (1 + π) ^ t * c t) =
      presentValue (fun t => discountFactor r t / (1 + π) ^ t) s
        (fun t => (1 + π) ^ t * c t) := by
    unfold presentValue
    apply Finset.sum_congr rfl
    intro t ht
    rw [hDF t ht]
  rw [hPV]
  exact presentValue_nominal_eq_real (discountFactor r) (fun t => (1 + π) ^ t) s c hI

end MathlibExt.Economics.Finance.RealNominal
