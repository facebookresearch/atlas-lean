/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Finite dividend-discount identity

If prices satisfy the one-period recursion `P t = (D (t + 1) + P (t + 1)) / (1 + r)`,
then today's price is the present value of the next `n` dividends plus the discounted
terminal price. Present values and discount factors are those of
`MathlibExt.Economics.Finance.DatedCashFlow`.

## Main results

* `MathlibExt.Economics.Finance.FiniteDividendDiscount.finiteDividendDiscount`: the finite identity.

## References

OpenStax, *Principles of Finance* (stock valuation / dividend discount model).
Atlas roadmap target FI14.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.FiniteDividendDiscount


open MathlibExt.Economics.Finance

/-- **Finite dividend-discount identity.** If prices satisfy the one-period recursion
`P t = (D (t+1) + P (t+1)) / (1 + r)` (source clause: "price = discounted next dividend
plus next price"), then today's price is the present value of the next `n` dividends plus
the discounted terminal price `P n`. `D t` is the dividend at date `t`; only `D t` for
`t ≥ 1` enter (the `Finset.Icc 1 n` sum). At `n = 0` both sides are `P 0`. -/
theorem finiteDividendDiscount {r : ℝ} (hr : 1 + r ≠ 0) {D P : ℕ → ℝ}
    (hrec : ∀ t, P t = (D (t + 1) + P (t + 1)) / (1 + r)) (n : ℕ) :
    P 0 = presentValue (discountFactor r) (Finset.Icc 1 n) D +
      discountFactor r n * P n := by
  -- `hr` is unused: the identity holds unconditionally (even at `r = -1`).
  have _hr := hr
  induction n with
  | zero =>
    simp [presentValue, discountFactor]
  | succ n ih =>
    have hle : 1 ≤ n + 1 := by omega
    have hsum : presentValue (discountFactor r) (Finset.Icc 1 (n + 1)) D
        = presentValue (discountFactor r) (Finset.Icc 1 n) D
          + discountFactor r (n + 1) * D (n + 1) := by
      simp only [presentValue]
      rw [Finset.sum_Icc_succ_top hle]
    have hdf : discountFactor r n / (1 + r) = discountFactor r (n + 1) := by
      simp only [discountFactor, pow_succ, mul_inv, div_eq_mul_inv]
    have hstep : discountFactor r n * P n
        = discountFactor r (n + 1) * D (n + 1)
          + discountFactor r (n + 1) * P (n + 1) := by
      rw [hrec n, ← hdf, ← mul_add, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [hsum, ih, hstep, add_assoc]


end MathlibExt.Economics.Finance.FiniteDividendDiscount
