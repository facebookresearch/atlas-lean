/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.FiniteDividendDiscount
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Tactic

/-!
# Infinite dividend-discount identity

The limit passage from the finite dividend-discount identity (FI14.T01): under a
vanishing discounted terminal-value (no-bubble) condition and nonnegative dividends,
the infinite sum of discounted dividends equals today's price. The unconditional
form discharges the finite identity with FI14.T01's theorem; this file is stacked
on the FI14.T01 PR.

## Main results

* `MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendTerm`: discounted
  dividend at date `t + 1`.
* `MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendDiscountInfinite_of_finite`:
  the limit passage.
* `MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendDiscountInfinite`: the
  unconditional identity.

## References

OpenStax, *Principles of Finance* (stock valuation / dividend discount model).
Atlas roadmap target FI14.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.InfiniteDividendDiscount

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.FiniteDividendDiscount

noncomputable def dividendTerm (r : ℝ) (D : ℕ → ℝ) (t : ℕ) : ℝ :=
  discountFactor r (t + 1) * D (t + 1)

private theorem sum_range_dividendTerm_eq_presentValue {r : ℝ} {D : ℕ → ℝ} (n : ℕ) :
    ∑ i ∈ Finset.range n, dividendTerm r D i
      = presentValue (discountFactor r) (Finset.Icc 1 n) D := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_Icc] at hx
    omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold presentValue dividendTerm
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- **Infinite dividend-discount identity.** If the finite identity holds for every `n`
(proved for the one-period recursion in FI14.T01), the discounted terminal price vanishes
(source clause: "no-bubble / vanishing discounted terminal-value condition"), and dividends
are nonnegative, then the infinite sum of discounted dividends equals today's price.
The finite identity is taken as a hypothesis so this theorem is exactly the limit passage;
combined with FI14.T01 it gives the unconditional infinite dividend-discount model. -/
theorem dividendDiscountInfinite_of_finite {r : ℝ} (hr : 0 < 1 + r) {D P : ℕ → ℝ}
    (hfinite : ∀ n, P 0 = presentValue (discountFactor r) (Finset.Icc 1 n) D +
      discountFactor r n * P n)
    (hvanish : Filter.Tendsto (fun n => discountFactor r n * P n) Filter.atTop (nhds 0))
    (hnn : ∀ t, 0 ≤ D (t + 1)) :
    HasSum (dividendTerm r D) (P 0) := by
  have hnonneg : ∀ i, 0 ≤ dividendTerm r D i := by
    intro i
    unfold dividendTerm discountFactor
    apply mul_nonneg _ (hnn i)
    rw [inv_nonneg]
    exact pow_nonneg (le_of_lt hr) _
  have hpart : ∀ n, ∑ i ∈ Finset.range n, dividendTerm r D i
      = P 0 - discountFactor r n * P n := by
    intro n
    rw [sum_range_dividendTerm_eq_presentValue]
    have h := hfinite n
    linarith
  have hlim : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, dividendTerm r D i)
      Filter.atTop (nhds (P 0)) := by
    have heq : (fun n => ∑ i ∈ Finset.range n, dividendTerm r D i)
        = (fun n => P 0 - discountFactor r n * P n) := funext hpart
    rw [heq]
    have h := tendsto_const_nhds (x := P 0) (f := Filter.atTop) |>.sub hvanish
    simpa using h
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg (P 0)).mpr hlim

theorem dividendDiscountInfinite {r : ℝ} (hr : 0 < 1 + r) {D P : ℕ → ℝ}
    (hrec : ∀ t, P t = (D (t + 1) + P (t + 1)) / (1 + r))
    (hvanish : Filter.Tendsto (fun n => discountFactor r n * P n) Filter.atTop (nhds 0))
    (hnn : ∀ t, 0 ≤ D (t + 1)) :
    HasSum (dividendTerm r D) (P 0) := by
  exact dividendDiscountInfinite_of_finite hr
    (fun n => finiteDividendDiscount (ne_of_gt hr) hrec n) hvanish hnn


end MathlibExt.Economics.Finance.InfiniteDividendDiscount
