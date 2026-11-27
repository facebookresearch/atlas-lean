/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The stock-flow identity

If a stock evolves by the per-period accounting `K (t + 1) = K t + inflow t - outflow t
+ otherChange t`, where `otherChange t` collects the changes in the stock recorded in period
`t` outside inflows and outflows (revaluations, that is holding gains and losses, together
with other changes in the volume of the stock, such as destruction, discoveries and
reclassifications), then after `n` periods the stock is the initial stock plus cumulative
inflows minus cumulative outflows plus cumulative other changes. This is the reconciliation
of opening and closing stocks in national accounting, where the opening value plus
transactions, other changes in volume, and revaluations gives the closing value; here the
last two categories share the `otherChange` summand. The proof is finite-sum telescoping.

The accounting is only needed for the periods before the horizon `n`, so the identity applies
to finite records and partially specified paths.

## Main results

* `stock_eq_initial_add_flows`: `K n = K 0 + ∑ inflows - ∑ outflows + ∑ other changes`.
* `stockFlow_example`: the concrete stock `K t = 100 + 9 * t` at `n = 2`.

## References

* United Nations, European Commission, IMF, OECD, and World Bank, *System of National Accounts
  2008* (2009), Chapter 12 (the other changes in assets accounts: other changes in the volume
  of assets, and revaluation) and Chapter 13 (the balance sheet).
* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.StockFlow

/-- **Stock-flow identity.** If the stock evolves by the per-period accounting
`K (t + 1) = K t + inflow t - outflow t + otherChange t` in every period `t < n`, where
`otherChange t` collects the changes recorded in period `t` outside inflows and outflows
(revaluations and other changes in volume), then after `n` periods the stock is the initial
stock plus cumulative inflows minus cumulative outflows plus cumulative other changes. This
instantiates finite-sum telescoping (`Finset.sum_range_sub`). -/
theorem stock_eq_initial_add_flows {K inflow outflow otherChange : ℕ → ℝ} (n : ℕ)
    (hflow : ∀ t < n, K (t + 1) = K t + inflow t - outflow t + otherChange t) :
    K n = K 0 + (∑ t ∈ Finset.range n, inflow t) -
      (∑ t ∈ Finset.range n, outflow t) + (∑ t ∈ Finset.range n, otherChange t) := by
  have htele := Finset.sum_range_sub K n
  have hsplit : (∑ t ∈ Finset.range n, (K (t + 1) - K t))
      = (∑ t ∈ Finset.range n, inflow t) - (∑ t ∈ Finset.range n, outflow t)
        + (∑ t ∈ Finset.range n, otherChange t) := by
    have hterm : ∀ t ∈ Finset.range n,
        K (t + 1) - K t = inflow t - outflow t + otherChange t := by
      intro t ht
      rw [hflow t (Finset.mem_range.mp ht)]
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit] at htele
  linarith

/-- Concrete stock: initial stock `100`, growing by `9` per period (`+10` inflow, `-3`
outflow, `+2` other change), so `K t = 100 + 9 * t`. -/
noncomputable def exampleStock : ℕ → ℝ := fun t => 100 + 9 * t

/-- The concrete stock satisfies the stock-flow identity at `n = 2`: `K 2 = 118`.
Prove by applying `stock_eq_initial_add_flows` with constant inflow `10`, outflow `3`,
other change `2`, discharging the per-period accounting by `simp [exampleStock]` and `ring`,
then evaluating the finite sums. -/
theorem stockFlow_example :
    exampleStock 2 = exampleStock 0 + (∑ t ∈ Finset.range 2, (10 : ℝ)) -
      (∑ t ∈ Finset.range 2, (3 : ℝ)) + (∑ t ∈ Finset.range 2, (2 : ℝ)) := by
  have h := stock_eq_initial_add_flows (K := exampleStock)
    (inflow := fun _ => (10 : ℝ)) (outflow := fun _ => (3 : ℝ))
    (otherChange := fun _ => (2 : ℝ)) 2 (fun t _ => by simp [exampleStock]; ring)
  exact h

end MathlibExt.Economics.Macro.StockFlow
