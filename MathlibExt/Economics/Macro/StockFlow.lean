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
+ valuation t`, where `valuation t` is the valuation change explicitly recorded in period
`t` (capital gains/losses, revaluations, other volume changes; not hidden inside inflows
or outflows), then after `n` periods the stock is the initial stock plus classified
cumulative inflows minus cumulative outflows plus cumulative valuation changes. This is
finite-sum telescoping instantiated locally.

## Main results

* `stock_eq_initial_add_flows`: `K n = K 0 + ∑ inflows - ∑ outflows + ∑ valuation changes`.
* `stockFlow_example`: the concrete stock `K t = 100 + 9 * t` at `n = 2`.

## References

* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.StockFlow

/-- **Stock-flow identity.** If the stock evolves by the per-period accounting
`K (t + 1) = K t + inflow t - outflow t + valuation t`, where `valuation t` is the
valuation change explicitly recorded in period `t` (capital gains/losses, revaluations,
other volume changes; not hidden inside inflows or outflows), then after `n` periods the
stock is the initial stock plus classified cumulative inflows minus cumulative outflows plus
cumulative valuation changes. This instantiates finite-sum telescoping
(`Finset.sum_range_sub`). -/
theorem stock_eq_initial_add_flows {K inflow outflow valuation : ℕ → ℝ}
    (hflow : ∀ t, K (t + 1) = K t + inflow t - outflow t + valuation t) (n : ℕ) :
    K n = K 0 + (∑ t ∈ Finset.range n, inflow t) -
      (∑ t ∈ Finset.range n, outflow t) + (∑ t ∈ Finset.range n, valuation t) := by
  have htele := Finset.sum_range_sub K n
  have hsplit : (∑ t ∈ Finset.range n, (K (t + 1) - K t))
      = (∑ t ∈ Finset.range n, inflow t) - (∑ t ∈ Finset.range n, outflow t)
        + (∑ t ∈ Finset.range n, valuation t) := by
    have hterm : ∀ t ∈ Finset.range n,
        K (t + 1) - K t = inflow t - outflow t + valuation t := by
      intro t _
      rw [hflow t]
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit] at htele
  linarith

/-- Concrete stock: initial stock `100`, growing by `9` per period (`+10` inflow, `-3`
outflow, `+2` valuation change), so `K t = 100 + 9 * t`. -/
noncomputable def exampleStock : ℕ → ℝ := fun t => 100 + 9 * t

/-- The concrete stock satisfies the stock-flow identity at `n = 2`: `K 2 = 118`.
Prove by applying `stock_eq_initial_add_flows` with constant inflow `10`, outflow `3`,
valuation `2`, discharging the per-period accounting by `simp [exampleStock]` and `ring`,
then evaluating the finite sums. -/
theorem stockFlow_example :
    exampleStock 2 = exampleStock 0 + (∑ t ∈ Finset.range 2, (10 : ℝ)) -
      (∑ t ∈ Finset.range 2, (3 : ℝ)) + (∑ t ∈ Finset.range 2, (2 : ℝ)) := by
  have h := stock_eq_initial_add_flows (K := exampleStock)
    (inflow := fun _ => (10 : ℝ)) (outflow := fun _ => (3 : ℝ))
    (valuation := fun _ => (2 : ℝ)) (fun t => by simp [exampleStock]; ring) 2
  exact h

end MathlibExt.Economics.Macro.StockFlow
