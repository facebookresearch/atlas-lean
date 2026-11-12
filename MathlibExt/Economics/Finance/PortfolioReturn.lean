/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# One-period portfolio return as a weighted average of asset returns

Holdings `h i` with prices `P₀ i → P₁ i` over the asset set `s` give initial
wealth `W₀ = ∑ h i * P₀ i` and portfolio return `(W₁ - W₀) / W₀`, with the
initial-value weights `portfolioWeight (h i) (P₀ i) W₀ = h i * P₀ i / W₀`.
The portfolio is fully invested: the weights sum to one when `W₀ ≠ 0`
(`sum_portfolioWeight_eq_one`), encoding the self-financing (no external cash
flow) condition. The portfolio return is then the initial-value-weighted
average of the asset returns (`portfolioReturn_eq_weighted`), via
`Finset.sum_div`, `Finset.sum_congr` and `Finset.sum_sub_distrib`. Future
unification: with the FI05.T01 `grossReturn`,
`assetReturn P₀ P₁ = grossReturn P₀ P₁ - 1` whenever `P₀ ≠ 0` (at `P₀ = 0`
the two sides are `0` and `-1`).

## Main results

* `MathlibExt.Economics.Finance.PortfolioReturn.sum_portfolioWeight_eq_one`
* `MathlibExt.Economics.Finance.PortfolioReturn.portfolioReturn_eq_weighted`

## References

OpenStax, *Principles of Finance*, portfolio returns. Atlas roadmap target
FI05.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.PortfolioReturn

/-- One-period asset return from initial price `P₀` to terminal price `P₁`. -/
noncomputable def assetReturn (P₀ P₁ : ℝ) : ℝ := (P₁ - P₀) / P₀

/-- Initial-value weight of a holding `h` with initial price `P₀` in a portfolio
with initial wealth `W₀`: the share of initial wealth held in this asset. -/
noncomputable def portfolioWeight (h P₀ W₀ : ℝ) : ℝ := h * P₀ / W₀

/-- One-period portfolio return of holdings `h i` with prices `P₀ i → P₁ i` over
the asset set `s`: `(W₁ - W₀) / W₀` with `W₀ = ∑ h i * P₀ i`, `W₁ = ∑ h i * P₁ i`. -/
noncomputable def portfolioReturn {ι : Type*} (h P₀ P₁ : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ i ∈ s, h i * P₁ i - ∑ i ∈ s, h i * P₀ i) / ∑ i ∈ s, h i * P₀ i

/-- **The initial-value weights sum to one** when initial wealth is nonzero:
the portfolio is fully invested. -/
theorem sum_portfolioWeight_eq_one {ι : Type*} {s : Finset ι} {h P₀ : ι → ℝ}
    (hW₀ : ∑ i ∈ s, h i * P₀ i ≠ 0) :
    ∑ i ∈ s, portfolioWeight (h i) (P₀ i) (∑ j ∈ s, h j * P₀ j) = 1 := by
  unfold portfolioWeight
  rw [← Finset.sum_div]
  exact div_self hW₀

/-- **A self-financing one-period portfolio return is the initial-value-weighted
average of the asset returns** when initial wealth is nonzero (and every initial
price is nonzero, so each asset return is defined). -/
theorem portfolioReturn_eq_weighted {ι : Type*} {s : Finset ι} {h P₀ P₁ : ι → ℝ}
    (hP₀ : ∀ i ∈ s, P₀ i ≠ 0) (hW₀ : ∑ i ∈ s, h i * P₀ i ≠ 0) :
    portfolioReturn h P₀ P₁ s =
      ∑ i ∈ s, portfolioWeight (h i) (P₀ i) (∑ j ∈ s, h j * P₀ j) *
        assetReturn (P₀ i) (P₁ i) := by
  unfold portfolioReturn portfolioWeight assetReturn
  have hterm : ∀ i ∈ s, h i * P₀ i / (∑ j ∈ s, h j * P₀ j) * ((P₁ i - P₀ i) / P₀ i)
      = (h i * P₁ i - h i * P₀ i) / (∑ j ∈ s, h j * P₀ j) := by
    intro i hi
    have hi0 : P₀ i ≠ 0 := hP₀ i hi
    field_simp
  have hsum : (∑ i ∈ s, h i * P₀ i / (∑ j ∈ s, h j * P₀ j) * ((P₁ i - P₀ i) / P₀ i))
      = ∑ i ∈ s, (h i * P₁ i - h i * P₀ i) / (∑ j ∈ s, h j * P₀ j) :=
    Finset.sum_congr rfl hterm
  rw [hsum, ← Finset.sum_div, Finset.sum_sub_distrib]

end MathlibExt.Economics.Finance.PortfolioReturn
