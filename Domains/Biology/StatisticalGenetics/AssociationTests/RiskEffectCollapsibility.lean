/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Collapsibility of constant risk differences and risk ratios

A common-weight mixture preserves a constant additive or multiplicative relation between
stratum risks.
-/

public section

namespace WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted

/-- **Constant risk differences and risk ratios collapse** (Greenland, Robins and Pearl 1999,
pp. 37–38). Let `q ∈ [0, 1]` be `P(Z = 1)`, let `r x z` be the risk of response given `X = x`
and `Z = z`, and let `m x = q r(x, 1) + (1 - q) r(x, 0)` be the marginal risk (the mixture that
holds when `X` is independent of `Z`). If `r(1, z) - r(0, z) = δ` for both `z`, then
`m 1 - m 0 = δ`; if `r(1, z) = ρ r(0, z)` for both `z`, then `m 1 = ρ m 0`.

Source: Greenland, Robins and Pearl (1999), pp. 37–38, Table 1. -/
public theorem riskDifference_riskRatio_collapse (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (r : Bool → Bool → ℝ) (δ ρ : ℝ) :
    ((∀ z, r true z - r false z = δ) →
        (q * r true true + (1 - q) * r true false) -
          (q * r false true + (1 - q) * r false false) = δ) ∧
      ((∀ z, r true z = ρ * r false z) →
        q * r true true + (1 - q) * r true false =
          ρ * (q * r false true + (1 - q) * r false false)) := by
  -- The bounds describe a mixture weight; the algebraic identities hold without them.
  have _hq : 0 ≤ q ∧ q ≤ 1 := ⟨hq₀, hq₁⟩
  constructor
  · intro h
    linear_combination q * h true + (1 - q) * h false
  · intro h
    rw [h true, h false]
    ring

end WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted
