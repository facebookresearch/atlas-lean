/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# Funded-gains fundamental theorem of asset pricing

Embed the funded gains `g a ω = X a ω - R * p a` (payoff minus
gross-risk-free-return times price) in the existing gain-form FTAP: the funded
gains admit no arbitrage iff there is a strictly positive normalized `q` with
`E_q[X a] = R * p a` for every asset. This does not reprove the FTAP; it
applies `one_period_fundamental_theorem_asset_pricing_general` and rewrites
`∑ ω, q ω * (X a ω - R * p a) = 0` as `∑ ω, q ω * X a ω = R * p a` using
`∑ ω, q ω = 1`.

## Main results

* `funded_ftap`: the funded-gains FTAP.

Atlas roadmap target FI08.T01.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.FundedFTAP

open MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

/-- **Funded-gains FTAP.** Embed the funded gains `g a ω = X a ω - R * p a`
(payoff minus gross-risk-free-return times price) in the existing gain-form
FTAP: the funded gains admit no arbitrage iff there is a strictly positive
normalized `q` with `E_q[X a] = R * p a` for every asset (Atlas roadmap
FI08.T01). This does NOT reprove the FTAP; it applies
`one_period_fundamental_theorem_asset_pricing_general` to `g` and rewrites
`∑ ω, q ω * (X a ω - R * p a) = 0` as `∑ ω, q ω * X a ω = R * p a` using
`∑ ω, q ω = 1`. No sign hypothesis on `R` is needed: the equivalence is pure
algebra plus the FTAP. -/
theorem funded_ftap {Ω : Type*} [Fintype Ω] [Nonempty Ω] {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) :
    (¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * (X a ω - R * p a)) ∧
      (∃ ω : Ω, 0 < ∑ a : A, h a * (X a ω - R * p a))) ↔
    ∃ q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
      (∀ a : A, ∑ ω : Ω, q ω * X a ω = R * p a) := by
  have hFTAP := one_period_fundamental_theorem_asset_pricing_general
    (Ω := Ω) (A := A) (fun a ω => X a ω - R * p a)
  have key : ∀ q : Ω → ℝ, ∑ ω : Ω, q ω = 1 → ∀ a : A,
      (∑ ω : Ω, q ω * (X a ω - R * p a) = 0) ↔
        (∑ ω : Ω, q ω * X a ω = R * p a) := by
    intro q hqsum a
    have hdecomp : ∑ ω : Ω, q ω * (X a ω - R * p a)
        = (∑ ω : Ω, q ω * X a ω) - R * p a := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_mul, hqsum, one_mul]
    rw [hdecomp, sub_eq_zero]
  constructor
  · intro hNA
    obtain ⟨q, hqpos, hqsum, hq⟩ := hFTAP.mp hNA
    exact ⟨q, hqpos, hqsum, fun a => (key q hqsum a).mp (hq a)⟩
  · rintro ⟨q, hqpos, hqsum, hq⟩
    apply hFTAP.mpr
    exact ⟨q, hqpos, hqsum, fun a => (key q hqsum a).mpr (hq a)⟩

end MathlibExt.Probability.Finance.FundedFTAP
