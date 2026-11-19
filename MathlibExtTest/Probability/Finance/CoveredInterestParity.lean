/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.CoveredInterestParity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.CoveredInterestParity` -/

namespace MathlibExtTest.CoveredInterestParity

open MathlibExt.Probability.Finance.CoveredInterestParity
open MathlibExt.Probability.Finance.StatePriceVector
open MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

example : convertedForeignPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ =
    domesticDepositPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ :=
  coveredInterestParity_example

example : (⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ : CoveredInterestMarket).forward =
    (6 / 5) * (21 / 20) / (51 / 50) := by
  change (21 / 17 : ℝ) = 6 / 5 * (21 / 20) / (51 / 50)
  have h := (coveredInterestParity_iff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩
    (by norm_num) (by norm_num)).mp coveredInterestParity_example
  change (21 / 17 : ℝ) = 6 / 5 * (21 / 20) / (51 / 50) at h
  exact h

example : convertedForeignPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ =
    domesticDepositPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ := by
  apply (coveredInterestParity_iff _ (by norm_num) (by norm_num)).mpr
  norm_num

/-- The no-arbitrage premise is satisfiable: the parity instance, with a single
state in which the terminal spot rate is the forward rate `21/17` and funding at
the domestic gross return `21/20`, admits no arbitrage on funded gains. The
pricing probability `1` on that state gives every funded gain zero expectation. -/
private theorem parity_noFundedArbitrage :
    NoFundedArbitrage (assetPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ fun _ : Unit => 21 / 17)
      (assetPrice ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩) (21 / 20) := by
  refine (one_period_fundamental_theorem_asset_pricing_general fun a ω =>
    assetPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ (fun _ : Unit => 21 / 17) a ω -
      21 / 20 * assetPrice ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ a).mpr
    ⟨fun _ => 1, fun _ => one_pos, by simp, fun a => ?_⟩
  fin_cases a <;> simp [assetPayoff, assetPrice]
  norm_num

/-- Under that premise the theorem recovers the parity forward rate. -/
example : (⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ : CoveredInterestMarket).forward =
    (6 / 5) * (21 / 20) / (51 / 50) :=
  forward_eq_of_noFundedArbitrage _ _ (21 / 20) (by norm_num) (by norm_num)
    parity_noFundedArbitrage

example : convertedForeignPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ =
    domesticDepositPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ :=
  coveredInterestParity_of_noFundedArbitrage _ _ (21 / 20) (by norm_num) (by norm_num)
    parity_noFundedArbitrage

/-- An off-parity forward rate is an arbitrage: with
`spot = foreignGross = domesticGross = 1` and `forward = 2`, no terminal spot
rate and no funding rate make the market free of arbitrage. -/
example {Ω : Type*} [Fintype Ω] [Nonempty Ω] (ST : Ω → ℝ) (R : ℝ) (hR : 0 < R) :
    ¬ NoFundedArbitrage (assetPayoff ⟨1, 2, 1, 1⟩ ST) (assetPrice ⟨1, 2, 1, 1⟩) R :=
  fun hNA => by
    have h := forward_mul_foreignGross_eq_of_noFundedArbitrage _ ST R hR hNA
    norm_num at h

end MathlibExtTest.CoveredInterestParity
