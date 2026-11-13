/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Portfolio log return is not the weighted average of component log returns

The portfolio gross return is the weight-weighted sum of the component gross
returns, but taking logs does not commute with averaging. The explicit
two-asset counterexample below has equal weights `1/2, 1/2` on gross returns
`2` and `1/2`: the portfolio gross return is `5/4`, whose log return
`log (5/4) > 0`, while the weighted average of the component log returns is
`(log 2 + log (1/2)) / 2 = 0`.

## Main results

* `portfolioGrossReturn`: weight-weighted sum of component gross returns.
* `logReturn`: log of a gross return.
* `portfolio_logReturn_ne_weightedAverage_logReturns`: the counterexample.

Atlas roadmap target FI05.T04.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.PortfolioLogReturn

/-- Portfolio gross return: the weight-weighted sum of the component gross
returns (source clause: "portfolio gross return is the weighted average of
component gross returns"). -/
noncomputable def portfolioGrossReturn (w₁ w₂ G₁ G₂ : ℝ) : ℝ := w₁ * G₁ + w₂ * G₂

/-- Log return of a (positive) gross return: `log G`
(source clause: "log return is the log of the gross return"). -/
noncomputable def logReturn (G : ℝ) : ℝ := Real.log G

/-- **Portfolio log return is not the weighted average of component log
returns.** Explicit two-asset counterexample (Atlas roadmap FI05.T04): equal
weights `1/2, 1/2` on gross returns `2` and `1/2` give portfolio gross return
`5/4`, whose log return `log (5/4) > 0`, while the weighted average of the
component log returns is `(log 2 + log (1/2)) / 2 = 0`. -/
theorem portfolio_logReturn_ne_weightedAverage_logReturns :
    logReturn (portfolioGrossReturn (1 / 2) (1 / 2) 2 (1 / 2)) ≠
      (1 / 2) * logReturn 2 + (1 / 2) * logReturn (1 / 2) := by
  have hLHS : logReturn (portfolioGrossReturn (1 / 2) (1 / 2) 2 (1 / 2))
      = Real.log (5 / 4) := by
    unfold logReturn portfolioGrossReturn
    congr 1
    norm_num
  have hpos : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h2, Real.log_inv]
  have hRHS : (1 / 2) * logReturn 2 + (1 / 2) * logReturn (1 / 2) = 0 := by
    unfold logReturn
    rw [hlog]
    ring
  rw [hLHS, hRHS]
  exact ne_of_gt hpos

end MathlibExt.Probability.Finance.PortfolioLogReturn
