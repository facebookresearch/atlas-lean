/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.PortfolioLogReturn

/-! # Tests for `MathlibExt.Probability.Finance.PortfolioLogReturn` -/

namespace MathlibExtTest.PortfolioLogReturn

open MathlibExt.Probability.Finance.PortfolioLogReturn in
example : 0 < logReturn (portfolioGrossReturn (1 / 2) (1 / 2) 2 (1 / 2)) := by
  have hLHS : logReturn (portfolioGrossReturn (1 / 2) (1 / 2) 2 (1 / 2))
      = Real.log (5 / 4) := by
    unfold logReturn portfolioGrossReturn
    congr 1
    norm_num
  rw [hLHS]
  exact Real.log_pos (by norm_num)

open MathlibExt.Probability.Finance.PortfolioLogReturn in
example : (1 / 2) * logReturn 2 + (1 / 2) * logReturn (1 / 2) = 0 := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h2, Real.log_inv]
  unfold logReturn
  rw [hlog]
  ring

end MathlibExtTest.PortfolioLogReturn
