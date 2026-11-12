/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.CoveredInterestParity
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.CoveredInterestParity` -/

namespace MathlibExtTest.CoveredInterestParity

open MathlibExt.Probability.Finance.CoveredInterestParity

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

end MathlibExtTest.CoveredInterestParity
