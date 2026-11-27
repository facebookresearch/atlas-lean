/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.RpowLowerBound

open MetaMathlibExt Real

-- The endpoint gives a strict inequality even though Γ(2) = 1.
example : (exp 1)⁻¹ < 1 := by
  simpa [Gamma_add_one one_ne_zero] using div_exp_one_rpow_lt_Gamma_add_one (x := 1) le_rfl

-- At x = e the base of the real power equals one.
example : 1 < Gamma (exp 1 + 1) := by
  simpa [div_self (exp_pos 1).ne'] using div_exp_one_rpow_lt_Gamma_add_one (one_le_exp zero_le_one)
