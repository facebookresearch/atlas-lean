/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchParityInterpolation
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.BridgeTorchGeneralizations

-- The first even term uses index zero, and the odd term at five uses index two.
example (a : ℕ → ℝ) (heven : ∀ m : ℕ, a (2 * m) = m)
    (hodd : ∀ m : ℕ, a (2 * m + 1) = -((m : ℝ) + 1)) : a 0 = 0 ∧ a 5 = -3 := by
  have h := parity_interpolation (fun m => (m : ℝ)) (fun m => -((m : ℝ) + 1)) a heven hodd
  constructor
  · simpa using h 0
  · have h₅ := h 5
    norm_num at h₅
    exact h₅

end MetaMathlibExt.BridgeTorchGeneralizations
