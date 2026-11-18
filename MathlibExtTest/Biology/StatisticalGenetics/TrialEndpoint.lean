/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-! Tests: truncation at horizon `5`. -/

namespace MathlibExtTest.Biology.StatisticalGenetics.TrialEndpoint

open MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-- Event at `7` is truncated at horizon `5`. -/
example : min (7:ℝ) 5 ≠ 7 := truncation_changes_value (T := (7:ℝ)) (h := (5:ℝ)) (by exact_mod_cast (by decide : (5:ℕ) < 7))

/-- Event at `3` is unchanged at horizon `5`. -/
example : min (3:ℝ) 5 = 3 := truncation_identity_inside (T := (3:ℝ)) (h := (5:ℝ)) (by exact_mod_cast (by decide : (3:ℕ) ≤ 5))

end MathlibExtTest.Biology.StatisticalGenetics.TrialEndpoint
