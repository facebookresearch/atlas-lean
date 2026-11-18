/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.TrialEndpoint
import MathlibExt.Probability.Causality.CausalIdentification

/-! Tests: truncation at horizon `5`. -/

namespace MathlibExtTest.Biology.StatisticalGenetics.TrialEndpoint

open MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-- Event at `7` is truncated at horizon `5`. -/
example : truncatedEndpoint (fun _ : Fin 1 => (7:ℝ)) 5 0 ≠ 7 :=
  truncation_changes_value _ 0 (by exact_mod_cast (by decide : (5:ℕ) < 7))

/-- Event at `3` is unchanged at horizon `5` (generic `min_eq_left`). -/
example : truncatedEndpoint (fun _ : Fin 1 => (3:ℝ)) 5 0 = 3 :=
  truncatedEndpoint_eq_of_le _ 5 0 (by exact_mod_cast (by decide : (3:ℕ) ≤ 5))

/-- Unbiasedness for truncated endpoints on three subjects, one treated. -/
example (T0 T1 : Fin 3 → ℝ) :
    MathlibExt.Probability.Causality.randExp 1
        (MathlibExt.Probability.Causality.diffInMeans
          (truncatedEndpoint T0 5) (truncatedEndpoint T1 5)) =
      MathlibExt.Probability.Causality.ate
        (truncatedEndpoint T0 5) (truncatedEndpoint T1 5) :=
  MathlibExt.Probability.Causality.randExp_diffInMeans _ _ (by decide) (by decide)

end MathlibExtTest.Biology.StatisticalGenetics.TrialEndpoint
