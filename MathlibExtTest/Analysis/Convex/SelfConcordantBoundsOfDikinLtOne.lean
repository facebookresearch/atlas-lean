/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import MathlibExt.Analysis.Convex.SelfConcordantBoundsOfDikinLtOne

open Filter Set
open scoped Topology
open MathlibExt.Analysis.Convex.SelfConcordant (IsSelfConcordant)
open WantedExt.Analysis.Convex.SelfConcordantWanted (bounds_of_dikin_lt_one)

namespace MathlibExtTest.Analysis.Convex.SelfConcordantBoundsOfDikinLtOne

/-- For `r = |h|_x < 1`, `ρ(-r) ≤ ρ(r)` with `ρ(s) = -log (1 - s) - s`. -/
theorem rho_neg_le_rho {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} (hF : IsSelfConcordant F Q) {x h : E}
    (hx : x ∈ Q) (hr : √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) < 1) :
    -Real.log (1 + √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) +
        √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) ≤
      -Real.log (1 - √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) -
        √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) := by
  have h := @bounds_of_dikin_lt_one E _ _ _ F Q hF x h hx hr
  have hle := le_trans h.1 h.2
  linarith [hle]

end MathlibExtTest.Analysis.Convex.SelfConcordantBoundsOfDikinLtOne
