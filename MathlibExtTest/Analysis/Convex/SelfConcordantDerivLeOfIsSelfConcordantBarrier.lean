/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.SelfConcordantDerivLeOfIsSelfConcordantBarrier
import MathlibExt.Analysis.Convex.SelfConcordant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.NormNum

/-!
# Tests for semiboundedness of a self-concordant barrier

The bound `DF(x)[y - x] ≤ ϑ` holds with equality for `-log` on `(0, ∞)` at `x = 1`, `y = 0`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Convex.SelfConcordantDerivLeOfIsSelfConcordantBarrier

open Set
open MathlibExt.Analysis.Convex.SelfConcordant (isSelfConcordantBarrier_neg_log)
open WantedExt.Analysis.Convex.SelfConcordantWanted (deriv_le_of_isSelfConcordantBarrier)

/-- The barrier bound for `-log` at `x = 1`, `y = 0`. -/
example : deriv (fun t : ℝ => -Real.log ((1 : ℝ) + t • ((0 : ℝ) - 1))) 0 ≤ (1 : ℝ) :=
  deriv_le_of_isSelfConcordantBarrier (E := ℝ) (F := fun x : ℝ => -Real.log x)
    (Q := Ioi (0 : ℝ)) (ϑ := (1 : ℝ)) isSelfConcordantBarrier_neg_log (x := (1 : ℝ))
    (y := (0 : ℝ)) (by norm_num) (by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl)

/-- The bound above is tight: the derivative equals `1`. -/
example : deriv (fun t : ℝ => -Real.log (1 + t * (0 - 1))) 0 = 1 := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (1 : ℝ) + s * (0 - 1)) (0 - 1) t := by
    intro t
    simpa using ((hasDerivAt_id t).mul_const (0 - 1 : ℝ)).const_add (1 : ℝ)
  have hlog : HasDerivAt (fun t : ℝ => -Real.log (1 + t * (0 - 1)))
      (-((0 - 1) / (1 + 0 * (0 - 1)))) 0 :=
    ((hu 0).log (by norm_num)).neg
  have hderiv := hlog.deriv
  simpa using hderiv

end MathlibExtTest.Analysis.Convex.SelfConcordantDerivLeOfIsSelfConcordantBarrier
