/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalInstrumentation.SampledState

/-! Tests: identity output is observable; a zero output is not, even
with dynamics (samples of a noninjective instantaneous `H`). -/

namespace PhyslibExtTest.BiomedicalInstrumentation.SampledState

open PhyslibExt.BiomedicalInstrumentation.SampledState
open scoped Matrix

/-- `H = 1`, `A = 0`, one sample: observable (exp 0 = 1). -/
example (t : Fin 1 → ℝ) :
    Function.Injective
      (sampledMap (n := 2) (m := 1) (k := 2) (0 : Matrix (Fin 2) (Fin 2) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) t) := by
  rw [sampled_injective_iff]
  intro x hx
  have h0 := hx 0
  simpa only [smul_zero, NormedSpace.exp_zero, Matrix.one_mulVec] using h0

/-- `H = 0`: not observable. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (t : Fin 1 → ℝ) :
    ¬ Function.Injective
      (sampledMap (k := 2) A (0 : Matrix (Fin 2) (Fin 2) ℝ) t) :=
  (sampled_injective_iff (n := 2) (m := 1) (k := 2) A (0 : Matrix (Fin 2) (Fin 2) ℝ) t).not.mpr
    (fun h => by
      have h0 := h (fun _ => 1) (fun j => by simp)
      exact one_ne_zero (congrFun h0 0))

end PhyslibExtTest.BiomedicalInstrumentation.SampledState
