/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.FiniteBoxFlowUniqueness

/-! Tests: constant solutions of the zero field agree. -/

namespace MathlibExtTest.Analysis.ODE.FiniteBoxFlowUniqueness

open MathlibExt.Analysis.ODE.FiniteBoxFlowUniqueness

/-- Constant zero-field solutions from the same start agree on `[0, 1]`. -/
example : Set.EqOn (fun _ : ℝ => (0:ℝ)) (fun _ : ℝ => (0:ℝ)) (Set.Icc 0 1) :=
  forward_unique_eqOn (F := fun _ : ℝ => (0:ℝ)) (K := 0)
    (by intro x y; simp [LipschitzWith, dist_eq_norm])
    continuousOn_const continuousOn_const
    (fun t _ => hasDerivWithinAt_const t (Set.Ici t) 0)
    (fun t _ => hasDerivWithinAt_const t (Set.Ici t) 0) rfl

end MathlibExtTest.Analysis.ODE.FiniteBoxFlowUniqueness
