/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ForwardLinear

/-! Tests: the zero operator with zero forcing has the constant forward trajectory. -/

namespace MathlibExtTest.Analysis.ODE.ForwardLinear

open MathlibExt.Analysis.ODE.ForwardLinear

/-- Constant trajectories agree with the Duhamel trajectory for zero data. -/
example : Set.EqOn (fun _ : ℝ => (0:ℝ)) (fun t => (NormedSpace.exp (t • (0 : ℝ →L[ℝ] ℝ))) 0 +
      ∫ s in (0:ℝ)..t, (NormedSpace.exp ((t - s) • (0 : ℝ →L[ℝ] ℝ))) ((fun _ => (0:ℝ)) s)) (Set.Ici 0) :=
  forward_duhamel_eqOn 0 (by fun_prop) 0 rfl continuousOn_const
    (fun t ht => by simpa using hasDerivWithinAt_const t (Set.Ici t) (0:ℝ))

end MathlibExtTest.Analysis.ODE.ForwardLinear
