/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PWMPrimitiveBound

@[expose] public section

open MathlibExt.Analysis.ODE.PWMPrimitiveBound

namespace MathlibExtTest.Analysis.ODE.PWMPrimitiveBound

/-- The half-duty primitive at half period is exactly `1/4`. -/
example : pwmPrimitive 1 (fun _ => 1 / 2) (1 / 2) = 1 / 4 :=
  pwmPrimitive_half_half

/-- Duty `2` (outside `[0, 1]`) gives primitive `-t`, breaking the envelope. -/
example (ε t : ℝ) (hε : 0 < ε) : pwmPrimitive ε (fun _ => 2) t = -t :=
  pwmPrimitive_two ε t hε

end MathlibExtTest.Analysis.ODE.PWMPrimitiveBound
