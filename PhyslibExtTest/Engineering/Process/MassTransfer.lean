/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.MassTransfer
import Mathlib.Tactic.NormNum

/-!
# Tests for interphase mass transfer

Boundary checks for `PhyslibExt.Engineering.Process.MassTransfer` with
`H = 2`, `p = 3`, and `k = a = 1`: absorption below equilibrium, desorption
above it, zero flux at equilibrium, and agreement with the volatility form.
-/

namespace Engineering.Process.MassTransfer.Tests

-- H = 2, p = 3, c = 1, k = a = 1: driving force 5, absorption.
example : interphaseFlux 1 1 2 3 1 = 5 := by
  unfold interphaseFlux
  norm_num

-- c = 7: flux is -1 (desorption), not a nonnegative source.
example : interphaseFlux 1 1 2 3 7 = -1 := by
  unfold interphaseFlux
  norm_num

example : interphaseFlux 1 1 2 3 7 < 0 := by
  unfold interphaseFlux
  norm_num

-- Zero driving force at c = H * p = 6.
example : interphaseFlux 1 1 2 3 6 = 0 := by
  unfold interphaseFlux
  norm_num

-- Volatility form agrees numerically: H = 1 / (1/2) = 2.
example : interphaseFlux 1 1 (1 / (1 / 2 : ℝ)) 3 1 = 5 := by
  unfold interphaseFlux
  norm_num

end Engineering.Process.MassTransfer.Tests
