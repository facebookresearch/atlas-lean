/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.ControlBridge

import Mathlib.Tactic.NormNum

/-!
# Tests for the CSTR-to-SISO bridge

Boundary checks for `PhyslibExt.Engineering.Process.ControlBridge`: unit
parameters give the scalar field `-x + u` and output `x`, including a
nonzero input; zero input deviation is pure decay; doubling the input
deviation without changing the input vector changes the field; and a
concrete equilibrium pair instantiates the deviation correspondence.
-/

namespace Engineering.Process.ControlBridge.Tests

open Engineering.Process.ControlBridge
open MathlibExt.Biology.Dynamics.IntegralFeedback

-- Unit parameters V = Q = 1, k = 0, C = 1 give lambda = b = C = 1: the
-- field at state 3 with nonzero input 2 is -3 + 2 = -1, output 3.
example :
    (cstrLinearSystem 1 1 0 1).field ![3] 2 = ![-1] ∧
      (cstrLinearSystem 1 1 0 1).output ![3] 2 = 3 := by
  constructor
  · rw [cstrLinearSystem_field_eq]
    norm_num [Matrix.cons_val_zero]
  · rw [cstrLinearSystem_output_eq]
    norm_num [Matrix.cons_val_zero]

-- Zero input deviation: the field is pure decay and the output is the
-- gained state.
example :
    (cstrLinearSystem 1 1 0 2).field ![3] 0 = ![-3] ∧
      (cstrLinearSystem 1 1 0 2).output ![3] 0 = 6 := by
  constructor
  · rw [cstrLinearSystem_field_eq]
    norm_num [Matrix.cons_val_zero]
  · rw [cstrLinearSystem_output_eq]
    norm_num [Matrix.cons_val_zero]

-- The input scale is part of the map: doubling the input deviation
-- without changing the input vector changes the field, so a unit change
-- on the input is not invisible.
example :
    (cstrLinearSystem 1 1 0 1).field ![0] 1 ≠
      (cstrLinearSystem 1 1 0 1).field ![0] 2 := by
  rw [cstrLinearSystem_field_eq, cstrLinearSystem_field_eq]
  norm_num [Matrix.cons_val_zero]

-- A concrete equilibrium pair: V = Q = k = 1 with css = 1 and
-- cinss = 2 is an equilibrium, and deviations x = 3, u = 2 give the
-- mapped field value -(1 + 1) * 3 + 1 * 2 = -4 through the deviation
-- correspondence.
example :
    ![(1 / 1 : ℝ) * ((2 + 2) - (1 + 3)) - 1 * (1 + 3)] =
      (cstrLinearSystem 1 1 1 1).field ![3] 2 := by
  rw [cstrLinearSystem_field_eq]
  norm_num [Matrix.cons_val_zero]

end Engineering.Process.ControlBridge.Tests
