/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.StateSpace.SISO
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! Field and output for a system with nonzero input gain and direct feedthrough. -/

open Matrix MathlibExt.Biology.Dynamics.IntegralFeedback

private def system : LinearSystem (Fin 2) where
  A := !![0, 1; -2, 0]
  b := ![1, 3]
  c := ![2, -1]
  d := 4

example : system.field ![2, 1] 3 = ![4, 5] := by
  ext i
  fin_cases i <;> norm_num [LinearSystem.field, system, mulVec, dotProduct, Fin.sum_univ_two]

example : system.output ![2, 1] 3 = 15 := by
  norm_num [LinearSystem.output, system, dotProduct, Fin.sum_univ_two]
