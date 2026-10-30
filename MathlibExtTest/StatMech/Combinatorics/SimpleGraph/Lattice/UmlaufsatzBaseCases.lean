/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases`

* `umBase_square_turning`, `umBase_domino_turning`: total turning angle `-2π`.
* `umBase_totalTurnAngle_eq` on the unit cell, giving total turn `-4`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases

example : totalTurnAngle unitCell ucDart0 4 = -(2 * Real.pi) := umBase_square_turning

example : totalTurnAngle domino dmD0 6 = -(2 * Real.pi) := umBase_domino_turning

example : (totalTurnZ unitCell ucDart0 4 : ℝ) = -4 := by
  have h := umBase_totalTurnAngle_eq unitCell ucDart0 4
  rw [umBase_square_turning] at h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h
  linarith

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzBaseCases
