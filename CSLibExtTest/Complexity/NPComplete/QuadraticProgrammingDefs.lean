/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : QuadraticProgrammingInstance) :
    quadraticProgrammingDec (bitEncode i) = true ↔
      WellFormed i ∧ QuadraticProgrammingFeasible i := by
  simp [quadraticProgrammingDec, bitDecode_bitEncode]

/-- Maximize `-y² + 2y` in one variable subject to `y ≤ 1/2`, with the bound `B`. -/
private abbrev program (B : RatCode) : QuadraticProgrammingInstance :=
  (1, [([((1, 0), 1)], ((1, 0), 2))], [((0, 1), 1)], [((2, 0), 1)], B)

/-- A lone continuation bit is a truncated instance encoding. -/
example : quadraticProgrammingDec [true] = false := by
  have h : bitDecode (α := QuadraticProgrammingInstance) [true] = none := rfl
  simp [quadraticProgrammingDec, h]

/-- The point `y = 1/2` is feasible and has objective value `3/4`. -/
example : quadraticProgrammingDec (bitEncode (program ((3, 0), 4))) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun _ => 1 / 2, ?_, ?_⟩
  · simp [ratVal]
  · simp [ratVal]
    norm_num

/-- The unconstrained maximum `1` sits at `y = 1`, which violates `y ≤ 1/2`; on the feasible
half-line the objective stays below `1`. -/
example : quadraticProgrammingDec (bitEncode (program ((1, 0), 1))) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, y, hcon, hobj⟩ := (accepts_encoding _).1 hacc
  have hy : y 0 ≤ 1 / 2 := by simpa [ratVal] using hcon
  simp [ratVal] at hobj
  nlinarith

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (program ((1, 0), 1)) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming
