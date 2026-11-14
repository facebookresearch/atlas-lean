/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.PRAM
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: the pointer-jumping program for
`ptr i = i + 1` and `2` processors maps memory `id` at cell
`0` to `2` after one CRCW step. -/
example : stepCRCW (fun i => i + 1)
    (pointerJumpStep (fun i => i + 1) 2) 0 = 2 := by
  rw [pointerJump_apply]
  norm_num
