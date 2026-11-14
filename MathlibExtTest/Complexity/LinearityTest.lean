/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.LinearityTest

@[expose] public section

/-- Boundary check: the zero linear function over
`Fin 2 → ZMod 2` passes the BLR test with probability `1`. -/
example : acceptProb (linFun (0 : Fin 2 → ZMod 2)) = 1 :=
  blr_complete _

/-- Boundary check: the zero function disagrees with itself
with probability `0`. -/
example : disagreeProb (0 : (Fin 2 → ZMod 2) → ZMod 2)
    (linFun (0 : Fin 2 → ZMod 2)) = 0 := by
  unfold disagreeProb linFun
  simp
