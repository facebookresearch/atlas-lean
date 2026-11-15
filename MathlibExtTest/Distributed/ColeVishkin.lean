/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.ColeVishkin
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: one CV step separates the first two nodes of
the color path `0, 1, 2`. -/
example : cvColor 0 1 (by norm_num) ≠ cvColor 1 2 (by norm_num) :=
  cvColor_proper 0 1 2 (by norm_num) (by norm_num)

/-- Boundary check: colors below `2 ^ 2` step to colors below
`2 * 2`. -/
example : cvColor 2 3 (by norm_num) < 2 * 2 :=
  cvColor_lt 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
