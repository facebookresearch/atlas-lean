/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.Geometry.BoseGases
import Mathlib.Tactic.NormNum

open MathlibExt.Geometry.BoseGasesWanted.BoseGases

example : η = (1 : ℝ) / 1615 := rfl

example : 0 < η := by
  norm_num [η]
