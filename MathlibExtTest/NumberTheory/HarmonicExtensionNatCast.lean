/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HarmonicExtensionNatCast
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The empty sum is included in the natural-input formula.
example : harmonicExtension (0 : ℕ) = 0 := by
  rw [harmonicExtension_natCast]
  simp

-- At a positive input, the geometric sum gives the first three reciprocals.
example : harmonicExtension (3 : ℕ) = (11 : ℝ) / 6 := by
  rw [harmonicExtension_natCast]
  norm_num [harmonic_succ]
