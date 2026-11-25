/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.PolakSchrijver
import Mathlib.Tactic.NormNum

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

/-- Package the construction as a length-five cycle code with its exact cardinality. -/
example : ∃ C : CycleCode 7 5, C.1.card = 367 := by
  obtain ⟨A, hA, hcard⟩ := polakSchrijverLowerBound
  exact ⟨⟨A, hA⟩, hcard⟩

/-- The strict decimal estimate printed alongside the exact fifth-root bound. -/
example : ENNReal.ofReal 3.2578 < shannonCapacityCycle 7 := by
  apply lt_of_lt_of_le _ polakSchrijverRateLowerBound
  apply (ENNReal.lt_rpow_inv_iff (by norm_num : (0 : ℝ) < 5)).2
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
  apply (ENNReal.ofReal_lt_natCast (n := 367) (by decide)).2
  norm_num
