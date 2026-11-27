/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Harmonic.HyperharmonicAsymptotic
import MathlibExt.NumberTheory.Harmonic.ShiftedChoose
import Mathlib.Tactic.NormNum

/-! # Tests for the asymptotics of hyperharmonic numbers -/

open Asymptotics Filter MetaMathlibExt

-- The shared estimate has the quadratic normalization at degree two.
example :
    (fun n : ℕ ↦ ((n + 2).choose 2 : ℝ)) ~[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 / 2 := by
  simpa [Nat.factorial] using isEquivalent_add_choose 2

-- The recursion gives zero at index zero and a nontrivial value at order three.
example : hyperharmonic 3 0 = 0 := by simp [hyperharmonic_succ]

example : hyperharmonic 3 2 = 7 / 2 := by
  norm_num [hyperharmonic, Finset.sum_Icc_succ_top]

-- At the minimum order, the normalization reduces to the ordinary harmonic asymptotic.
example : (fun n : ℕ ↦ (harmonic n : ℝ)) ~[atTop] fun n : ℕ ↦ Real.log n := by
  simpa [hyperharmonic_one] using hyperharmonic_isEquivalent 1 le_rfl

-- At order three, both the exponent and factorial normalization are nontrivial.
example :
    (fun n : ℕ ↦ (hyperharmonic 3 n : ℝ)) ~[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log n / 2 := by
  simpa [Nat.factorial] using hyperharmonic_isEquivalent 3 (by decide)
