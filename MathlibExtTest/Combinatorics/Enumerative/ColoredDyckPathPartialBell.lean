/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ColoredDyckPathPartialBell

open MetaMathlibExt

-- The six two-peak paths of semilength four have descent lengths (1,3), (2,2), or (3,1).
-- Giving a descent of length j exactly j colors yields twenty colored paths.
example : partialBellPolynomial 4 2 (fun j => (j.factorial : ℚ) * j) = 120 := by
  have h := coloredDyckPathCount_eq_partialBell (fun j => j) (n := 4) (by decide) 2
  have hcount : coloredDyckPathCount (fun j => j) 4 2 = 20 := by decide +kernel
  rw [hcount] at h
  norm_num [Nat.factorial] at h
  linarith

-- Here 1 + 1 - 3 truncates to zero, and a one-peak path cannot contribute.
example (γ : ℕ → ℕ) : partialBellPolynomial 1 3 (fun j => (j.factorial : ℚ) * γ j) = 0 := by
  have h := coloredDyckPathCount_eq_partialBell γ (n := 1) (by decide) 3
  have hpeak : ∀ p : {p : DyckWord // p.semilength = 1},
      (dyckPeakDescents p.1.toList).length ≠ 3 := by decide +kernel
  simpa [coloredDyckPathCount, hpeak, Nat.factorial] using h.symm
