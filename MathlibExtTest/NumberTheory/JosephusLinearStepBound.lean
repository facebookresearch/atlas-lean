/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusLinearStepBound

open MathlibExt.NumberTheory.JosephusWanted

-- At the initial point the quotient is zero, so only the zero step fits.
example (m : ℕ) : 1 + 2 * m ≤ 1 + m ↔ m = 0 :=
  ((shift_le_iff_le_div 2 0 (by decide) (by decide)).1 m).trans Nat.le_zero

-- At J₅(8) = 3 the numerator is 5 and the denominator is 4.
example (m : ℕ) : 3 + 5 * m ≤ 8 + m ↔ m ≤ 1 :=
  (shift_le_iff_le_div 5 7 (by decide) (by decide)).1 m

-- The sufficient condition for one step includes equality.
example : MetaMathlibExt.josephus 2 2 + 2 * 1 ≤ 2 + 1 := by
  obtain ⟨hsteps, hone⟩ := shift_le_iff_le_div 2 1 (by decide) (by decide)
  exact (hsteps 1).mpr (hone (by decide))
