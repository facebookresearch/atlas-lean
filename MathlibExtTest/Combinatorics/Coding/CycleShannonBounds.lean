/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBounds

/-! # Tests for the 7-cycle capacity bounds -/

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

-- The production import exposes both exact bounds, with no import of WantedExt.
example : ENNReal.rpow 343 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 ∧
    shannonCapacityCycle 7 ≤ (7 : ENNReal) / 2 :=
  ⟨bmrrst1971LowerBound, shannon1956UpperBound⟩

-- A one-letter code cannot have four codewords: its rate is its cardinality.
example (A : CycleCode 7 1) : A.1.card ≤ 3 := by
  have hrate : (A.1.card : ENNReal) ≤ (7 : ENNReal) / 2 := by
    simpa [cycleCodeRate] using
      (cycleCodeRate_le_shannonCapacity 7 ⟨1, le_rfl⟩ A).trans shannon1956UpperBound
  have hcut : (7 : ENNReal) / 2 < 4 :=
    (ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)).2 (by
      exact_mod_cast (show (7 : ℕ) < 4 * 2 by decide))
  have hcard : A.1.card < 4 := by exact_mod_cast hrate.trans_lt hcut
  exact Nat.le_of_lt_succ hcard
