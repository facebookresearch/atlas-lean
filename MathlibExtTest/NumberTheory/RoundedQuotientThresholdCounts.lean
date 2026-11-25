/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoundedQuotientThresholdCounts

open MetaMathlibExt

-- The empty interval contributes at neither threshold.
example : ((Finset.Icc 1 0).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(0 : ℚ) / d + 1 / 2⌋)).card = 0 :=
  (round_div_sequence_card_ge (n := 0)).1

example : ((Finset.Icc 1 0).filter (fun d : ℕ => (2 : ℤ) ≤ ⌊(0 : ℚ) / d + 1 / 2⌋)).card = 0 :=
  (round_div_sequence_card_ge (n := 0)).2 (k := 2) (by decide)

-- With one denominator, only the first threshold is reached.
example : ((Finset.Icc 1 1).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(1 : ℚ) / d + 1 / 2⌋)).card = 1 :=
  (round_div_sequence_card_ge (n := 1)).1

example : ((Finset.Icc 1 1).filter (fun d : ℕ => (2 : ℤ) ≤ ⌊(1 : ℚ) / d + 1 / 2⌋)).card = 0 :=
  (round_div_sequence_card_ge (n := 1)).2 (k := 2) (by decide)

-- At `d = 2`, `3 / d = 3 / 2` rounds up and is counted at threshold 2.
example : (2 : ℕ) ∈ (Finset.Icc 1 3).filter (fun d : ℕ => (2 : ℤ) ≤ ⌊(3 : ℚ) / d + 1 / 2⌋) := by
  decide +kernel

example : ((Finset.Icc 1 3).filter (fun d : ℕ => (2 : ℤ) ≤ ⌊(3 : ℚ) / d + 1 / 2⌋)).card = 2 :=
  (round_div_sequence_card_ge (n := 3)).2 (k := 2) (by decide)
