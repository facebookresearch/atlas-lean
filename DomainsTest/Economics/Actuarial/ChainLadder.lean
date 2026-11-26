/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Actuarial.ChainLadder
import Mathlib.Tactic.NormNum

/-! # Tests for chain-ladder completion -/

open Domains.Economics.Actuarial.ChainLadder

namespace DomainsTest.Economics.Actuarial.ChainLadder

/-- Observed rows: `(2, 6, 9)`, `(8, 12)`, `(100)`. -/
private def weighted : Triangle 2
  | 0, 0, _ => 2
  | 0, 1, _ => 6
  | 0, _, _ => 9
  | 1, 0, _ => 8
  | 1, _, _ => 12
  | _, _, _ => 100

-- The first factor is (6 + 12) / (2 + 8), neither the mean of 3 and 3/2 nor 18/110.
private theorem first_factor : factor weighted 0 = 9 / 5 := by
  change (∑ i : Fin 2, weighted i 1 (by have := i.isLt; omega)) /
    (∑ i : Fin 2, weighted i 0 (by have := i.isLt; omega)) = 9 / 5
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change (6 + 12 : ℝ) / (2 + 8) = 9 / 5
  norm_num

-- The 12 on the middle row's diagonal has no successor and is excluded here.
private theorem second_factor : factor weighted 1 = 3 / 2 := by
  change (∑ i : Fin 1, weighted i 2 (by have := i.isLt; omega)) /
    (∑ i : Fin 1, weighted i 1 (by have := i.isLt; omega)) = 3 / 2
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  change (9 : ℝ) / 6 = 3 / 2
  norm_num

-- Both an observation before the diagonal and the latest observation are retained.
example : complete weighted 1 0 = 8 := complete_observed weighted 1 0 (by decide)
example : complete weighted 1 1 = 12 := complete_observed weighted 1 1 (by decide)

-- The youngest row must use both different factors in sequence.
private theorem first_forecast : complete weighted 2 1 = 180 := by
  rw [show (1 : Fin 3) = (0 : Fin 2).succ by decide, complete_succ weighted 2 0 (by decide),
    complete_observed weighted 2 _ (by decide), first_factor]
  norm_num [weighted]

private theorem ultimate : complete weighted 2 2 = 270 := by
  change complete weighted 2 (1 : Fin 2).succ = 270
  rw [complete_succ weighted 2 1 (by decide),
    show (1 : Fin 2).castSucc = 1 by decide, first_forecast, second_factor]
  norm_num

example : reserve weighted 2 = 170 := by
  change complete weighted 2 2 - 100 = 170
  rw [ultimate]
  norm_num

-- Row zero never forecasts. This includes the only row when there are no factors (`Fin 0`).
example {n : ℕ} (C : Triangle n) : reserve C 0 = 0 := by
  unfold reserve
  rw [complete_observed C 0 (Fin.last n) (by simp)]
  simp [latest]

example (C : Triangle 0) : complete C 0 0 = C 0 0 (by decide) :=
  complete_observed C 0 0 (by decide)

-- A flat triangle with zero individual claims can still have positive paired totals.
private def flat : Triangle 2 := fun i _ _ ↦ if i = 0 then 5 else 0

example : factor flat 0 = 1 ∧ factor flat 1 = 1 := by
  norm_num [factor, pairedBase, flat, Fin.sum_univ_succ]

-- All claims are nonnegative and the denominator is positive, but the older row declines.
private def declining : Triangle 1 := fun i j _ ↦ if i = 0 then (if j = 0 then 4 else 2) else 10

example : reserve declining 1 = -5 := by
  change complete declining 1 (0 : Fin 1).succ - 10 = -5
  rw [complete_succ declining 1 0 (by decide), complete_observed declining 1 _ (by decide)]
  change 10 * ((∑ i : Fin 1, declining i 1 (by have := i.isLt; omega)) /
    ∑ i : Fin 1, declining i 0 (by have := i.isLt; omega)) - 10 = -5
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  change (10 : ℝ) * (2 / 4) - 10 = -5
  norm_num

end DomainsTest.Economics.Actuarial.ChainLadder
