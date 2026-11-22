/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical integer partitions and cardinalities, and keep proof helpers private.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

import MathlibExt.Combinatorics.Enumerative.Partition.ExponentialLowerBound
import MathlibExt.Combinatorics.Enumerative.Partition.ExponentialUpperBound

/-!
# Logarithmic bounds for the number of integer partitions

The number of integer partitions of `n` has logarithm to base two bounded above and below by
expressions whose leading term is `π * sqrt (2 / 3) / log 2 * sqrt n`. This is adapted from
`eth/proof/rates/ClauseBound/Part/Bounds.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Nat.Partition

private theorem logb_exp (x : ℝ) : Real.logb 2 (Real.exp x) = x / Real.log 2 := by
  rw [Real.logb, Real.log_exp]

private theorem leading_mul (x : ℝ) :
    (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * x =
      Real.pi * Real.sqrt ((2 : ℝ) / 3) * x / Real.log 2 := by
  ring

/-- There are constants `B` and `C` such that the base-two logarithm of the number of integer
partitions of `n` differs from its leading square-root term by at most a logarithmic lower-order
term below and a constant above. -/
theorem exists_logb_card_bounds :
    ∃ B C : ℝ,
      (∀ n : ℕ, 1 ≤ n →
        (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt n -
              B * Real.logb 2 (n : ℝ) - C ≤
            Real.logb 2 (Fintype.card (Partition n) : ℝ)) ∧
      (∀ n : ℕ,
        Real.logb 2 (Fintype.card (Partition n) : ℝ) ≤
          (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt n + C) := by
  obtain ⟨H, B, hH, hlow⟩ := exists_exp_div_pow_le_card
  refine ⟨B, max 0 (-Real.logb 2 H), fun n hn => ?_, fun n => ?_⟩
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos :
        0 < H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) /
          (n : ℝ) ^ B := by
      positivity
    have hlog := Real.logb_le_logb_of_le one_lt_two hpos (hlow n hn)
    rw [Real.logb_div (by positivity) (by positivity),
      Real.logb_mul hH.ne' (Real.exp_pos _).ne', logb_exp, Real.logb_pow] at hlog
    have hC : -Real.logb 2 H ≤ max 0 (-Real.logb 2 H) := le_max_right _ _
    rw [leading_mul]
    linarith
  · have hp : (0 : ℝ) < Fintype.card (Partition n) := by
      exact_mod_cast Fintype.card_pos (α := Partition n)
    have hlog := Real.logb_le_logb_of_le one_lt_two hp (card_le_exp n)
    rw [logb_exp] at hlog
    have hC : (0 : ℝ) ≤ max 0 (-Real.logb 2 H) := le_max_left _ _
    rw [leading_mul]
    linarith

end Nat.Partition
