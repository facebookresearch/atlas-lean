/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciGeneratingFunctionsKnappMRelations
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The theorem still applies when the original second coordinate is zero.
example : knappM 1 0 1 1 = -1 ∧ (knappM 1 0 1 0 ^ 2 : ℚ) = 1 := by
  obtain ⟨hrec, hquad⟩ := knappM_recurrence_and_quadratic 1 0 1 0 (by decide)
  constructor
  · convert hrec using 1 <;> norm_num [knappM]
  · convert hquad using 1 <;> norm_num [knappM]

-- Nonzero, unequal seeds exercise the sign of the mixed term.
example : knappM 1 2 2 3 = -34 ∧
    knappM 1 2 1 1 ^ 2 + 3 * knappM 1 2 1 1 * knappM 1 2 1 2 +
      knappM 1 2 1 2 ^ 2 = -1 := by
  obtain ⟨hrec, hquad⟩ := knappM_recurrence_and_quadratic 1 2 1 1 (by decide)
  constructor
  · convert hrec using 1 <;> norm_num [knappM]
  · norm_num only [Int.reduceAdd, Int.reduceMul, Int.reduceSub, Int.reducePow, Int.cast_neg,
      Int.cast_one] at hquad
    exact hquad

-- A zero middle second coordinate is allowed as well.
example : knappM 1 0 0 (-1) = 0 := by
  have h := (knappM_recurrence_and_quadratic 1 0 1 (-1) (by decide)).1
  convert h using 1 <;> norm_num [knappM]
