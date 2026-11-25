/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticTwo

open MetaMathlibExt

-- The two base values and the first pair defined by the recurrence.
example : [0, 1, 2, 3].map metaAutomaticTwo = [false, true, true, false] := by
  decide +kernel

-- At block indices 5 and 7 the nested selector takes both Boolean values.
example : [20, 21, 22, 23, 28, 29, 30, 31].map metaAutomaticTwo =
    [true, false, false, true, false, true, true, false] := by
  decide +kernel

example (n : ℕ) : metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
  have h := metaAutomaticTwo_balanced n
  cases he : metaAutomaticTwo (2 * n) <;> cases ho : metaAutomaticTwo (2 * n + 1) <;>
    simp_all

example : metaAutomaticTwo (2 * 0) = false ∧ metaAutomaticTwo (2 * 0 + 1) = true := by
  have h : xor (metaAutomaticTwo 0)
      (metaAutomaticTwo (2 * 0 + (metaAutomaticTwo 0).toNat)) = false := by decide +kernel
  simpa only [h, Bool.not_false] using metaAutomaticTwo_recover 0

-- At n = 4 the selector is false, so the nested term is the even term.
example : metaAutomaticTwo (2 * 4) = true ∧ metaAutomaticTwo (2 * 4 + 1) = false := by
  have hx : metaAutomaticTwo 4 = false := by decide +kernel
  have hy : metaAutomaticTwo (2 * 4 + (metaAutomaticTwo 4).toNat) = true := by
    decide +kernel
  have h := metaAutomaticTwo_recover 4
  rw [hy, hx] at h
  simpa only [Bool.false_xor, Bool.not_true] using h

-- At n = 5 the selector is true, so the nested term is the odd term.
example : metaAutomaticTwo (2 * 5) = false ∧ metaAutomaticTwo (2 * 5 + 1) = true := by
  have hx : metaAutomaticTwo 5 = true := by decide +kernel
  have hy : metaAutomaticTwo (2 * 5 + (metaAutomaticTwo 5).toNat) = true := by decide +kernel
  have h := metaAutomaticTwo_recover 5
  rw [hy, hx] at h
  simpa only [Bool.true_xor, Bool.not_true, Bool.not_false] using h
