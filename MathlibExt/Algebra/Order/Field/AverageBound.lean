/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# A value bounded by an average plus a slack

In a linearly ordered field, if `0 < m` and `m * (M - p) ≤ T`, then `M ≤ T / m + p`
(`MathlibExt.le_div_add_of_mul_sub_le`). If moreover `T / m ≤ B` and `p ≤ B`, then
`M ≤ 2 * B` (`MathlibExt.le_two_mul_of_mul_sub_le`).

These are the arithmetic steps of the textbook analysis of Graham's list scheduling, read
with `m` machines, makespan `M`, the length `p` of a job that finishes at time `M`, total work
`T`, and `B` the optimal makespan. They contain no scheduling model: the hypothesis
`m * (M - p) ≤ T` is assumed, not derived. The list-scheduling theorem for concrete schedules
is `Cslib.Algorithms.Lean.Scheduling.listSchedule_approx` in `CSLibExt`.
-/

@[expose] public section

namespace MathlibExt

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If `0 < m` and `m * (M - p) ≤ T`, then `M ≤ T / m + p`. -/
theorem le_div_add_of_mul_sub_le (m M p T : K) (hm : 0 < m)
    (h : m * (M - p) ≤ T) : M ≤ T / m + p := by
  have h1 : M - p ≤ T / m := (le_div_iff₀ hm).mpr (by linarith)
  linarith

/-- If `0 < m`, `m * (M - p) ≤ T`, `T / m ≤ B` and `p ≤ B`, then `M ≤ 2 * B`. -/
theorem le_two_mul_of_mul_sub_le (m M p T B : K) (hm : 0 < m)
    (h : m * (M - p) ≤ T) (hT : T / m ≤ B) (hp : p ≤ B) :
    M ≤ 2 * B := by
  have hMb := le_div_add_of_mul_sub_le m M p T hm h
  linarith

end MathlibExt
