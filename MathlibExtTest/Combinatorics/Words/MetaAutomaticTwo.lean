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

-- The seed produces all four states, so the next iteration exercises every row.
example : ∃ w : ℕ → ℕ,
    [w 0, w 1, w 2, w 3] = [0, 1, 3, 2] ∧
      [w 4, w 5, w 6, w 7] = [2, 3, 1, 0] ∧
      [w 8, w 9, w 10, w 11] = [1, 0, 2, 3] ∧
      [w 12, w 13, w 14, w 15] = [3, 2, 0, 1] := by
  obtain ⟨w, hzero, hstep, _⟩ := metaAutomaticTwo_morphism_coding
  have hrow (n : ℕ) :
      [w (4 * n + 0), w (4 * n + 1), w (4 * n + 2), w (4 * n + 3)] =
        [0, 1, 2, 3].map (fun r =>
          ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD (w n) []).getD r 0) := by
    simp only [List.map_cons, List.map_nil, hstep n 0 (by decide), hstep n 1 (by decide),
      hstep n 2 (by decide), hstep n 3 (by decide)]
  have hseed : [w 0, w 1, w 2, w 3] = [0, 1, 3, 2] := by simpa [hzero] using hrow 0
  obtain ⟨_, h₁, h₂, h₃⟩ : w 0 = 0 ∧ w 1 = 1 ∧ w 2 = 3 ∧ w 3 = 2 := by
    simpa only [List.cons.injEq, and_true] using hseed
  exact ⟨w, hseed, by simpa [h₁] using hrow 1, by simpa [h₂] using hrow 2,
    by simpa [h₃] using hrow 3⟩

-- Outside the seed block, states 2 and 3 are coded to false and true, respectively.
example : metaAutomaticTwo 4 = false ∧ metaAutomaticTwo 5 = true := by
  obtain ⟨w, hzero, hstep, hcode⟩ := metaAutomaticTwo_morphism_coding
  have h₁ : w 1 = 1 := by simpa [hzero] using hstep 0 1 (by decide)
  have h₄ : w 4 = 2 := by simpa [h₁] using hstep 1 0 (by decide)
  have h₅ : w 5 = 3 := by simpa [h₁] using hstep 1 1 (by decide)
  exact ⟨by simpa [h₄] using hcode 4, by simpa [h₅] using hcode 5⟩
