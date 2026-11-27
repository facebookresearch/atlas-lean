/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasQOneShiftComposite

open MetaMathlibExt

-- At the smallest allowed parameter, index three rules out any smaller threshold.
example : ∃ N : ℕ, 4 ≤ N ∧ ∀ n ≥ N, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
    1 < lucasU ⟨3, 1, by decide⟩ n + d ∧ ¬ (lucasU ⟨3, 1, by decide⟩ n + d).natAbs.Prime := by
  obtain ⟨N, hN⟩ := lucasU_q_one_shifts_eventually_composite (P := 3) (hP := by decide)
  have hprime : (lucasU ⟨3, 1, by decide⟩ 3 + (-1)).natAbs.Prime := by decide
  refine ⟨N, ?_, hN⟩
  by_contra! h
  exact (hN 3 (by omega) (-1) (by simp)).2 hprime

-- Check all three shifts at the first even and odd indices covered by the proof.
example {n : ℕ} (hn : n = 4 ∨ n = 5) {d : ℤ} (hd : d ∈ ({-1, 0, 1} : Set ℤ)) :
    1 < lucasU ⟨3, 1, by decide⟩ n + d ∧ ¬ (lucasU ⟨3, 1, by decide⟩ n + d).natAbs.Prime := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hn with rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> decide
