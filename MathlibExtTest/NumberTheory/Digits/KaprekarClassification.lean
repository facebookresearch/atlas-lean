/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.KaprekarClassification

open MetaMathlibExt

-- Five digits cannot be the combined length of the blocks in any of the five families.
example {α : ℕ} (hα : α < 10 ^ 5) (hne : α ≠ 0) : kaprekarMap 5 α ≠ α := by
  intro h
  obtain ⟨s, hlen, _, hf⟩ := (kaprekarMap_fixed_iff (by decide) hα hne).mp h
  rcases hf with ⟨x, hx, rfl⟩ | ⟨y, rfl⟩ | ⟨x, y, hx, rfl⟩ | ⟨x, z, hx, hz, rfl⟩ |
    ⟨x, z, y, w, hx, hz, rfl⟩
  all_goals
    simp [List.length_flatten] at hlen
    omega

-- The shortest word in the fifth family includes a zero and has no optional blocks.
example : kaprekarMap 8 97508421 = 97508421 := by
  apply (kaprekarMap_fixed_iff (by decide) (by decide) (by decide)).mpr
  refine ⟨[1, 2, 4, 5, 7, 8, 0, 9], rfl, ?_, Or.inr (.inr (.inr (.inr ?_)))⟩
  · norm_num [kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons, Nat.ofDigits_cons]
  · exact ⟨1, 1, 0, 0, by decide, by decide, rfl⟩
