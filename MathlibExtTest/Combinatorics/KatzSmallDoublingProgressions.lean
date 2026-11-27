/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KatzSmallDoublingProgressions

open MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted

example : katzSumset ({-1, 1} : Finset ℤ) = {-2, 0, 2} := by decide

example (a : ℤ) : (katzAPSet 3 {a}).ncard = 1 := by
  have h : katzAPSet 3 ({a} : Finset ℤ) = {(a, 0)} := by
    ext w
    change (∀ i : ℕ, i < 3 → w.1 + (i : ℤ) * w.2 ∈ ({a} : Finset ℤ)) ↔ w = (a, 0)
    constructor
    · intro hw
      have h₀ : w.1 = a := by simpa using hw 0 (by decide)
      have h₁ : w.1 + w.2 = a := by simpa using hw 1 (by decide)
      exact Prod.ext h₀ (by omega)
    · rintro rfl
      simp
  rw [h, Set.ncard_singleton]

example : ({(0, 1), (2, -1), (1, 0)} : Set (ℤ × ℤ)) ⊆
    katzAPSet 3 ({0, 1, 2} : Finset ℤ) := by
  intro w hw i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hw with rfl | rfl | rfl <;> rcases h with rfl | rfl | rfl <;> decide
