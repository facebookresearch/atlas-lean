/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EvenFibonacciAccessibility

open MetaMathlibExt

-- The definition also excludes a palette of size zero.
example (r : ℕ) : IsRAccessible r evenFibonacciSet ↔ r = 1 := by
  obtain ⟨hone, hmany⟩ := evenFibonacciSet_degreeOfAccessibility_eq_one
  constructor
  · intro h
    have := h.2.1
    by_contra hne
    exact hmany r (by omega) h
  · rintro rfl
    exact hone

-- At the first excluded palette size there is a coloring and a positive forbidden length.
example : ∃ (c : ℕ+ → Fin 2) (k : ℕ), 1 ≤ k ∧ ¬ ∃ x : Fin k → ℕ+,
    IsMonochromatic c x ∧ IsDDiffSequence evenFibonacciSet (fun i => ((x i : ℕ) : ℤ)) := by
  obtain ⟨hone, hmany⟩ := evenFibonacciSet_degreeOfAccessibility_eq_one
  by_contra! hall
  exact hmany 2 le_rfl ⟨hone.1, by decide, hall⟩
