/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositionTernary
import Mathlib.Data.List.Infix

namespace MetaMathlibExt.even_eq_ternaryStrings_avoiding

-- The empty word contributes one.
example : positionalColoredCompositionCount 2 0 0 = 1 := by
  have words : {w : List (Fin 3) | w.length = 0 ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w ∧
      w.head? ≠ some 2 ∧ w.getLast? ≠ some 0} = {[]} := by
    ext w
    cases w <;> simp
  rw [even_eq_ternaryStrings_avoiding, words, Set.ncard_singleton]

-- At length two the four restrictions leave precisely 02 and 11.
example : positionalColoredCompositionCount 2 0 2 = 2 := by
  have pair : ∀ a b : Fin 3,
      (¬ [0, 1] <:+: [a, b] ∧ ¬ [1, 2] <:+: [a, b] ∧
        [a, b].head? ≠ some 2 ∧ [a, b].getLast? ≠ some 0) ↔
      [a, b] = [0, 2] ∨ [a, b] = [1, 1] := by decide
  have words : {w : List (Fin 3) | w.length = 2 ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w ∧
      w.head? ≠ some 2 ∧ w.getLast? ≠ some 0} = {[0, 2], [1, 1]} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hl, hw⟩
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
      exact (pair a b).mp hw
    · rintro (rfl | rfl)
      · exact ⟨rfl, (pair 0 2).mpr (Or.inl rfl)⟩
      · exact ⟨rfl, (pair 1 1).mpr (Or.inr rfl)⟩
  rw [even_eq_ternaryStrings_avoiding, words, Set.ncard_pair (by decide)]

end MetaMathlibExt.even_eq_ternaryStrings_avoiding
