/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TuDengConjecture

namespace MathlibExtTest.NumberTheory.TuDengConjecture

open MathlibExt.NumberTheory.TuDengConjectureWanted (tuDengConjecture_holds)
open MetaMathlibExt (binDigitSum)

private def pairs (k : ℕ) (t : ZMod (2 ^ k - 1)) : Set (ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1)) :=
  {p | p.1 + p.2 = t ∧ binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}

-- The first admissible k attains the bound with both orderings of (0, 1).
example : (pairs 2 1).ncard = 2 := by
  apply le_antisymm (tuDengConjecture_holds 2 (by decide) 1 (by decide))
  change 2 ≤ (pairs 2 1).ncard
  have h : ({(0, 1), (1, 0)} : Set (ZMod 3 × ZMod 3)) ⊆ pairs 2 1 := by
    intro p hp
    rcases hp with hp | hp
    · subst p
      unfold pairs
      decide
    · change p = (1, 0) at hp
      subst p
      unfold pairs
      decide
  simpa using Set.ncard_le_ncard h

-- In three bits, (4, 4) wraps to 1 modulo 7. The bound is strict for this target.
example : (pairs 3 1).ncard = 3 := by
  have h : pairs 3 1 = ({(0, 1), (1, 0), (4, 4)} : Set (ZMod 7 × ZMod 7)) := by
    apply Set.ext
    change ∀ p : ZMod 7 × ZMod 7, (p.1 + p.2 = 1 ∧
      binDigitSum p.1.val + binDigitSum p.2.val ≤ 2) ↔
      p = (0, 1) ∨ p = (1, 0) ∨ p = (4, 4)
    decide
  rw [h]
  simp [Set.ncard_insert_of_notMem, show (0 : ZMod 7) ≠ 1 by decide,
    show (0 : ZMod 7) ≠ 4 by decide, show (1 : ZMod 7) ≠ 4 by decide]

end MathlibExtTest.NumberTheory.TuDengConjecture
