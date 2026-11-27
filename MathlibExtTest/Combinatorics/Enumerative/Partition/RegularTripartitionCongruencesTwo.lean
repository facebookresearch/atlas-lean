/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesTwo

open MetaMathlibExt

-- Both divisors are attained at the first indices in the two progressions.
example : regularTripartitionCount 2 1 = 3 := regularTripartitionCount_one 2 (by decide)

example : regularTripartitionCount 2 2 = 6 := by
  have card (n : ℕ) (hn : n ≤ 2) : (Nat.Partition.restricted n (¬ 2 ∣ ·)).card = 1 := by
    let ones : n.Partition :=
      { parts := Multiset.replicate n 1
        parts_pos := fun h ↦ by simp [Multiset.eq_of_mem_replicate h]
        parts_sum := by simp }
    rw [Finset.card_eq_one]
    refine ⟨ones, ?_⟩
    ext p
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hp
      have hparts : p.parts = Multiset.replicate p.parts.card 1 := by
        refine Multiset.eq_replicate_card.mpr fun i hi ↦ ?_
        have hpos := p.parts_pos hi
        have hle := p.le_of_mem_parts hi
        have hndvd := hp i hi
        omega
      have hcard : n = p.parts.card := by simpa [p.parts_sum] using congrArg Multiset.sum hparts
      exact Nat.Partition.ext (hparts.trans (congrArg (Multiset.replicate · 1) hcard.symm))
    · rintro rfl i hi
      rw [Multiset.eq_of_mem_replicate hi]
      decide
  simp at card
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, card 0 (by decide),
    card 1 (by decide), card 2 (by decide)]

-- The second branch also applies at odd sizes in the progression 3n + 2.
example : 3 ∣ regularTripartitionCount 2 4 ∧ 6 ∣ regularTripartitionCount 2 5 :=
  regularTripartitionCount_two_mod_three_six 1
