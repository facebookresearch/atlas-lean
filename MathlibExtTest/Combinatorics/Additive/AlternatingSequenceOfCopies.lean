/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.AlternatingSequenceOfCopies

/-! # Tests for `MathlibExt.Combinatorics.Additive.AlternatingSequenceOfCopies` -/

open scoped Pointwise
open MetaMathlibExt (alternating_sequence_of_copies)

namespace MathlibExtTest.AlternatingSequenceOfCopies

/-- The Conway set, a sum-dominated set with eight elements. -/
private def conway : Finset ℤ := {0, 2, 3, 4, 7, 11, 12, 14}

/-- The sets of the construction for the Conway set and the modulus `n`: adjoin `l * n` to get
the term of index `2 * l`, and the copy `conway + {l * n}` to get the term of index `2 * l + 1`. -/
private def seq (n : ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | 1 => conway
  | i + 2 => if i % 2 = 0 then seq n (i + 1) ∪ {((i / 2 + 1 : ℕ) : ℤ) * n}
      else seq n i ∪ (conway + {((i / 2 + 1 : ℕ) : ℤ) * n})

private theorem seq_even (n : ℤ) :
    ∀ l ≥ 1, seq n (2 * l) = seq n (2 * l - 1) ∪ {(l : ℤ) * n} := by
  intro l hl
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, show 2 * m + 2 - 1 = 2 * m + 1 by omega, seq,
    ite_eq_left (by omega), show 2 * m / 2 + 1 = m + 1 by omega]

private theorem seq_odd (n : ℤ) :
    ∀ l ≥ 1, seq n (2 * l + 1) = seq n (2 * l - 1) ∪ (conway + {(l : ℤ) * n}) := by
  intro l hl
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega, show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
    seq, ite_eq_right (by omega), show (2 * m + 1) / 2 + 1 = m + 1 by omega]

-- Test section: the example of Herrmann, Hill, Phillips, Flores, Miller and Senger. For the
-- Conway set and `n = 17`, the counts in condition (b) are `x = 3` and `y = 4`, and there are
-- `26` sums and `25` differences, so `2 * y - x - 1 = 4 > 1`.
example : (conway.filter fun a => 17 + a ∉ conway + conway).card = 3 ∧
    (conway.filter fun b => 17 - b ∉ conway - conway).card = 4 ∧
    (conway + conway).card = 26 ∧ (conway - conway).card = 25 := by
  decide +kernel

-- All hypotheses hold for the Conway set and `n = 17`, so the sets alternate forever.
example : ∀ l ≥ 1, (seq 17 (2 * l) + seq 17 (2 * l)).card < (seq 17 (2 * l) - seq 17 (2 * l)).card ∧
      (seq 17 (2 * l + 1) - seq 17 (2 * l + 1)).card <
        (seq 17 (2 * l + 1) + seq 17 (2 * l + 1)).card ∧
      seq 17 (2 * l - 1) ⊂ seq 17 (2 * l) ∧ seq 17 (2 * l) ⊂ seq 17 (2 * l + 1) :=
  alternating_sequence_of_copies conway 17 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (seq 17) rfl (seq_even 17)
    (seq_odd 17)

-- The second term of that sequence is the Conway set with `17` adjoined.
example : (conway ∪ {17} + (conway ∪ {17})).card < (conway ∪ {17} - (conway ∪ {17})).card := by
  have h := (alternating_sequence_of_copies conway 17 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (seq 17) rfl (seq_even 17)
    (seq_odd 17) 1 le_rfl).1
  rwa [seq_even 17 1 le_rfl] at h

-- Test section: condition (b) cannot be dropped. For `n = 16` every other hypothesis holds,
-- condition (b) fails, and the Conway set with `16` adjoined has more sums than differences.
example : (∀ a ∈ conway, 0 ≤ a ∧ a < 16) ∧
    ((conway + conway).image (· % 16)).card = ((conway - conway).image (· % 16)).card ∧
    ¬ (2 * ((conway.filter fun b => 16 - b ∉ conway - conway).card : ℤ) -
        (conway.filter fun a => 16 + a ∉ conway + conway).card - 1 >
      ((conway + conway).card : ℤ) - (conway - conway).card) ∧
    (conway ∪ {16} - (conway ∪ {16})).card < (conway ∪ {16} + (conway ∪ {16})).card := by
  decide +kernel

/-- A translate of the Conway set containing `0` and negative elements. -/
private def conwayShift : Finset ℤ := {-14, -12, -11, -10, -7, -3, -2, 0}

-- Test section: the bound `0 ≤ a` cannot be dropped. With `n = 3`, the translate is
-- sum-dominated, contains `0`, lies below `n` and meets both counting conditions, but adjoining
-- the copy `conwayShift + {3}` gives as many differences as sums.
example : (conwayShift - conwayShift).card < (conwayShift + conwayShift).card ∧ 0 ∈ conwayShift ∧
    (∀ a ∈ conwayShift, a < 3) ∧
    ((conwayShift + conwayShift).image (· % 3)).card =
      ((conwayShift - conwayShift).image (· % 3)).card ∧
    2 * ((conwayShift.filter fun b => 3 - b ∉ conwayShift - conwayShift).card : ℤ) -
        (conwayShift.filter fun a => 3 + a ∉ conwayShift + conwayShift).card - 1 >
      ((conwayShift + conwayShift).card : ℤ) - (conwayShift - conwayShift).card ∧
    (conwayShift ∪ (conwayShift + {3}) - (conwayShift ∪ (conwayShift + {3}))).card =
      (conwayShift ∪ (conwayShift + {3}) + (conwayShift ∪ (conwayShift + {3}))).card := by
  decide +kernel

end MathlibExtTest.AlternatingSequenceOfCopies
