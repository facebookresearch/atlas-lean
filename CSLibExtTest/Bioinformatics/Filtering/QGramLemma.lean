/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Filtering.QGramLemma
public meta import CSLibExt.Bioinformatics.Filtering.QGramLemma
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# `q`-gram filtering lemma tests

Executed fixtures: the `q`-grams of `ACGTAC` and the number of aligned `q`-grams it shares with
`ACCTAC` (one mismatch) for `q = 0, 2, 3, 4, 6`, where the bound `w - q + 1 ≤ s + k q` is attained
for `q = 2, 3`; `q = 7 > w`, where `ACGTAC` shares no aligned `q`-gram even with itself, so the
hypothesis `q ≤ w` is needed; two mismatches in a word of length `8`; the boundary
`k q = w - q + 1`, where two words at Hamming distance `k` share no aligned `q`-gram, so the
strict hypothesis of the corollary cannot be relaxed. Closed checks: the three theorems
instantiated.
-/

@[expose] public section

open Finset Cslib.Bioinformatics.Filtering.QGramLemma

namespace CSLibExtTest.Bioinformatics.Filtering.QGramLemma

/-- `ACGTAC`. -/
def x₁ : Fin 6 → Char := !['A', 'C', 'G', 'T', 'A', 'C']

/-- `ACCTAC`: one mismatch with `x₁`, at position `2`. -/
def y₁ : Fin 6 → Char := !['A', 'C', 'C', 'T', 'A', 'C']

#guard hammingDist x₁ y₁ = 1
-- The `2`-grams of `x₁`: `AC`, `CG`, `GT`, `TA`, `AC`.
#guard (List.finRange 5).map (fun i => List.ofFn (qGram x₁ 2 i)) =
  ["AC", "CG", "GT", "TA", "AC"].map String.toList
-- `q = 2`: the mismatch spoils the windows at offsets `1` and `2`; `5 = 3 + 1 * 2`.
#guard #{i | qGram x₁ 2 i = qGram y₁ 2 i} = 3
-- `q = 3`: only the window at offset `3` survives; `4 = 1 + 1 * 3`.
#guard #{i | qGram x₁ 3 i = qGram y₁ 3 i} = 1
-- `q = 4`: every window contains position `2`.
#guard #{i | qGram x₁ 4 i = qGram y₁ 4 i} = 0
-- `q = w`: one window, which contains the mismatch; identical words share it.
#guard #{i | qGram x₁ 6 i = qGram y₁ 6 i} = 0
#guard #{i | qGram x₁ 6 i = qGram x₁ 6 i} = 1
-- `q = 0`: all `w + 1` empty windows agree.
#guard #{i | qGram x₁ 0 i = qGram y₁ 0 i} = 7
-- `q > w`: there are no windows, so a word shares no `7`-gram even with itself; without `q ≤ w`
-- the corollary would claim one, as `k * q = 0 < 1 = 6 - 7 + 1` in `ℕ`.
#guard #{i | qGram x₁ 7 i = qGram x₁ 7 i} = 0

/-- `AAAAAAAA`. -/
def x₂ : Fin 8 → Char := !['A', 'A', 'A', 'A', 'A', 'A', 'A', 'A']

/-- `ABAAAABA`: mismatches with `x₂` at positions `1` and `6`. -/
def y₂ : Fin 8 → Char := !['A', 'B', 'A', 'A', 'A', 'A', 'B', 'A']

#guard hammingDist x₂ y₂ = 2
-- `q = 3`: the windows at offsets `2` and `3` survive; `6 ≤ 2 + 2 * 3`.
#guard #{i | qGram x₂ 3 i = qGram y₂ 3 i} = 2

/-- `AAAAA`. -/
def x₃ : Fin 5 → Char := !['A', 'A', 'A', 'A', 'A']

/-- `ABABA`: mismatches with `x₃` at positions `1` and `3`. -/
def y₃ : Fin 5 → Char := !['A', 'B', 'A', 'B', 'A']

-- The boundary `k q = w - q + 1` (`k = q = 2`, `w = 5`): no aligned `2`-gram is shared.
#guard hammingDist x₃ y₃ = 2
#guard #{i | qGram x₃ 2 i = qGram y₃ 2 i} = 0

-- The theorems, instantiated.
example : 6 - 2 + 1 ≤ #{i | qGram x₁ 2 i = qGram y₁ 2 i} + 1 * 2 :=
  sub_add_one_le_card_qGram_eq_add_mul (by decide) (by decide)

example : 8 - 3 + 1 ≤ #{i | qGram x₂ 3 i = qGram y₂ 3 i} + 2 * 3 :=
  sub_add_one_le_card_qGram_eq_add_mul (by decide) (by decide)

example : ∃ i, qGram x₁ 3 i = qGram y₁ 3 i :=
  exists_qGram_eq_of_mul_lt (k := 1) (by decide) (by decide) (by decide)

example : ¬∃ i, qGram x₃ 2 i = qGram y₃ 2 i := by decide

example : (x₁, y₁) ∈ {p : (Fin 6 → Char) × (Fin 6 → Char) | ∃ i, qGram p.1 3 i = qGram p.2 3 i} :=
  setOf_hammingDist_le_subset (k := 1) (by decide) (by decide) subset_rfl
    (show hammingDist x₁ y₁ ≤ 1 by decide)

end CSLibExtTest.Bioinformatics.Filtering.QGramLemma
