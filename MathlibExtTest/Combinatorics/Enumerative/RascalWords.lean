/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Sublists
import MathlibExt.Combinatorics.Enumerative.RascalWords

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- The empty word contributes once at every ascent bound.
example (j : ℕ) : rascalGen j 0 0 = 1 := by
  calc
    _ = ({[]} : Finset (List ℕ)).card := by
      apply Nat.subtype_card
      intro w
      cases w <;> simp [wordAscents]
    _ = 1 := Finset.card_singleton _

-- At the first positive bound, a word and its odd-position flip straddle the cutoff.
example : RascalWord 1 3 7 := ⟨[0, 0, 1, 1, 1, 0, 0], by decide⟩

example : wordAscents [1, 0, 0, 1, 0, 0, 1] = 2 := rfl

-- With no ascents allowed, the first row covered by the theorem counts four words.
example : ∑ k ∈ Finset.range 4, (rascalGen 0 k 3 : ℤ) = 4 := by
  simpa using sum_rascalGen_four_mul_add_three 0

-- The empty row contributes once even when the binomial cutoff extends past the row.
example (j : ℕ) : ∑ k ∈ Finset.range 1, (rascalGen j k 0 : ℤ) = 1 := by
  rw [show 1 = 0 + 1 by rfl, sum_rascalGen_row]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
  · simp

-- With no ascents, each number of ones determines a unique word.
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (rascalGen 0 k n : ℤ) = n + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using sum_rascalGen_row 0 n

-- At the first nontrivial cutoff, only the word 0101 is excluded.
example : ∑ k ∈ Finset.range 5, (rascalGen 1 k 4 : ℤ) = 15 := by
  rw [sum_rascalGen_row 1 4]
  decide

-- The first odd row cancels at every ascent bound.
example (j : ℕ) :
    ∑ k ∈ Finset.range 2, (-1 : ℤ) ^ k * (rascalGen j k 1 : ℤ) = 0 := by
  simpa using sum_rascalGen_alternating_odd j 0

-- At cutoff one, 00110 and its reverse-complement 10011 are both admitted,
-- but 01010 has two ascents and is excluded.
example : RascalWord 1 2 5 := ⟨[0, 0, 1, 1, 0], by decide⟩

example : RascalWord 1 3 5 := ⟨[1, 0, 0, 1, 1], by decide⟩

example : ¬ (wordAscents [0, 1, 0, 1, 0] ≤ 1) := by decide

example : ∑ k ∈ Finset.range 6, (-1 : ℤ) ^ k * (rascalGen 1 k 5 : ℤ) = 0 := by
  simpa using sum_rascalGen_alternating_odd 1 2

private def avoidsTriple : List ℕ → Bool
  | [a, b, c] => decide (¬ (a = b ∧ b < c) ∧ ¬ (c < b ∧ b < a))
  | _ => true

private theorem avoids001210_of_all {w : List ℕ} (h : w.sublists.all avoidsTriple = true) :
    Avoids001210 w := by
  intro a b c habc
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_sublists.mpr habc))

-- With k = 0 only the first branch can apply, including to the empty word.
example (w : AscentSeqAvoid 0 0) : w.1 = [] := by
  rcases ascentSeqAvoid_form 0 0 w with h | ⟨_, x, _, _, hx, _⟩
  · exact h
  · exact (Nat.not_lt_zero x hx).elim

-- The increasing prefix can end in more than one copy of its largest letter and
-- still be followed by a lower constant tail.
example :
    ∃ y x : ℕ, 1 ≤ y ∧ y < 6 - 2 ∧ x < 2 ∧
      [0, 1, 2, 2, 1, 1] = List.range 2 ++ List.replicate y 2 ++
        List.replicate (6 - 2 - y) x := by
  have hseq : IsAscentSeq [0, 1, 2, 2, 1, 1] := by
    refine ⟨fun _ => rfl, ?_⟩
    intro i hi
    change i < 6 at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  let w : AscentSeqAvoid 6 2 := ⟨[0, 1, 2, 2, 1, 1], rfl, hseq, avoids001210_of_all (by decide), rfl⟩
  apply (ascentSeqAvoid_form 6 2 w).resolve_left
  change [0, 1, 2, 2, 1, 1] ≠ List.range 2 ++ List.replicate (6 - 2) 2
  decide

-- The first difference at the empty row is one at ascent bound zero.
example : (∑ k ∈ Finset.range 2, rascalGenZ 0 1 (k : ℤ)) -
    (∑ k ∈ Finset.range 1, rascalGenZ 0 0 (k : ℤ)) = 1 := by
  exact iterate_forwardDiff_sum_rascalGen 0 0

-- At ascent bound one the third difference at the next row uses rows one through four.
example : (∑ k ∈ Finset.range 5, rascalGenZ 1 4 (k : ℤ)) -
    3 * (∑ k ∈ Finset.range 4, rascalGenZ 1 3 (k : ℤ)) +
    3 * (∑ k ∈ Finset.range 3, rascalGenZ 1 2 (k : ℤ)) -
    (∑ k ∈ Finset.range 2, rascalGenZ 1 1 (k : ℤ)) = 1 := by
  have h := iterate_forwardDiff_sum_rascalGen 1 1
  change
    (((∑ k ∈ Finset.range 5, rascalGenZ 1 4 (k : ℤ)) -
        (∑ k ∈ Finset.range 4, rascalGenZ 1 3 (k : ℤ))) -
      ((∑ k ∈ Finset.range 4, rascalGenZ 1 3 (k : ℤ)) -
        (∑ k ∈ Finset.range 3, rascalGenZ 1 2 (k : ℤ)))) -
    (((∑ k ∈ Finset.range 4, rascalGenZ 1 3 (k : ℤ)) -
        (∑ k ∈ Finset.range 3, rascalGenZ 1 2 (k : ℤ))) -
      ((∑ k ∈ Finset.range 3, rascalGenZ 1 2 (k : ℤ)) -
        (∑ k ∈ Finset.range 2, rascalGenZ 1 1 (k : ℤ)))) = 1 at h
  omega

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
