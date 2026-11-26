/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.IntervalCases

/-!
# Sums of six and of eight nonzero squares

To get six squares, apply Lagrange's four-square theorem to `n - 26`, discard the
zero roots, and represent `26` with enough positive squares to complete the list.
Two extra ones turn a six-square representation into an eight-square representation.
-/

namespace MetaMathlibExt

private theorem fin_of_list {k n : ℕ} (l : List ℕ) (hlen : l.length = k)
    (hzero : 0 ∉ l) (hsum : (l.map (· ^ 2)).sum = n) :
    ∃ a : Fin k → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  subst k
  refine ⟨fun i => l[i.val], fun i hi => hzero (hi ▸ List.getElem_mem i.isLt), ?_⟩
  rw [← List.sum_ofFn]
  simpa only [List.map_ofFn, Function.comp_def] using
    (congrArg (fun xs : List ℕ => (xs.map (· ^ 2)).sum)
      (List.ofFn_getElem (xs := l))).trans hsum

private theorem sum_squares_filter_ne_zero (l : List ℕ) :
    ((l.filter (· != 0)).map (· ^ 2)).sum = (l.map (· ^ 2)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : a = 0 <;> simp [ha, ih]

-- Each possible number of missing roots can be supplied without changing the sum of 26.
private theorem pad_twenty_six (k : ℕ) (hk₁ : 2 ≤ k) (hk₂ : k ≤ 6) :
    ∃ l : List ℕ, l.length = k ∧ 0 ∉ l ∧ (l.map (· ^ 2)).sum = 26 := by
  interval_cases k
  · exact ⟨[1, 5], by decide⟩
  · exact ⟨[1, 3, 4], by decide⟩
  · exact ⟨[2, 2, 3, 3], by decide⟩
  · exact ⟨[1, 1, 2, 2, 4], by decide⟩
  · exact ⟨[1, 2, 2, 2, 2, 3], by decide⟩

private theorem sum_six_squares_list (n : ℕ) (hn : 20 ≤ n) :
    ∃ l : List ℕ, l.length = 6 ∧ 0 ∉ l ∧ (l.map (· ^ 2)).sum = n := by
  by_cases h : n < 26
  · interval_cases n
    · exact ⟨[1, 1, 1, 2, 2, 3], by decide⟩
    · exact ⟨[1, 1, 1, 1, 1, 4], by decide⟩
    · exact ⟨[1, 1, 1, 1, 3, 3], by decide⟩
    · exact ⟨[1, 1, 2, 2, 2, 3], by decide⟩
    · exact ⟨[1, 1, 1, 1, 2, 4], by decide⟩
    · exact ⟨[1, 1, 1, 2, 3, 3], by decide⟩
  obtain ⟨a, b, c, d, hfour⟩ := Nat.sum_four_squares (n - 26)
  let roots := [a, b, c, d].filter (· != 0)
  have hlen : roots.length ≤ 4 := List.length_filter_le _ _
  have hzero : 0 ∉ roots := by
    intro hz
    have := (List.mem_filter.mp hz).2
    simp at this
  have hsum : (roots.map (· ^ 2)).sum = n - 26 := by
    simpa [roots, sum_squares_filter_ne_zero, Nat.add_assoc] using hfour
  obtain ⟨pad, hpadlen, hpadzero, hpadsum⟩ := pad_twenty_six (6 - roots.length) (by omega)
    (by omega)
  refine ⟨roots ++ pad, ?_, by simpa [List.mem_append, hzero] using hpadzero, ?_⟩
  · rw [List.length_append, hpadlen]
    omega
  · rw [List.map_append, List.sum_append, hsum, hpadsum]
    omega

/-- **Sums of six and of eight nonzero squares.** Every integer $n \ge 20$ is a sum of $6$
squares of positive integers, and every integer $n \ge 22$ is a sum of $8$ squares of positive
integers.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Corollary 1, as extracted inside the Lemma 1
record (`integers-2026-A121-lem-1`). -/
public theorem sum_six_and_eight_nonzero_squares :
    (∀ n : ℕ, 20 ≤ n → ∃ a : Fin 6 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ∧
      ∀ n : ℕ, 22 ≤ n → ∃ a : Fin 8 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  constructor
  · intro n hn
    obtain ⟨l, hlen, hzero, hsum⟩ := sum_six_squares_list n hn
    exact fin_of_list l hlen hzero hsum
  · intro n hn
    obtain ⟨l, hlen, hzero, hsum⟩ := sum_six_squares_list (n - 2) (by omega)
    refine fin_of_list (1 :: 1 :: l) (by simp [hlen]) (by simpa using hzero) ?_
    simp only [List.map_cons, one_pow, List.sum_cons, hsum]
    omega

end MetaMathlibExt
