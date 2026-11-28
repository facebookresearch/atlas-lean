/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Dynamics.NExpansionGaps
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.IntervalCases

/-!
# Comparing ideal periodic points and their orbits

This file proves that the purely periodic points of the ideal period words
decrease as the word index grows: for `0 < α ≤ √N - 1`, if `x` and `y` in
`[α, α + 1]` have purely periodic `N`-expansions with period words `d_k` and
`d_ℓ`, then `x < y` if and only if `ℓ < k`. The proof compares the periodic
digit sequences: they agree below a first-difference index determined by the
smaller word index, and differ there in a way fixed by its parity; the
`N`-expansion map is expanding, so the order at the first difference
determines the order of the points, and equal digit sequences determine
equal points.

Each ideal periodic point is also the least point in its orbit: compare the
digit string of its word with each of its cyclic shifts.

## Main declarations

* `MetaMathlibExt.idealPeriodWord_point_lt_iff`: the ideal periodic points
  decrease (de Jonge, Lemma 4).
* `MetaMathlibExt.idealPeriodWord_point_le_orbit`: each ideal periodic point
  is the least in its orbit (de Jonge, Lemma 5).

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26
(2026), Article A75.
-/

namespace MetaMathlibExt

@[expose] public section


private theorem idealPeriodWord_point_lt_iff_add_five (n : ℕ) :
    idealPeriodWord (n + 5) =
      let w := idealPeriodWord (n + 4)
      if w.drop (w.length - 4) = [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] then
        w ++ w.take (w.length - 4) ++ [[2, 1, 1], [2, 2], [2, 2]]
      else if w.drop (w.length - 3) = [[2, 1, 1], [2, 2], [2, 2]] then
        w ++ w.take (w.length - 3) ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
      else w :=
  rfl

private theorem idealPeriodWord_point_lt_iff_add_five_of_abab {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) :
    idealPeriodWord (n + 5) = idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 2]] := by
  rw [idealPeriodWord_point_lt_iff_add_five]
  simp [h]

private theorem idealPeriodWord_point_lt_iff_add_five_of_abb {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) :
    idealPeriodWord (n + 5) =
      idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  have h4 : (idealPeriodWord (n + 4)).drop ((idealPeriodWord (n + 4)).length - 4) ≠
      [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
    rw [h]
    rcases List.eq_nil_or_concat j with rfl | ⟨L, x, rfl⟩
    · decide
    · simp
  rw [idealPeriodWord_point_lt_iff_add_five]
  simp only [h4, ite_false]
  simp [h]

private theorem idealPeriodWord_point_lt_iff_add_four_shape (k : ℕ) :
    (Even k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) ∧
      (Odd k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) := by
  induction k with
  | zero =>
    exact ⟨fun _ => ⟨[[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1],
      [2, 2], [2, 2]], rfl⟩, fun h => absurd h (by decide)⟩
  | succ k ih =>
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨j, hj⟩ := ih.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_point_lt_iff_add_five_of_abab hj⟩
    · obtain ⟨j, hj⟩ := ih.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_point_lt_iff_add_five_of_abb hj⟩

private theorem idealPeriodWord_point_lt_iff_word_rec_step (m : ℕ)
    (h2 : idealPeriodWord (m + 6) = idealPeriodWord (m + 5) ++ idealPeriodWord (m + 4) ++
      idealPeriodWord (m + 4))
    (h3 : idealPeriodWord (m + 7) = idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++
      idealPeriodWord (m + 5)) :
    idealPeriodWord (m + 8) = idealPeriodWord (m + 7) ++ idealPeriodWord (m + 6) ++
      idealPeriodWord (m + 6) := by
  rcases Nat.even_or_odd (m + 1) with hev | hodd
  · have hev3 : Even (m + 3) := by obtain ⟨r, hr⟩ := hev; exact ⟨r + 1, by omega⟩
    obtain ⟨j', hj'0⟩ := (idealPeriodWord_point_lt_iff_add_four_shape (m + 1)).1 hev
    obtain ⟨j, hj0⟩ := (idealPeriodWord_point_lt_iff_add_four_shape (m + 3)).1 hev3
    have hj' : idealPeriodWord (m + 5) = j' ++ [[2, 1, 1], [2, 2], [2, 2]] := hj'0
    have hj : idealPeriodWord (m + 7) = j ++ [[2, 1, 1], [2, 2], [2, 2]] := hj0
    have hW6 : idealPeriodWord (m + 6) =
        idealPeriodWord (m + 5) ++ j' ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] :=
      idealPeriodWord_point_lt_iff_add_five_of_abb hj'0
    have hW8 : idealPeriodWord (m + 8) =
        idealPeriodWord (m + 7) ++ j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] :=
      idealPeriodWord_point_lt_iff_add_five_of_abb hj0
    have hJ : j' ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] =
        idealPeriodWord (m + 4) ++ idealPeriodWord (m + 4) := by
      have e := hW6.symm.trans h2
      simp only [List.append_assoc] at e
      exact List.append_cancel_left e
    have hJid : idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j' = j := by
      have hS : (idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j') ++
          [[2, 1, 1], [2, 2], [2, 2]] = j ++ [[2, 1, 1], [2, 2], [2, 2]] := by
        have hL : (idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j') ++
            [[2, 1, 1], [2, 2], [2, 2]] =
              idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ idealPeriodWord (m + 5) := by
          simp only [← List.append_assoc, hj']
        rw [hL, ← h3, hj]
      exact List.append_cancel_right hS
    rw [hW8, ← hJid]
    simp only [List.append_assoc, hJ]
    have hfold : idealPeriodWord (m + 5) ++ (idealPeriodWord (m + 4) ++ idealPeriodWord (m + 4)) =
        idealPeriodWord (m + 6) := (List.append_assoc _ _ _).symm.trans h2.symm
    rw [hfold]
  · have hodd3 : Odd (m + 3) := by obtain ⟨r, hr⟩ := hodd; exact ⟨r + 1, by omega⟩
    obtain ⟨j', hj'0⟩ := (idealPeriodWord_point_lt_iff_add_four_shape (m + 1)).2 hodd
    obtain ⟨j, hj0⟩ := (idealPeriodWord_point_lt_iff_add_four_shape (m + 3)).2 hodd3
    have hj' : idealPeriodWord (m + 5) = j' ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := hj'0
    have hj : idealPeriodWord (m + 7) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := hj0
    have hW6 : idealPeriodWord (m + 6) =
        idealPeriodWord (m + 5) ++ j' ++ [[2, 1, 1], [2, 2], [2, 2]] :=
      idealPeriodWord_point_lt_iff_add_five_of_abab hj'0
    have hW8 : idealPeriodWord (m + 8) =
        idealPeriodWord (m + 7) ++ j ++ [[2, 1, 1], [2, 2], [2, 2]] :=
      idealPeriodWord_point_lt_iff_add_five_of_abab hj0
    have hJ : j' ++ [[2, 1, 1], [2, 2], [2, 2]] =
        idealPeriodWord (m + 4) ++ idealPeriodWord (m + 4) := by
      have e := hW6.symm.trans h2
      simp only [List.append_assoc] at e
      exact List.append_cancel_left e
    have hJid : idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j' = j := by
      have hS : (idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j') ++
          [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] =
            j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
        have hL : (idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ j') ++
            [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] =
              idealPeriodWord (m + 6) ++ idealPeriodWord (m + 5) ++ idealPeriodWord (m + 5) := by
          simp only [← List.append_assoc, hj']
        rw [hL, ← h3, hj]
      exact List.append_cancel_right hS
    rw [hW8, ← hJid]
    simp only [List.append_assoc, hJ]
    have hfold : idealPeriodWord (m + 5) ++ (idealPeriodWord (m + 4) ++ idealPeriodWord (m + 4)) =
        idealPeriodWord (m + 6) := (List.append_assoc _ _ _).symm.trans h2.symm
    rw [hfold]

/-- The word recursion: each ideal period word is the previous word followed by
two copies of the word before it. -/
private theorem idealPeriodWord_point_lt_iff_word_rec (n : ℕ) (hn : 1 ≤ n) :
    idealPeriodWord (n + 2) = idealPeriodWord (n + 1) ++ idealPeriodWord n ++
      idealPeriodWord n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide
    | k + 7, _ =>
      exact idealPeriodWord_point_lt_iff_word_rec_step (k + 1) (ih (k + 5) (by omega) (by omega))
        (ih (k + 6) (by omega) (by omega))

/-- The digit strings satisfy the same recursion. -/
private theorem idealPeriodWord_point_lt_iff_flatten_rec {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord (n + 2)).flatten = (idealPeriodWord (n + 1)).flatten ++
      (idealPeriodWord n).flatten ++ (idealPeriodWord n).flatten := by
  rw [idealPeriodWord_point_lt_iff_word_rec n hn, List.flatten_append, List.flatten_append]

/-- The digit strings have positive length. -/
private theorem idealPeriodWord_point_lt_iff_flatten_length_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (idealPeriodWord n).flatten.length := by
  have h := idealPeriodWord_flatten_length hn
  have hpos : (0 : ℤ) < 2 ^ (n + 1) - (-1) ^ n := by
    have h4n : (4 : ℕ) ≤ 2 ^ (n + 1) := by
      have hle := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 2 ≤ n + 1)
      simpa using hle
    have h4 : (4 : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast h4n
    rcases Nat.even_or_odd n with hev | hodd
    · rw [hev.neg_one_pow]
      linarith
    · rw [hodd.neg_one_pow]
      linarith
  have h2 : (0 : ℤ) < ((idealPeriodWord n).flatten.length : ℤ) := by rw [h]; exact hpos
  exact_mod_cast h2

/-- Lengths of digit strings satisfy the doubling recursion. -/
private theorem idealPeriodWord_point_lt_iff_flatten_length_rec {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord (n + 2)).flatten.length = (idealPeriodWord (n + 1)).flatten.length +
      2 * (idealPeriodWord n).flatten.length := by
  rw [idealPeriodWord_point_lt_iff_flatten_rec hn, List.length_append, List.length_append]
  omega

/-- Every digit string is a prefix of the next one. -/
private theorem idealPeriodWord_point_lt_iff_flatten_prefix {n m : ℕ} (hn : 1 ≤ n) (h : n ≤ m) :
    (idealPeriodWord n).flatten <+: (idealPeriodWord m).flatten := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m hm ih =>
    have hstep : (idealPeriodWord m).flatten <+: (idealPeriodWord (m + 1)).flatten := by
      rcases eq_or_ne m 1 with rfl | hne
      · exact ⟨[2, 2], by decide⟩
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        have hr := idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 1)
        refine ⟨(idealPeriodWord (k + 1)).flatten ++ (idealPeriodWord (k + 1)).flatten, ?_⟩
        rw [hr]
        simp [List.append_assoc]
    exact ih.trans hstep

/-- The `getD` of an append, on the left part. -/
private theorem idealPeriodWord_point_lt_iff_getD_append_left (l₁ l₂ : List ℕ) (i : ℕ)
    (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  have h2 : i < (l₁ ++ l₂).length := by simp only [List.length_append]; omega
  rw [← List.getElem_eq_getD (0 : ℕ) (h := h2), ← List.getElem_eq_getD (0 : ℕ) (h := h)]
  exact List.getElem_append_left h

/-- The `getD` of an append, on the right part. -/
private theorem idealPeriodWord_point_lt_iff_getD_append_right (l₁ l₂ : List ℕ) (i : ℕ)
    (h : l₁.length ≤ i)
    (h2 : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  have h3 : i - l₁.length < l₂.length := by simp only [List.length_append] at h2; omega
  rw [← List.getElem_eq_getD (0 : ℕ) (h := h2), ← List.getElem_eq_getD (0 : ℕ) (h := h3)]
  exact List.getElem_append_right h

/-- The `getD` of a prefix list. -/
private theorem idealPeriodWord_point_lt_iff_getD_of_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂)
    (i : ℕ) (hi : i < l₁.length) :
    l₂.getD i 0 = l₁.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  exact idealPeriodWord_point_lt_iff_getD_append_left l₁ t i hi

/-- The digit sequence of an ideal period word, as a natural number. -/
private def idealPeriodWord_point_lt_iff_dig (n i : ℕ) : ℕ :=
  (idealPeriodWord n).flatten.getD (i % (idealPeriodWord n).flatten.length) 0

private theorem idealPeriodWord_point_lt_iff_dig_of_lt {n m : ℕ} (hm : 1 ≤ m)
    (h : (idealPeriodWord n).flatten <+: (idealPeriodWord m).flatten) {i : ℕ}
    (hi : i < (idealPeriodWord n).flatten.length) :
    idealPeriodWord_point_lt_iff_dig m i = idealPeriodWord_point_lt_iff_dig n i := by
  have hpos : 0 < (idealPeriodWord m).flatten.length :=
    idealPeriodWord_point_lt_iff_flatten_length_pos hm
  have hle := h.length_le
  unfold idealPeriodWord_point_lt_iff_dig
  rw [Nat.mod_eq_of_lt (by omega : i < (idealPeriodWord m).flatten.length),
    Nat.mod_eq_of_lt hi]
  exact idealPeriodWord_point_lt_iff_getD_of_prefix h i hi

/-- The index of the first difference between the periodic digit sequences of
two distinct ideal period words, defined by `firstDiff 0 = 1` and
`firstDiff (n+1) = |d_{n+1}| + firstDiff n`. -/
private def idealPeriodWord_point_lt_iff_firstDiff : ℕ → ℕ
  | 0 => 1
  | n + 1 => (idealPeriodWord (n + 1)).flatten.length + idealPeriodWord_point_lt_iff_firstDiff n

/-- The first-difference index plus one is a digit length: `|d_{t+1}|` when `t`
is odd and `2|d_t|` when `t` is even. -/
private theorem idealPeriodWord_point_lt_iff_firstDiff_add_one {t : ℕ} (ht : 1 ≤ t) :
    (Odd t → idealPeriodWord_point_lt_iff_firstDiff t + 1 =
      (idealPeriodWord (t + 1)).flatten.length) ∧
    (Even t → idealPeriodWord_point_lt_iff_firstDiff t + 1 =
      2 * (idealPeriodWord t).flatten.length) := by
  induction t using Nat.strong_induction_on with
  | _ t iht =>
    rcases (by omega : t = 1 ∨ t = 2 ∨ 3 ≤ t) with rfl | rfl | ht3
    · exact ⟨fun _ => by decide, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h (by decide), fun _ => by decide⟩
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩
      have ih := iht (k + 1) (by omega) (by omega)
      have hlen : (idealPeriodWord (k + 3)).flatten.length =
          (idealPeriodWord (k + 2)).flatten.length + 2 * (idealPeriodWord (k + 1)).flatten.length :=
        idealPeriodWord_point_lt_iff_flatten_length_rec (by omega : 1 ≤ k + 1)
      have hlen2 : (idealPeriodWord (k + 3 + 1)).flatten.length =
          (idealPeriodWord (k + 3)).flatten.length + 2 * (idealPeriodWord (k + 2)).flatten.length :=
        idealPeriodWord_point_lt_iff_flatten_length_rec (by omega : 1 ≤ k + 2)
      have e1 : idealPeriodWord_point_lt_iff_firstDiff (k + 3) =
          (idealPeriodWord (k + 3)).flatten.length +
            idealPeriodWord_point_lt_iff_firstDiff (k + 2) := rfl
      have e2 : idealPeriodWord_point_lt_iff_firstDiff (k + 2) =
          (idealPeriodWord (k + 2)).flatten.length +
            idealPeriodWord_point_lt_iff_firstDiff (k + 1) := rfl
      rw [e1, e2]
      constructor
      · intro hodd
        have hodd1 : Odd (k + 1) := by obtain ⟨r, hr⟩ := hodd; exact ⟨r - 1, by omega⟩
        have h1 : idealPeriodWord_point_lt_iff_firstDiff (k + 1) + 1 =
            (idealPeriodWord (k + 2)).flatten.length := ih.1 hodd1
        omega
      · intro hev
        have hev1 : Even (k + 1) := by obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩
        have h1 : idealPeriodWord_point_lt_iff_firstDiff (k + 1) + 1 =
            2 * (idealPeriodWord (k + 1)).flatten.length := ih.2 hev1
        omega

/-- Digit string lengths are odd. -/
private theorem idealPeriodWord_point_lt_iff_flatten_length_odd {n : ℕ} (hn : 1 ≤ n) :
    Odd (idealPeriodWord n).flatten.length := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    match n, hn with
    | 1, _ => decide
    | k + 2, _ =>
      have h := idealPeriodWord_point_lt_iff_flatten_length_rec (by omega : 1 ≤ k + 1)
      rw [h]
      exact ih.add_even ⟨(idealPeriodWord (k + 1)).flatten.length, by omega⟩

/-- The first-difference index is below the next digit length and below twice
the digit length. -/
private theorem idealPeriodWord_point_lt_iff_firstDiff_lt {t : ℕ} (ht : 1 ≤ t) :
    idealPeriodWord_point_lt_iff_firstDiff t < (idealPeriodWord (t + 1)).flatten.length ∧
      idealPeriodWord_point_lt_iff_firstDiff t < 2 * (idealPeriodWord t).flatten.length := by
  induction t using Nat.strong_induction_on with
  | _ t iht =>
    rcases (by omega : t = 1 ∨ t = 2 ∨ 3 ≤ t) with rfl | rfl | ht3
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩
      have ih1 : idealPeriodWord_point_lt_iff_firstDiff (k + 2) <
          (idealPeriodWord (k + 3)).flatten.length ∧
            idealPeriodWord_point_lt_iff_firstDiff (k + 2) <
              2 * (idealPeriodWord (k + 2)).flatten.length := iht (k + 2) (by omega) (by omega)
      have ih2 : idealPeriodWord_point_lt_iff_firstDiff (k + 1) <
          (idealPeriodWord (k + 2)).flatten.length ∧
            idealPeriodWord_point_lt_iff_firstDiff (k + 1) <
              2 * (idealPeriodWord (k + 1)).flatten.length := iht (k + 1) (by omega) (by omega)
      have hlen : (idealPeriodWord (k + 3 + 1)).flatten.length =
          (idealPeriodWord (k + 3)).flatten.length + 2 * (idealPeriodWord (k + 2)).flatten.length :=
        idealPeriodWord_point_lt_iff_flatten_length_rec (by omega : 1 ≤ k + 2)
      have e1 : idealPeriodWord_point_lt_iff_firstDiff (k + 3) =
          (idealPeriodWord (k + 3)).flatten.length +
            idealPeriodWord_point_lt_iff_firstDiff (k + 2) := rfl
      have e2 : idealPeriodWord_point_lt_iff_firstDiff (k + 2) =
          (idealPeriodWord (k + 2)).flatten.length +
            idealPeriodWord_point_lt_iff_firstDiff (k + 1) := rfl
      omega

/-- The first-difference index is even exactly for odd indices. -/
private theorem idealPeriodWord_point_lt_iff_firstDiff_parity {t : ℕ} (ht : 1 ≤ t) :
    Even (idealPeriodWord_point_lt_iff_firstDiff t) ↔ Odd t := by
  have h := idealPeriodWord_point_lt_iff_firstDiff_add_one ht
  have hodd : Odd (idealPeriodWord (t + 1)).flatten.length :=
    idealPeriodWord_point_lt_iff_flatten_length_odd (by omega)
  constructor
  · intro hev
    rcases Nat.even_or_odd t with hev2 | hodd2
    · have h2 := h.2 hev2
      obtain ⟨r, hr⟩ := hev
      exfalso
      omega
    · exact hodd2
  · intro hodd2
    have h1 := h.1 hodd2
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r, by omega⟩

/-- Shift identity for the smaller index: past the first two blocks of the
digit string, the sequence of `s = k+3` continues as the sequence of `k+1`. -/
private theorem idealPeriodWord_point_lt_iff_dig_shift_left {k : ℕ} (hk : 1 ≤ k) {i : ℕ}
    (hi : i ≤ idealPeriodWord_point_lt_iff_firstDiff k) :
    idealPeriodWord_point_lt_iff_dig (k + 3)
        ((idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
          (idealPeriodWord (k + 1)).flatten.length + i) =
      idealPeriodWord_point_lt_iff_dig (k + 1) i := by
  have hDs : (idealPeriodWord (k + 3)).flatten =
      (idealPeriodWord (k + 2)).flatten ++ (idealPeriodWord (k + 1)).flatten ++
        (idealPeriodWord (k + 1)).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 1)
  have hDa : (idealPeriodWord (k + 2)).flatten =
      (idealPeriodWord (k + 1)).flatten ++ (idealPeriodWord k).flatten ++
        (idealPeriodWord k).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec hk
  have hLs : (idealPeriodWord (k + 3)).flatten.length =
      (idealPeriodWord (k + 2)).flatten.length + 2 * (idealPeriodWord (k + 1)).flatten.length := by
    rw [hDs]; simp only [List.length_append]; omega
  have hLa : (idealPeriodWord (k + 2)).flatten.length =
      (idealPeriodWord (k + 1)).flatten.length + 2 * (idealPeriodWord k).flatten.length := by
    rw [hDa]; simp only [List.length_append]; omega
  have hlt := idealPeriodWord_point_lt_iff_firstDiff_lt hk
  have hpos : 0 < (idealPeriodWord (k + 1)).flatten.length :=
    idealPeriodWord_point_lt_iff_flatten_length_pos (by omega)
  have hmod : ((idealPeriodWord (k + 3)).flatten.length +
        (idealPeriodWord (k + 2)).flatten.length + (idealPeriodWord (k + 1)).flatten.length + i) %
        (idealPeriodWord (k + 3)).flatten.length =
      (idealPeriodWord (k + 2)).flatten.length + (idealPeriodWord (k + 1)).flatten.length + i := by
    rw [show (idealPeriodWord (k + 3)).flatten.length +
        (idealPeriodWord (k + 2)).flatten.length + (idealPeriodWord (k + 1)).flatten.length + i =
        (idealPeriodWord (k + 3)).flatten.length +
          ((idealPeriodWord (k + 2)).flatten.length
            + (idealPeriodWord (k + 1)).flatten.length + i) from by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  unfold idealPeriodWord_point_lt_iff_dig
  rw [hmod, hDs, List.append_assoc]
  have h1 : (idealPeriodWord (k + 2)).flatten.length ≤
      (idealPeriodWord (k + 2)).flatten.length
        + (idealPeriodWord (k + 1)).flatten.length + i := by omega
  have h2 : (idealPeriodWord (k + 2)).flatten.length
    + (idealPeriodWord (k + 1)).flatten.length + i <
      ((idealPeriodWord (k + 2)).flatten ++
        ((idealPeriodWord (k + 1)).flatten ++ (idealPeriodWord (k + 1)).flatten)).length := by
    simp only [List.length_append]; omega
  rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ h1 h2]
  have h3 : (idealPeriodWord (k + 2)).flatten.length
    + (idealPeriodWord (k + 1)).flatten.length + i -
      (idealPeriodWord (k + 2)).flatten.length =
        (idealPeriodWord (k + 1)).flatten.length + i := by omega
  rw [h3, idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
    (by simp only [List.length_append]; omega)]
  have h4 : (idealPeriodWord (k + 1)).flatten.length + i -
      (idealPeriodWord (k + 1)).flatten.length = i := by omega
  rw [h4]
  have h5 : i < (idealPeriodWord (k + 1)).flatten.length := by omega
  rw [Nat.mod_eq_of_lt h5]

/-- Shift identity for the larger index: past the same point, the sequence of
any larger `m` continues as the sequence of `k`. -/
private theorem idealPeriodWord_point_lt_iff_dig_shift_right {k m : ℕ} (hk : 1 ≤ k)
    (hms : k + 3 < m) {i : ℕ}
    (hi : i ≤ idealPeriodWord_point_lt_iff_firstDiff k) :
    idealPeriodWord_point_lt_iff_dig m
        ((idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
          (idealPeriodWord (k + 1)).flatten.length + i) =
      idealPeriodWord_point_lt_iff_dig k i := by
  have hDs : (idealPeriodWord (k + 3)).flatten =
      (idealPeriodWord (k + 2)).flatten ++ (idealPeriodWord (k + 1)).flatten ++
        (idealPeriodWord (k + 1)).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 1)
  have hDa : (idealPeriodWord (k + 2)).flatten =
      (idealPeriodWord (k + 1)).flatten ++ (idealPeriodWord k).flatten ++
        (idealPeriodWord k).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec hk
  have hD4 : (idealPeriodWord (k + 4)).flatten =
      (idealPeriodWord (k + 3)).flatten ++ (idealPeriodWord (k + 2)).flatten ++
        (idealPeriodWord (k + 2)).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 2)
  have hLs : (idealPeriodWord (k + 3)).flatten.length =
      (idealPeriodWord (k + 2)).flatten.length + 2 * (idealPeriodWord (k + 1)).flatten.length := by
    rw [hDs]; simp only [List.length_append]; omega
  have hLa : (idealPeriodWord (k + 2)).flatten.length =
      (idealPeriodWord (k + 1)).flatten.length + 2 * (idealPeriodWord k).flatten.length := by
    rw [hDa]; simp only [List.length_append]; omega
  have hL4 : (idealPeriodWord (k + 4)).flatten.length =
      (idealPeriodWord (k + 3)).flatten.length + 2 * (idealPeriodWord (k + 2)).flatten.length := by
    rw [hD4]; simp only [List.length_append]; omega
  have hlt := idealPeriodWord_point_lt_iff_firstDiff_lt hk
  have hpre : (idealPeriodWord (k + 4)).flatten <+: (idealPeriodWord m).flatten :=
    idealPeriodWord_point_lt_iff_flatten_prefix (by omega) (by omega)
  have hle := hpre.length_le
  have hpos : 0 < (idealPeriodWord k).flatten.length :=
    idealPeriodWord_point_lt_iff_flatten_length_pos hk
  -- the index is below the length of `m`'s digit string
  have hltm : (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
      (idealPeriodWord (k + 1)).flatten.length + i < (idealPeriodWord m).flatten.length := by omega
  have hmod : ((idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i) % (idealPeriodWord m).flatten.length =
      (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i := Nat.mod_eq_of_lt hltm
  unfold idealPeriodWord_point_lt_iff_dig
  rw [hmod]
  have hget : (idealPeriodWord m).flatten.getD
      ((idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i) 0 =
      (idealPeriodWord (k + 4)).flatten.getD
      ((idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i) 0 :=
    idealPeriodWord_point_lt_iff_getD_of_prefix hpre _ (by omega)
  rw [hget, hD4, List.append_assoc]
  have h1 : (idealPeriodWord (k + 3)).flatten.length ≤
      (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i := by omega
  have h2 : (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i <
      ((idealPeriodWord (k + 3)).flatten ++
        ((idealPeriodWord (k + 2)).flatten ++ (idealPeriodWord (k + 2)).flatten)).length := by
    simp only [List.length_append]; omega
  rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ h1 h2]
  have hidx : (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
        (idealPeriodWord (k + 1)).flatten.length + i - (idealPeriodWord (k + 3)).flatten.length =
      (idealPeriodWord (k + 2)).flatten.length
        + (idealPeriodWord (k + 1)).flatten.length + i := by omega
  rw [hidx]
  have hidx2 : (idealPeriodWord (k + 2)).flatten.length +
    (idealPeriodWord (k + 1)).flatten.length + i -
      (idealPeriodWord (k + 2)).flatten.length =
        (idealPeriodWord (k + 1)).flatten.length + i := by omega
  rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega) (by
    simp only [List.length_append]; omega)]
  rw [hidx2, hDa, List.append_assoc]
  have hidx3 : (idealPeriodWord (k + 1)).flatten.length + i -
      (idealPeriodWord (k + 1)).flatten.length = i := by omega
  rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega) (by
    simp only [List.length_append]; omega), hidx3]
  -- now the index lies in two copies of the `k` digit string
  by_cases hiLc : i < (idealPeriodWord k).flatten.length
  · rw [idealPeriodWord_point_lt_iff_getD_append_left _ _ _ hiLc, Nat.mod_eq_of_lt hiLc]
  · have hi2 : i < 2 * (idealPeriodWord k).flatten.length := by omega
    rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
      (by simp only [List.length_append]; omega)]
    have hmod2 : i % (idealPeriodWord k).flatten.length =
        i - (idealPeriodWord k).flatten.length := by
      conv_lhs => rw [show i = (idealPeriodWord k).flatten.length +
        (i - (idealPeriodWord k).flatten.length) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod2]

/-- Below the shift point, the sequences of `k+3` and any larger `m` agree. -/
private theorem idealPeriodWord_point_lt_iff_dig_agree_below {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hms : k + 3 < m) {i : ℕ}
    (hi : i < (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
      (idealPeriodWord (k + 1)).flatten.length) :
    idealPeriodWord_point_lt_iff_dig (k + 3) i = idealPeriodWord_point_lt_iff_dig m i := by
  have hDs : (idealPeriodWord (k + 3)).flatten =
      (idealPeriodWord (k + 2)).flatten ++ (idealPeriodWord (k + 1)).flatten ++
        (idealPeriodWord (k + 1)).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 1)
  have hDa : (idealPeriodWord (k + 2)).flatten =
      (idealPeriodWord (k + 1)).flatten ++ (idealPeriodWord k).flatten ++
        (idealPeriodWord k).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec hk
  have hD4 : (idealPeriodWord (k + 4)).flatten =
      (idealPeriodWord (k + 3)).flatten ++ (idealPeriodWord (k + 2)).flatten ++
        (idealPeriodWord (k + 2)).flatten :=
    idealPeriodWord_point_lt_iff_flatten_rec (by omega : 1 ≤ k + 2)
  have hLs : (idealPeriodWord (k + 3)).flatten.length =
      (idealPeriodWord (k + 2)).flatten.length + 2 * (idealPeriodWord (k + 1)).flatten.length := by
    rw [hDs]; simp only [List.length_append]; omega
  have hLa : (idealPeriodWord (k + 2)).flatten.length =
      (idealPeriodWord (k + 1)).flatten.length + 2 * (idealPeriodWord k).flatten.length := by
    rw [hDa]; simp only [List.length_append]; omega
  have hL4 : (idealPeriodWord (k + 4)).flatten.length =
      (idealPeriodWord (k + 3)).flatten.length + 2 * (idealPeriodWord (k + 2)).flatten.length := by
    rw [hD4]; simp only [List.length_append]; omega
  have hpre : (idealPeriodWord (k + 4)).flatten <+: (idealPeriodWord m).flatten :=
    idealPeriodWord_point_lt_iff_flatten_prefix (by omega) (by omega)
  have e1 : idealPeriodWord_point_lt_iff_dig m i =
      idealPeriodWord_point_lt_iff_dig (k + 4) i :=
    idealPeriodWord_point_lt_iff_dig_of_lt hm hpre (by omega)
  rw [e1]
  unfold idealPeriodWord_point_lt_iff_dig
  rw [Nat.mod_eq_of_lt (show i < (idealPeriodWord (k + 4)).flatten.length from by omega)]
  by_cases h1 : i < (idealPeriodWord (k + 3)).flatten.length
  · rw [Nat.mod_eq_of_lt h1, hD4, List.append_assoc]
    exact (idealPeriodWord_point_lt_iff_getD_append_left _ _ _ h1).symm
  · have hsub : i % (idealPeriodWord (k + 3)).flatten.length =
        i - (idealPeriodWord (k + 3)).flatten.length := by
      conv_lhs => rw [show i = (idealPeriodWord (k + 3)).flatten.length +
        (i - (idealPeriodWord (k + 3)).flatten.length) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    set j := i - (idealPeriodWord (k + 3)).flatten.length with hjdef
    rw [hDs, List.append_assoc, hD4, List.append_assoc]
    by_cases h2 : j < (idealPeriodWord (k + 2)).flatten.length
    · rw [idealPeriodWord_point_lt_iff_getD_append_left _ _ _ h2]
      rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
        (by simp only [List.length_append]; omega)]
      rw [idealPeriodWord_point_lt_iff_getD_append_left _ _ _ h2]
    · rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
      (by simp only [List.length_append]; omega)]
      rw [idealPeriodWord_point_lt_iff_getD_append_left _ _ _ (by omega)]
      rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
        (by simp only [List.length_append]; omega)]
      rw [idealPeriodWord_point_lt_iff_getD_append_right _ _ _ (by omega)
        (by simp only [List.length_append]; omega)]
      have hidx3 : i - (idealPeriodWord (k + 3)).flatten.length -
          (idealPeriodWord (k + 2)).flatten.length =
          j - (idealPeriodWord (k + 2)).flatten.length := by omega
      rw [hidx3, hDa, List.append_assoc,
        idealPeriodWord_point_lt_iff_getD_append_left _ _ _
          (by simp only [List.length_append]; omega)]

/-- The periodic digit sequences of two distinct ideal period words agree
below the first-difference index, and differ there with the values determined
by the parity of the smaller index. -/
private theorem idealPeriodWord_point_lt_iff_dig_compare : ∀ s : ℕ, 1 ≤ s → ∀ m : ℕ, s < m →
    (∀ i, i < idealPeriodWord_point_lt_iff_firstDiff s →
      idealPeriodWord_point_lt_iff_dig s i = idealPeriodWord_point_lt_iff_dig m i) ∧
    idealPeriodWord_point_lt_iff_dig s (idealPeriodWord_point_lt_iff_firstDiff s) =
      (if Odd s then 1 else 2) ∧
    idealPeriodWord_point_lt_iff_dig m (idealPeriodWord_point_lt_iff_firstDiff s) =
      (if Odd s then 2 else 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs m hm
    rcases (by omega : s = 1 ∨ s = 2 ∨ s = 3 ∨ 4 ≤ s) with rfl | rfl | rfl | hs4
    · have hp : idealPeriodWord_point_lt_iff_firstDiff 1 = 6 := rfl
      have hpre : (idealPeriodWord 2).flatten <+: (idealPeriodWord m).flatten :=
        idealPeriodWord_point_lt_iff_flatten_prefix (by norm_num) (by omega)
      have hlen2 : (idealPeriodWord 2).flatten.length = 7 := by decide
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hp] at hi
        have e : idealPeriodWord_point_lt_iff_dig m i = idealPeriodWord_point_lt_iff_dig 2 i :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        interval_cases i <;> decide
      · rw [hp, ite_eq_left (by decide : Odd 1)]
        decide
      · rw [hp, ite_eq_left (by decide : Odd 1)]
        have e : idealPeriodWord_point_lt_iff_dig m 6 = idealPeriodWord_point_lt_iff_dig 2 6 :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        decide
    · have hp : idealPeriodWord_point_lt_iff_firstDiff 2 = 13 := rfl
      have hpre : (idealPeriodWord 3).flatten <+: (idealPeriodWord m).flatten :=
        idealPeriodWord_point_lt_iff_flatten_prefix (by norm_num) (by omega)
      have hlen3 : (idealPeriodWord 3).flatten.length = 17 := by decide
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hp] at hi
        have e : idealPeriodWord_point_lt_iff_dig m i = idealPeriodWord_point_lt_iff_dig 3 i :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        interval_cases i <;> decide
      · rw [hp, ite_eq_right (by decide : ¬ Odd 2)]
        decide
      · rw [hp, ite_eq_right (by decide : ¬ Odd 2)]
        have e : idealPeriodWord_point_lt_iff_dig m 13 = idealPeriodWord_point_lt_iff_dig 3 13 :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        decide
    · have hp : idealPeriodWord_point_lt_iff_firstDiff 3 = 30 := rfl
      have hpre : (idealPeriodWord 4).flatten <+: (idealPeriodWord m).flatten :=
        idealPeriodWord_point_lt_iff_flatten_prefix (by norm_num) (by omega)
      have hlen4 : (idealPeriodWord 4).flatten.length = 31 := by decide
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hp] at hi
        have e : idealPeriodWord_point_lt_iff_dig m i = idealPeriodWord_point_lt_iff_dig 4 i :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        interval_cases i <;> decide
      · rw [hp, ite_eq_left (by decide : Odd 3)]
        decide
      · rw [hp, ite_eq_left (by decide : Odd 3)]
        have e : idealPeriodWord_point_lt_iff_dig m 30 = idealPeriodWord_point_lt_iff_dig 4 30 :=
          idealPeriodWord_point_lt_iff_dig_of_lt (by omega) hpre (by omega)
        rw [e]
        decide
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
      have hk : 1 ≤ k := by omega
      have ihk := ih k (by omega) hk (k + 1) (by omega)
      obtain ⟨ihagree, ihval1, ihval2⟩ := ihk
      have hp1 : idealPeriodWord_point_lt_iff_firstDiff (k + 3) =
          (idealPeriodWord (k + 3)).flatten.length
            + idealPeriodWord_point_lt_iff_firstDiff (k + 2) := rfl
      have hp2 : idealPeriodWord_point_lt_iff_firstDiff (k + 2) =
          (idealPeriodWord (k + 2)).flatten.length
            + idealPeriodWord_point_lt_iff_firstDiff (k + 1) := rfl
      have hp3 : idealPeriodWord_point_lt_iff_firstDiff (k + 1) =
          (idealPeriodWord (k + 1)).flatten.length + idealPeriodWord_point_lt_iff_firstDiff k := rfl
      have hp_eq : idealPeriodWord_point_lt_iff_firstDiff (k + 3) =
          (idealPeriodWord (k + 3)).flatten.length + (idealPeriodWord (k + 2)).flatten.length +
            (idealPeriodWord (k + 1)).flatten.length
              + idealPeriodWord_point_lt_iff_firstDiff k := by
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hp_eq] at hi
        by_cases hlt : i < (idealPeriodWord (k + 3)).flatten.length +
            (idealPeriodWord (k + 2)).flatten.length + (idealPeriodWord (k + 1)).flatten.length
        · exact idealPeriodWord_point_lt_iff_dig_agree_below hk (by omega) (by omega) hlt
        · obtain ⟨t, rfl⟩ : ∃ t, i = (idealPeriodWord (k + 3)).flatten.length +
              (idealPeriodWord (k + 2)).flatten.length
                + (idealPeriodWord (k + 1)).flatten.length + t :=
            ⟨i - ((idealPeriodWord (k + 3)).flatten.length +
              (idealPeriodWord (k + 2)).flatten.length +
              (idealPeriodWord (k + 1)).flatten.length), by omega⟩
          have ht : t < idealPeriodWord_point_lt_iff_firstDiff k := by omega
          have hms' : k + 3 < m := hm
          rw [idealPeriodWord_point_lt_iff_dig_shift_left hk (le_of_lt ht),
            idealPeriodWord_point_lt_iff_dig_shift_right hk hms' (le_of_lt ht)]
          exact (ihagree t ht).symm
      · have hms' : k + 3 < m := hm
        rw [hp_eq, idealPeriodWord_point_lt_iff_dig_shift_left hk le_rfl]
        have hpar : Odd (k + 3) ↔ Even k := by
          constructor
          · intro h
            obtain ⟨r, hr⟩ := h
            exact ⟨r - 1, by omega⟩
          · intro h
            obtain ⟨r, hr⟩ := h
            exact ⟨r + 1, by omega⟩
        rcases Nat.even_or_odd k with hkev | hkodd
        · have hsodd : Odd (k + 3) := hpar.mpr hkev
          have hknot : ¬ Odd k := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hkev
            omega
          rw [ite_eq_right hknot] at ihval2
          rw [ite_eq_left hsodd]
          exact ihval2
        · have hseven : ¬ Even k := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hkodd
            omega
          have hsnot : ¬ Odd (k + 3) := fun h => hseven (hpar.mp h)
          rw [ite_eq_left hkodd] at ihval2
          rw [ite_eq_right hsnot]
          exact ihval2
      · have hms' : k + 3 < m := hm
        rw [hp_eq, idealPeriodWord_point_lt_iff_dig_shift_right hk hms' le_rfl]
        have hpar : Odd (k + 3) ↔ Even k := by
          constructor
          · intro h
            obtain ⟨r, hr⟩ := h
            exact ⟨r - 1, by omega⟩
          · intro h
            obtain ⟨r, hr⟩ := h
            exact ⟨r + 1, by omega⟩
        rcases Nat.even_or_odd k with hkev | hkodd
        · have hsodd : Odd (k + 3) := hpar.mpr hkev
          have hknot : ¬ Odd k := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hkev
            omega
          rw [ite_eq_right hknot] at ihval1
          rw [ite_eq_left hsodd]
          exact ihval1
        · have hseven : ¬ Even k := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hkodd
            omega
          have hsnot : ¬ Odd (k + 3) := fun h => hseven (hpar.mp h)
          rw [ite_eq_left hkodd] at ihval1
          rw [ite_eq_right hsnot]
          exact ihval1

/-- The N-expansion map never takes a value below `α`. -/
private theorem idealPeriodWord_point_lt_iff_le_map (N : ℕ) (α x : ℝ) :
    α ≤ nExpansionMap N α x := by
  have hd : nExpansionDigit N α x ≤ ⌊(N : ℝ) / x - α⌋ := by
    unfold nExpansionDigit
    split_ifs <;> omega
  have h : (nExpansionDigit N α x : ℝ) ≤ (N : ℝ) / x - α :=
    (Int.cast_le.mpr hd).trans (Int.floor_le _)
  rw [nExpansionMap]
  linarith

/-- For `α > 0`, the orbit of a positive point stays positive. -/
private theorem idealPeriodWord_point_lt_iff_iterate_pos {N : ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (j : ℕ) : 0 < (nExpansionMap N α)^[j] x := by
  cases j with
  | zero => exact hx
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact hα.trans_le (idealPeriodWord_point_lt_iff_le_map N α _)

/-- The N-expansion map sends `I_α` to itself, when `α ≤ √N - 1`. -/
private theorem idealPeriodWord_point_lt_iff_map_mem_Icc {N : ℕ} {α : ℝ} (_hα : 0 < α)
    (_hαN : α ≤ Real.sqrt N - 1) {x : ℝ} (_hx : x ∈ Set.Icc α (α + 1)) :
    nExpansionMap N α x ∈ Set.Icc α (α + 1) := by
  refine ⟨idealPeriodWord_point_lt_iff_le_map N α x, ?_⟩
  by_cases hxα : x = α
  · rw [hxα]
    by_cases hint : ∃ k : ℤ, (N : ℝ) / α - α = k
    · obtain ⟨k, hk⟩ := hint
      rw [nExpansionMap_self_of_int hk]
    · have hd : nExpansionDigit N α α = ⌊(N : ℝ) / α - α⌋ := by
        simp [nExpansionDigit, hint]
      have hT : nExpansionMap N α α = α + Int.fract ((N : ℝ) / α - α) := by
        rw [nExpansionMap, hd, Int.fract]
        ring
      rw [hT]
      have := Int.fract_lt_one ((N : ℝ) / α - α)
      linarith [Int.fract_nonneg ((N : ℝ) / α - α)]
  · have h := nExpansionMap_mem_Ico_of_ne (N := N) hxα
    exact h.2.le

/-- Iterates of the N-expansion map stay in `I_α`. -/
private theorem idealPeriodWord_point_lt_iff_iterate_mem_Icc {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1)) (j : ℕ) :
    (nExpansionMap N α)^[j] x ∈ Set.Icc α (α + 1) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact idealPeriodWord_point_lt_iff_map_mem_Icc hα hαN ih

/-- The digit of a point of `I_α` is nonnegative. -/
private theorem idealPeriodWord_point_lt_iff_digit_nonneg {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1)) :
    0 ≤ nExpansionDigit N α x := by
  have hx0 : 0 < x := hα.trans_le hx.1
  have hNα : (α + 1) * (α + 1) ≤ (N : ℝ) := by
    have h1 : (0 : ℝ) ≤ α + 1 := by linarith
    have h2 : α + 1 ≤ Real.sqrt N := by linarith
    calc (α + 1) * (α + 1) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul h2 h2 h1 (by positivity)
    _ = (N : ℝ) := Real.mul_self_sqrt (by positivity)
  have hge : (1 : ℝ) ≤ (N : ℝ) / x - α := by
    have h3 : (N : ℝ) / (α + 1) ≥ α + 1 := by
      rw [ge_iff_le, le_div_iff₀ (by linarith : (0:ℝ) < α + 1)]
      linarith [hNα]
    have h4 : (N : ℝ) / (α + 1) ≤ (N : ℝ) / x := by
      apply div_le_div_of_nonneg_left (by positivity) hx0 hx.2
    linarith
  have hf : 1 ≤ ⌊(N : ℝ) / x - α⌋ := by
    apply Int.le_floor.mpr
    exact_mod_cast hge
  unfold nExpansionDigit
  split_ifs <;> omega

/-- Orbits with the same digits alternate in order, for a single parameter. -/
private theorem idealPeriodWord_point_lt_iff_iterate_lt_iff {N : ℕ} (hN : 0 < N) {α x y : ℝ}
    (hα : 0 < α) (hx : 0 < x) (hxy : x < y) (m : ℕ)
    (hd : ∀ j < m, nExpansionDigit N α ((nExpansionMap N α)^[j] x) =
      nExpansionDigit N α ((nExpansionMap N α)^[j] y)) :
    ((nExpansionMap N α)^[m] y < (nExpansionMap N α)^[m] x ↔ Odd m) ∧
      ((nExpansionMap N α)^[m] x < (nExpansionMap N α)^[m] y ↔ Even m) := by
  induction m with
  | zero =>
    have hodd0 : ¬ Odd (0 : ℕ) := by decide
    have hev0 : Even (0 : ℕ) := ⟨0, rfl⟩
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
    exact ⟨iff_of_false (not_lt_of_gt hxy) hodd0, iff_of_true hxy hev0⟩
  | succ m ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun j hj => hd j (by omega)
    have hy := idealPeriodWord_point_lt_iff_iterate_pos (N := N) hα hx m
    have hy' := idealPeriodWord_point_lt_iff_iterate_pos (N := N) hα (hx.trans hxy) m
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', nExpansionMap,
      nExpansionMap, hd m (by omega), sub_lt_sub_iff_right, sub_lt_sub_iff_right,
      div_lt_div_iff_of_pos_left hN' hy hy', div_lt_div_iff_of_pos_left hN' hy' hy, ih₁, ih₂,
      Nat.odd_add_one, Nat.even_add_one, Nat.not_odd_iff_even, Nat.not_even_iff_odd]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- If the digit at step `m` of `x` is smaller than that of `y`, then the
`m`-th iterate of `y` is below the `m`-th iterate of `x`. -/
private theorem idealPeriodWord_point_lt_iff_iterate_lt_of_digit_lt {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hαN : α ≤ Real.sqrt N - 1) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1)) {m : ℕ}
    (hdm : nExpansionDigit N α ((nExpansionMap N α)^[m] x) <
      nExpansionDigit N α ((nExpansionMap N α)^[m] y)) :
    (nExpansionMap N α)^[m] y < (nExpansionMap N α)^[m] x := by
  have hmemx := idealPeriodWord_point_lt_iff_iterate_mem_Icc hα hαN hx m
  have hmemy := idealPeriodWord_point_lt_iff_iterate_mem_Icc hα hαN hy m
  have hmemx1 := idealPeriodWord_point_lt_iff_map_mem_Icc hα hαN hmemx
  have hmemy1 := idealPeriodWord_point_lt_iff_map_mem_Icc hα hαN hmemy
  set u := (nExpansionMap N α)^[m] x with hu_def
  set v := (nExpansionMap N α)^[m] y with hv_def
  have hu0 : 0 < u := hα.trans_le hmemx.1
  have hv0 : 0 < v := hα.trans_le hmemy.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  -- the inverse formula: `u = N / (digit u + T u)`
  have key : ∀ z : ℝ, z ∈ Set.Icc α (α + 1) →
      z = (N : ℝ) / ((nExpansionDigit N α z : ℝ) + nExpansionMap N α z) := by
    intro z hz
    have hz0 : 0 < z := hα.trans_le hz.1
    have hD : (0 : ℝ) < (nExpansionDigit N α z : ℝ) + nExpansionMap N α z := by
      have h : (nExpansionDigit N α z : ℝ) + nExpansionMap N α z = (N : ℝ) / z := by
        rw [nExpansionMap]; ring
      rw [h]
      positivity
    rw [eq_div_iff (ne_of_gt hD)]
    have h : (nExpansionDigit N α z : ℝ) + nExpansionMap N α z = (N : ℝ) / z := by
      rw [nExpansionMap]; ring
    rw [h]
    field_simp
  have hu := key u hmemx
  have hv := key v hmemy
  have hle : (nExpansionDigit N α u : ℝ) + nExpansionMap N α u ≤
      (nExpansionDigit N α v : ℝ) + nExpansionMap N α v := by
    have hd1 : (nExpansionDigit N α u : ℝ) + 1 ≤ nExpansionDigit N α v := by
      exact_mod_cast (by omega : nExpansionDigit N α u + 1 ≤ nExpansionDigit N α v)
    linarith [hmemx1.2, hmemy1.1]
  have hle' : v ≤ u := by
    rw [hv, hu]
    apply div_le_div_of_nonneg_left (by positivity) (by
      have hD : (0 : ℝ) < (nExpansionDigit N α u : ℝ) + nExpansionMap N α u := by
        have h : (nExpansionDigit N α u : ℝ) + nExpansionMap N α u = (N : ℝ) / u := by
          rw [nExpansionMap]; ring
        rw [h]; positivity
      exact hD) hle
  have hne : v ≠ u := by
    intro h
    rw [← h] at hdm
    exact lt_irrefl _ hdm
  exact lt_of_le_of_ne hle' hne

/-- From a first difference of digits, the order of the points is determined
by the parity of the difference index and the direction of the digit
inequality. -/
private theorem idealPeriodWord_point_lt_iff_lt_of_first_diff {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hαN : α ≤ Real.sqrt N - 1) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1)) {m : ℕ}
    (hdlt : ∀ j < m, nExpansionDigit N α ((nExpansionMap N α)^[j] x) =
      nExpansionDigit N α ((nExpansionMap N α)^[j] y))
    (hdm : nExpansionDigit N α ((nExpansionMap N α)^[m] x) <
      nExpansionDigit N α ((nExpansionMap N α)^[m] y)) :
    (Odd m → x < y) ∧ (Even m → y < x) := by
  have hlt4 := idealPeriodWord_point_lt_iff_iterate_lt_of_digit_lt hN hα hαN hx hy hdm
  have hx0 : 0 < x := hα.trans_le hx.1
  have hy0 : 0 < y := hα.trans_le hy.1
  have hne : x ≠ y := by
    intro h
    rw [h] at hdm
    exact lt_irrefl _ hdm
  rcases lt_trichotomy x y with hxy | h | hyx
  · exact ⟨fun _ => hxy, fun hev => by
      have alt := idealPeriodWord_point_lt_iff_iterate_lt_iff hN hα hx0 hxy m hdlt
      have hodd : Odd m := alt.1.mp hlt4
      exfalso
      obtain ⟨r, hr⟩ := hodd
      obtain ⟨r2, hr2⟩ := hev
      omega⟩
  · exact absurd h hne
  · have hdlt' : ∀ j < m, nExpansionDigit N α ((nExpansionMap N α)^[j] y) =
        nExpansionDigit N α ((nExpansionMap N α)^[j] x) := fun j hj => (hdlt j hj).symm
    have alt := idealPeriodWord_point_lt_iff_iterate_lt_iff hN hα hy0 hyx m hdlt'
    -- here `hlt4 : T^[m] y < T^[m] x`, and the alternating lemma for `y < x`
    -- says this happens exactly when `m` is even
    have hev : Even m := alt.2.mp hlt4
    exact ⟨fun hodd => by
      exfalso
      obtain ⟨r, hr⟩ := hodd
      obtain ⟨r2, hr2⟩ := hev
      omega, fun _ => hyx⟩

/-- The inverse formula for the N-expansion map: a point is `N` divided by
its digit plus its image. -/
private theorem idealPeriodWord_point_lt_iff_inv {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) {z : ℝ}
    (hz : z ∈ Set.Icc α (α + 1)) :
    z = (N : ℝ) / ((nExpansionDigit N α z : ℝ) + nExpansionMap N α z) := by
  have hz0 : 0 < z := hα.trans_le hz.1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : (0 : ℝ) < (nExpansionDigit N α z : ℝ) + nExpansionMap N α z := by
    have h : (nExpansionDigit N α z : ℝ) + nExpansionMap N α z = (N : ℝ) / z := by
      rw [nExpansionMap]; ring
    rw [h]
    positivity
  rw [eq_div_iff (ne_of_gt hD)]
  have h : (nExpansionDigit N α z : ℝ) + nExpansionMap N α z = (N : ℝ) / z := by
    rw [nExpansionMap]; ring
  rw [h]
  field_simp

/-- Two points of `I_α` with the same digit sequence are equal: the
N-expansion map is expanding in two steps by a uniform factor. -/
private theorem idealPeriodWord_point_lt_iff_eq_of_eq_digits {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hαN : α ≤ Real.sqrt N - 1) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1))
    (hd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      nExpansionDigit N α ((nExpansionMap N α)^[i] y)) :
    x = y := by
  by_contra hne
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmemx : ∀ j, (nExpansionMap N α)^[j] x ∈ Set.Icc α (α + 1) :=
    fun j => idealPeriodWord_point_lt_iff_iterate_mem_Icc hα hαN hx j
  have hmemy : ∀ j, (nExpansionMap N α)^[j] y ∈ Set.Icc α (α + 1) :=
    fun j => idealPeriodWord_point_lt_iff_iterate_mem_Icc hα hαN hy j
  have hNα2 : (α + 1) * (α + 1) ≤ (N : ℝ) := by
    have h1 : (0 : ℝ) ≤ α + 1 := by linarith
    have h2 : α + 1 ≤ Real.sqrt N := by linarith
    calc (α + 1) * (α + 1) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul h2 h2 h1 (by positivity)
    _ = (N : ℝ) := Real.mul_self_sqrt (by positivity)
  have hNαpos : (0 : ℝ) < (N : ℝ) - α := by nlinarith
  -- backward determinism: equality at step `j+1` gives equality at step `j`
  have hback : ∀ j, (nExpansionMap N α)^[j + 1] x = (nExpansionMap N α)^[j + 1] y →
      (nExpansionMap N α)^[j] x = (nExpansionMap N α)^[j] y := by
    intro j hj
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hj
    have hx1 := idealPeriodWord_point_lt_iff_inv hN hα (hmemx j)
    have hy1 := idealPeriodWord_point_lt_iff_inv hN hα (hmemy j)
    rw [hd j, hj] at hx1
    exact hx1.trans hy1.symm
  have hprop : ∀ j, (nExpansionMap N α)^[j] x = (nExpansionMap N α)^[j] y → x = y := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih => intro h; exact ih (hback j h)
  -- the digit of every orbit point is at least `1`
  have hge1 : ∀ j, (1 : ℝ) ≤ (N : ℝ) / (nExpansionMap N α)^[j] x - α := by
    intro j
    have h3 : (N : ℝ) / (α + 1) ≥ α + 1 := by
      rw [ge_iff_le, le_div_iff₀ (by linarith : (0:ℝ) < α + 1)]
      linarith [hNα2]
    have h4 : (N : ℝ) / (α + 1) ≤ (N : ℝ) / (nExpansionMap N α)^[j] x := by
      apply div_le_div_of_nonneg_left (by positivity)
        (hα.trans_le (hmemx j).1) (hmemx j).2
    linarith
  have hdigit1 : ∀ j, 1 ≤ nExpansionDigit N α ((nExpansionMap N α)^[j] x) := by
    intro j
    by_contra hcon
    have hnonneg := idealPeriodWord_point_lt_iff_digit_nonneg hα hαN (hmemx j)
    have hd0 : nExpansionDigit N α ((nExpansionMap N α)^[j] x) = 0 := by omega
    have hux : (nExpansionMap N α)^[j] x = α := by
      by_contra hneα
      have hdig := nExpansionDigit_of_ne (N := N) (α := α) hneα
      have hf : 1 ≤ ⌊(N : ℝ) / (nExpansionMap N α)^[j] x - α⌋ := by
        apply Int.le_floor.mpr
        exact_mod_cast hge1 j
      omega
    have hvy : (nExpansionMap N α)^[j] y = α := by
      by_contra hneα
      have hdig := nExpansionDigit_of_ne (N := N) (α := α) hneα
      have hf : 1 ≤ ⌊(N : ℝ) / (nExpansionMap N α)^[j] y - α⌋ := by
        apply Int.le_floor.mpr
        have h3 : (N : ℝ) / (α + 1) ≥ α + 1 := by
          rw [ge_iff_le, le_div_iff₀ (by linarith : (0:ℝ) < α + 1)]
          linarith [hNα2]
        have h4 : (N : ℝ) / (α + 1) ≤ (N : ℝ) / (nExpansionMap N α)^[j] y := by
          apply div_le_div_of_nonneg_left (by positivity)
            (hα.trans_le (hmemy j).1) (hmemy j).2
        linarith
      have hdy : nExpansionDigit N α ((nExpansionMap N α)^[j] y) = 0 := by rw [← hd j, hd0]
      omega
    exact hne (hprop j (by rw [hux, hvy]))
  -- A nonzero separation cannot stay bounded under two-step expansion.
  have hd0pos : 0 < |(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y| := by
    simpa using abs_pos.mpr (sub_ne_zero.mpr hne)
  have hdle : ∀ j, |(nExpansionMap N α)^[j] x - (nExpansionMap N α)^[j] y| ≤ 1 := by
    intro j
    have h1 := (hmemx j).1
    have h2 := (hmemx j).2
    have h3 := (hmemy j).1
    have h4 := (hmemy j).2
    rw [abs_le]
    constructor <;> linarith
  have hstep : ∀ j, |(nExpansionMap N α)^[j + 1] x - (nExpansionMap N α)^[j + 1] y| =
      |(nExpansionMap N α)^[j] x - (nExpansionMap N α)^[j] y| *
        ((N : ℝ) / ((nExpansionMap N α)^[j] x * (nExpansionMap N α)^[j] y)) := by
    intro j
    have hdiff : (nExpansionMap N α)^[j + 1] x - (nExpansionMap N α)^[j + 1] y =
        (N : ℝ) * ((nExpansionMap N α)^[j] y - (nExpansionMap N α)^[j] x) /
          ((nExpansionMap N α)^[j] x * (nExpansionMap N α)^[j] y) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', nExpansionMap,
        nExpansionMap, hd j]
      have hu0 : (nExpansionMap N α)^[j] x ≠ 0 :=
        ne_of_gt (hα.trans_le (hmemx j).1)
      have hv0 : (nExpansionMap N α)^[j] y ≠ 0 :=
        ne_of_gt (hα.trans_le (hmemy j).1)
      field_simp
      ring
    rw [hdiff, abs_div, abs_mul, abs_of_pos hN',
      abs_of_pos (mul_pos (hα.trans_le (hmemx j).1) (hα.trans_le (hmemy j).1)),
      abs_sub_comm]
    ring
  have hbound : ∀ j, (nExpansionMap N α)^[j] x * (nExpansionMap N α)^[j + 1] x ≤ (N : ℝ) - α ∧
      (nExpansionMap N α)^[j] y * (nExpansionMap N α)^[j + 1] y ≤ (N : ℝ) - α := by
    intro j
    have hu0 : 0 < (nExpansionMap N α)^[j] x := hα.trans_le (hmemx j).1
    have hv0 : 0 < (nExpansionMap N α)^[j] y := hα.trans_le (hmemy j).1
    have hA : (nExpansionMap N α)^[j] x * (nExpansionMap N α)^[j + 1] x =
        (N : ℝ) - (nExpansionDigit N α ((nExpansionMap N α)^[j] x) : ℝ) *
          (nExpansionMap N α)^[j] x := by
      rw [Function.iterate_succ_apply', nExpansionMap]
      field_simp
    have hB : (nExpansionMap N α)^[j] y * (nExpansionMap N α)^[j + 1] y =
        (N : ℝ) - (nExpansionDigit N α ((nExpansionMap N α)^[j] y) : ℝ) *
          (nExpansionMap N α)^[j] y := by
      rw [Function.iterate_succ_apply', nExpansionMap]
      field_simp
    have hdge : (1 : ℝ) * α ≤ (nExpansionDigit N α ((nExpansionMap N α)^[j] x) : ℝ) *
        (nExpansionMap N α)^[j] x :=
      mul_le_mul (by exact_mod_cast hdigit1 j) (hmemx j).1 (by linarith)
        (by exact_mod_cast idealPeriodWord_point_lt_iff_digit_nonneg hα hαN (hmemx j))
    have hd1y : 1 ≤ nExpansionDigit N α ((nExpansionMap N α)^[j] y) := by
      rw [← hd j]; exact hdigit1 j
    have hdge2 : (1 : ℝ) * α ≤ (nExpansionDigit N α ((nExpansionMap N α)^[j] y) : ℝ) *
        (nExpansionMap N α)^[j] y :=
      mul_le_mul (by exact_mod_cast hd1y) (hmemy j).1 (by linarith)
        (by exact_mod_cast (by omega : 0 ≤ nExpansionDigit N α ((nExpansionMap N α)^[j] y)))
    refine ⟨?_, ?_⟩
    · rw [hA]; linarith
    · rw [hB]; linarith
  have htwo : ∀ j, |(nExpansionMap N α)^[j] x - (nExpansionMap N α)^[j] y| *
        ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) ≤
      |(nExpansionMap N α)^[j + 2] x - (nExpansionMap N α)^[j + 2] y| := by
    intro j
    have hu0 : 0 < (nExpansionMap N α)^[j] x := hα.trans_le (hmemx j).1
    have hv0 : 0 < (nExpansionMap N α)^[j] y := hα.trans_le (hmemy j).1
    have hu1 : 0 < (nExpansionMap N α)^[j + 1] x := hα.trans_le (hmemx (j + 1)).1
    have hv1 : 0 < (nExpansionMap N α)^[j + 1] y := hα.trans_le (hmemy (j + 1)).1
    have hstep2 : |(nExpansionMap N α)^[j + 2] x - (nExpansionMap N α)^[j + 2] y| =
        |(nExpansionMap N α)^[j] x - (nExpansionMap N α)^[j] y| *
          ((N : ℝ) ^ 2 / (((nExpansionMap N α)^[j] x * (nExpansionMap N α)^[j + 1] x) *
            ((nExpansionMap N α)^[j] y * (nExpansionMap N α)^[j + 1] y))) := by
      rw [show j + 2 = (j + 1) + 1 from rfl, hstep (j + 1), hstep j]
      have hu0' : (nExpansionMap N α)^[j] x ≠ 0 := ne_of_gt hu0
      have hv0' : (nExpansionMap N α)^[j] y ≠ 0 := ne_of_gt hv0
      have hu1' : (nExpansionMap N α)^[j + 1] x ≠ 0 := ne_of_gt hu1
      have hv1' : (nExpansionMap N α)^[j + 1] y ≠ 0 := ne_of_gt hv1
      field_simp
    rw [hstep2]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply div_le_div_of_nonneg_left (by positivity)
      (mul_pos (mul_pos hu0 hu1) (mul_pos hv0 hv1))
    rw [pow_two]
    exact mul_le_mul (hbound j).1 (hbound j).2
      (mul_nonneg (le_of_lt hv0) (le_of_lt hv1)) (by linarith [hNαpos])
  have hc : (1 : ℝ) < (N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2 := by
    rw [one_lt_div (by positivity)]
    nlinarith [hNαpos, hα, hN']
  have hiter : ∀ n, |(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y| *
        ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) ^ n ≤
      |(nExpansionMap N α)^[2 * n] x - (nExpansionMap N α)^[2 * n] y| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 := htwo (2 * n)
      have heq : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [heq]
      calc |(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y| *
            ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) ^ (n + 1)
          = (|(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y| *
              ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) ^ n) *
              ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) := by rw [pow_succ]; ring
        _ ≤ |(nExpansionMap N α)^[2 * n] x - (nExpansionMap N α)^[2 * n] y| *
              ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ |(nExpansionMap N α)^[2 * n + 2] x - (nExpansionMap N α)^[2 * n + 2] y| := h2
  obtain ⟨n, hn⟩ : ∃ n, (1 : ℝ) < |(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y| *
      ((N : ℝ) ^ 2 / ((N : ℝ) - α) ^ 2) ^ n := by
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt
      (1 / |(nExpansionMap N α)^[0] x - (nExpansionMap N α)^[0] y|) hc
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hd0pos] at hn'
    rwa [mul_comm] at hn'
  have hle2 := hdle (2 * n)
  linarith [hiter n, hn]

/-- **The ideal periodic points decrease.** Let $N$ be a natural number, let $\alpha$ be a real
number with $0 < \alpha \le \sqrt N - 1$, and let $T_\alpha$ be the $N$-expansion map on
$I_\alpha = [\alpha, \alpha + 1]$. For $m \ge 1$ write $|d_m|$ for the length of the digit string
of the ideal period word $d_m$. Let $k, \ell \ge 1$ and let $x, y \in I_\alpha$ be such that for
every $i \ge 0$ the digit of $T_\alpha^i(x)$ is entry $i \bmod |d_k|$ (counting from $0$) of the
digit string of $d_k$, and the digit of $T_\alpha^i(y)$ is entry $i \bmod |d_\ell|$ of the digit
string of $d_\ell$; that is, the expansions of $x$ and $y$ are purely periodic with period words
$d_k$ and $d_\ell$. Then $x < y$ if and only if $\ell < k$.

The source works in Phase I; only the assumption $0 < \alpha \le \sqrt N - 1$ is kept here, which
makes $T_\alpha$ expanding, so that a digit sequence determines its point.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 4 (`integers-2026-A75-lem-4`). -/
public theorem idealPeriodWord_point_lt_iff {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord k).flatten.getD (i % (idealPeriodWord k).flatten.length) 0 : ℤ))
    (hyd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] y) =
      ((idealPeriodWord ℓ).flatten.getD (i % (idealPeriodWord ℓ).flatten.length) 0 : ℤ)) :
    x < y ↔ ℓ < k := by
  have hs1 : (1 : ℝ) < Real.sqrt N := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hsq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [mul_pos (show (0 : ℝ) < Real.sqrt N - 1 by linarith)
      (show (0 : ℝ) < Real.sqrt N + 1 by linarith)]
  have hN : 0 < N := by exact_mod_cast hNpos
  have hdigx : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      (idealPeriodWord_point_lt_iff_dig k i : ℤ) := fun i => hxd i
  have hdigy : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] y) =
      (idealPeriodWord_point_lt_iff_dig ℓ i : ℤ) := fun i => hyd i
  by_cases hkl : k = ℓ
  · subst hkl
    have hxy_eq : x = y := idealPeriodWord_point_lt_iff_eq_of_eq_digits hN hα hαN hx hy
      fun i => by rw [hdigx i, hdigy i]
    constructor
    · intro h
      rw [hxy_eq] at h
      exact (lt_irrefl _ h).elim
    · intro h
      exact (lt_irrefl _ h).elim
  · have hdecide : (x < y ∧ ℓ < k) ∨ (y < x ∧ k < ℓ) := by
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · -- `k < ℓ`: the first difference gives `y < x`
        obtain ⟨hagree, hvalk, hvall⟩ :=
          idealPeriodWord_point_lt_iff_dig_compare k hk ℓ hlt
        have hpar := idealPeriodWord_point_lt_iff_firstDiff_parity hk
        have hdlt : ∀ j < idealPeriodWord_point_lt_iff_firstDiff k,
            nExpansionDigit N α ((nExpansionMap N α)^[j] x) =
              nExpansionDigit N α ((nExpansionMap N α)^[j] y) := by
          intro j hj
          rw [hdigx j, hdigy j, hagree j hj]
        rcases Nat.even_or_odd k with hkev | hkodd
        · have hodd : Odd (idealPeriodWord_point_lt_iff_firstDiff k) := by
            apply Nat.not_even_iff_odd.mp
            intro hev
            have hodd' : Odd k := hpar.mp hev
            obtain ⟨r, hr⟩ := hodd'
            obtain ⟨r2, hr2⟩ := hkev
            omega
          have hknot : ¬ Odd k := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hkev
            omega
          rw [ite_eq_right hknot] at hvalk hvall
          have hdm : nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff k] y) <
              nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff k] x) := by
            rw [hdigy, hdigx, hvall, hvalk]
            norm_num
          have hdlt' : ∀ j < idealPeriodWord_point_lt_iff_firstDiff k,
              nExpansionDigit N α ((nExpansionMap N α)^[j] y) =
                nExpansionDigit N α ((nExpansionMap N α)^[j] x) := fun j hj => (hdlt j hj).symm
          have hord := idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hy hx hdlt' hdm
          exact Or.inr ⟨hord.1 hodd, hlt⟩
        · have hev : Even (idealPeriodWord_point_lt_iff_firstDiff k) := hpar.mpr hkodd
          have hvalk' : idealPeriodWord_point_lt_iff_dig k
              (idealPeriodWord_point_lt_iff_firstDiff k) = 1 := by
            rw [ite_eq_left hkodd] at hvalk
            exact hvalk
          have hvall' : idealPeriodWord_point_lt_iff_dig ℓ
              (idealPeriodWord_point_lt_iff_firstDiff k) = 2 := by
            rw [ite_eq_left hkodd] at hvall
            exact hvall
          have hdm : nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff k] x) <
              nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff k] y) := by
            rw [hdigx, hdigy, hvalk', hvall']
            norm_num
          have hord := idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hx hy hdlt hdm
          exact Or.inr ⟨hord.2 hev, hlt⟩
      · -- `ℓ < k`: the first difference gives `x < y`
        obtain ⟨hagree, hvall, hvalk⟩ :=
          idealPeriodWord_point_lt_iff_dig_compare ℓ hℓ k hgt
        have hpar := idealPeriodWord_point_lt_iff_firstDiff_parity hℓ
        have hdlt : ∀ j < idealPeriodWord_point_lt_iff_firstDiff ℓ,
            nExpansionDigit N α ((nExpansionMap N α)^[j] x) =
              nExpansionDigit N α ((nExpansionMap N α)^[j] y) := by
          intro j hj
          rw [hdigx j, hdigy j, (hagree j hj).symm]
        rcases Nat.even_or_odd ℓ with hℓev | hℓodd
        · have hodd : Odd (idealPeriodWord_point_lt_iff_firstDiff ℓ) := by
            apply Nat.not_even_iff_odd.mp
            intro hev
            have hodd' : Odd ℓ := hpar.mp hev
            obtain ⟨r, hr⟩ := hodd'
            obtain ⟨r2, hr2⟩ := hℓev
            omega
          have hℓnot : ¬ Odd ℓ := by
            intro h
            obtain ⟨r, hr⟩ := h
            obtain ⟨r2, hr2⟩ := hℓev
            omega
          rw [ite_eq_right hℓnot] at hvall hvalk
          have hdm : nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff ℓ] x) <
              nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff ℓ] y) := by
            rw [hdigx, hdigy, hvalk, hvall]
            norm_num
          have hord := idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hx hy hdlt hdm
          exact Or.inl ⟨hord.1 hodd, hgt⟩
        · have hev : Even (idealPeriodWord_point_lt_iff_firstDiff ℓ) := hpar.mpr hℓodd
          have hvall' : idealPeriodWord_point_lt_iff_dig ℓ
              (idealPeriodWord_point_lt_iff_firstDiff ℓ) = 1 := by
            rw [ite_eq_left hℓodd] at hvall
            exact hvall
          have hvalk' : idealPeriodWord_point_lt_iff_dig k
              (idealPeriodWord_point_lt_iff_firstDiff ℓ) = 2 := by
            rw [ite_eq_left hℓodd] at hvalk
            exact hvalk
          have hdm : nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff ℓ] y) <
              nExpansionDigit N α
              ((nExpansionMap N α)^[idealPeriodWord_point_lt_iff_firstDiff ℓ] x) := by
            rw [hdigy, hdigx, hvall', hvalk']
            norm_num
          have hdlt' : ∀ j < idealPeriodWord_point_lt_iff_firstDiff ℓ,
              nExpansionDigit N α ((nExpansionMap N α)^[j] y) =
                nExpansionDigit N α ((nExpansionMap N α)^[j] x) := fun j hj => (hdlt j hj).symm
          have hord := idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hy hx hdlt' hdm
          exact Or.inl ⟨hord.2 hev, hgt⟩
    rcases hdecide with ⟨hxy, hlk⟩ | ⟨hyx, hkl2⟩
    · constructor
      · intro _
        exact hlk
      · intro _
        exact hxy
    · constructor
      · intro h
        exact absurd h (not_lt_of_gt hyx)
      · intro h
        exact absurd h (not_lt_of_gt hkl2)

namespace IdealPeriodOrbit

private def slotBlocks (b : Bool) : List (List ℕ) :=
  if b then [[2, 1, 1], [2, 2]] else [[2, 2]]

private def slotDigits (b : Bool) : List ℕ := (slotBlocks b).flatten

private def digits (w : List Bool) : List ℕ := w.flatMap slotDigits

-- The period-doubling substitution sends each bit `b` to `[true, !b]`.
private def doubleSlots (w : List Bool) : List Bool := w.flatMap fun b => [true, !b]

private def slots : ℕ → List Bool
  | 0 => [true]
  | n + 1 => doubleSlots (slots n)

private theorem slots_rec (n : ℕ) :
    slots (n + 2) = slots (n + 1) ++ slots n ++ slots n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change doubleSlots (slots (n + 2)) =
      doubleSlots (slots (n + 1)) ++ doubleSlots (slots n) ++ doubleSlots (slots n)
    rw [ih]
    simp [doubleSlots, List.flatMap_append]

private theorem digits_append (u v : List Bool) : digits (u ++ v) = digits u ++ digits v :=
  List.flatMap_append

private theorem digits_cons (b : Bool) (w : List Bool) :
    digits (b :: w) = slotDigits b ++ digits w :=
  rfl

private theorem doubleSlots_length (w : List Bool) : (doubleSlots w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [doubleSlots] at ih ⊢; omega

private theorem slots_length_pos (n : ℕ) : 0 < (slots n).length := by
  induction n with
  | zero => decide
  | succ n ih => rw [slots, doubleSlots_length]; omega

private def cyclicGet {α : Type*} [Inhabited α] (w : List α) (i : ℕ) : α :=
  w.getD (i % w.length) default

private theorem cyclicGet_inside {α : Type*} [Inhabited α] {w : List α} {i : ℕ}
    (hi : i < w.length) : cyclicGet w i = w[i] := by
  rw [cyclicGet, Nat.mod_eq_of_lt hi, ← List.getElem_eq_getD (h := hi)]

private theorem doubleSlots_pair (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (doubleSlots w).getD (2 * i) default = true ∧
      (doubleSlots w).getD (2 * i + 1) default = !(w.getD i default) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons b w ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have h := ih (i := i) (by simpa using hi)
      simpa [doubleSlots, show 2 * (i + 1) = 2 * i + 2 by omega,
        show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega] using h

private theorem cyclicGet_doubleSlots (w : List Bool) (hw : 0 < w.length) (i : ℕ) :
    cyclicGet (doubleSlots w) (2 * i) = true ∧
      cyclicGet (doubleSlots w) (2 * i + 1) = !(cyclicGet w i) := by
  have h₀ : 2 * i % (2 * w.length) = 2 * (i % w.length) := Nat.mul_mod_mul_left _ _ _
  have h₁ : (2 * i + 1) % (2 * w.length) = 2 * (i % w.length) + 1 := by
    rw [Nat.add_mod, h₀, Nat.mod_eq_of_lt (show 1 < 2 * w.length by omega)]
    exact Nat.mod_eq_of_lt (by have := Nat.mod_lt i hw; omega)
  simpa only [cyclicGet, doubleSlots_length, h₀, h₁] using
    doubleSlots_pair w (Nat.mod_lt i hw)

private theorem slots_head (n : ℕ) : ∃ w, slots n = true :: w := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    rw [slots, hw]
    exact ⟨false :: doubleSlots w, rfl⟩

private theorem slot_zero (n : ℕ) : cyclicGet (slots n) 0 = true := by
  obtain ⟨w, hw⟩ := slots_head n
  simp [hw, cyclicGet]

-- The two substituted slots have total length 7 or 10, of the same parity as the
-- original slot's length (5 or 2, respectively).
private theorem digits_doubleSlots_length_mod_two (w : List Bool) :
    (digits (doubleSlots w)).length % 2 = (digits w).length % 2 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (digits (true :: (!b) :: doubleSlots w)).length % 2 = (digits (b :: w)).length % 2
    cases b <;> simp only [Bool.not_true, Bool.not_false, digits_cons, List.length_append] <;>
      simp [slotDigits, slotBlocks] <;> omega

private theorem take_doubleSlots (w : List Bool) (k : ℕ) :
    (doubleSlots w).take (2 * k) = doubleSlots (w.take k) := by
  induction w generalizing k with
  | nil => simp [doubleSlots]
  | cons b w ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
      change true :: (!b) :: (doubleSlots w).take (2 * k) =
        true :: (!b) :: doubleSlots (w.take k)
      rw [ih]

-- Every nonzero shift of the slot word has a first mismatch, and the number of
-- digits through the original mismatching slot is odd.
private theorem slot_firstDiff (n : ℕ) {j : ℕ} (hj₀ : 0 < j) (hj : j < (slots n).length) :
    ∃ k < (slots n).length,
      (∀ i < k, cyclicGet (slots n) i = cyclicGet (slots n) (j + i)) ∧
      cyclicGet (slots n) k ≠ cyclicGet (slots n) (j + k) ∧
      (digits ((slots n).take (k + 1))).length % 2 = 1 := by
  induction n generalizing j with
  | zero => change j < 1 at hj; omega
  | succ n ih =>
    let w := slots n
    have hw : 0 < w.length := slots_length_pos n
    change j < (doubleSlots w).length at hj
    rw [doubleSlots_length] at hj
    change ∃ k < (doubleSlots w).length,
      (∀ i < k, cyclicGet (doubleSlots w) i = cyclicGet (doubleSlots w) (j + i)) ∧
      cyclicGet (doubleSlots w) k ≠ cyclicGet (doubleSlots w) (j + k) ∧
      (digits ((doubleSlots w).take (k + 1))).length % 2 = 1
    have hpair := cyclicGet_doubleSlots w hw
    rcases (show ∃ s, j = 2 * s ∨ j = 2 * s + 1 from
      ⟨j / 2, by omega⟩) with ⟨s, rfl | rfl⟩
    · have hs : s < w.length := by omega
      obtain ⟨k, hk, hagree, hne, hpar⟩ := ih (j := s) (by omega) hs
      change k < w.length at hk
      refine ⟨2 * k + 1, by rw [doubleSlots_length]; omega, ?_, ?_, ?_⟩
      · intro i hi
        rcases (show ∃ t, i = 2 * t ∨ i = 2 * t + 1 from ⟨i / 2, by omega⟩) with
          ⟨t, rfl | rfl⟩
        · rw [show 2 * s + 2 * t = 2 * (s + t) by omega, (hpair t).1, (hpair (s + t)).1]
        · rw [show 2 * s + (2 * t + 1) = 2 * (s + t) + 1 by omega, (hpair t).2,
            (hpair (s + t)).2, hagree t (by omega)]
      · rw [show 2 * s + (2 * k + 1) = 2 * (s + k) + 1 by omega, (hpair k).2,
          (hpair (s + k)).2]
        simpa using hne
      · rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, take_doubleSlots,
          digits_doubleSlots_length_mod_two]
    · have h0 : cyclicGet (doubleSlots w) 0 = true := (hpair 0).1
      have h1 : cyclicGet (doubleSlots w) 1 = false := by
        change cyclicGet (doubleSlots w) (2 * 0 + 1) = false
        rw [(hpair 0).2, slot_zero]
        rfl
      have hshift1 : cyclicGet (doubleSlots w) (2 * s + 1 + 1) = true := by
        rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega, (hpair (s + 1)).1]
      have hprefix : (doubleSlots w).take 2 = [true, false] := by
        obtain ⟨t, ht⟩ := slots_head n
        change w = true :: t at ht
        rw [ht]
        rfl
      by_cases hshift0 : cyclicGet (doubleSlots w) (2 * s + 1) = true
      · refine ⟨1, by rw [doubleSlots_length]; omega, ?_, ?_, ?_⟩
        · intro i hi
          have : i = 0 := by omega
          simp [this, h0, hshift0]
        · rw [h1, hshift1]; decide
        · rw [hprefix]; decide
      · refine ⟨0, by rw [doubleSlots_length]; omega, by omega, ?_, ?_⟩
        · simpa only [h0, Nat.add_zero] using Ne.symm hshift0
        · have hprefix₁ := congrArg (List.take 1) hprefix
          rw [List.take_take] at hprefix₁
          change (doubleSlots w).take 1 = [true] at hprefix₁
          rw [hprefix₁]; decide

private theorem cyclicGet_rotate {α : Type*} [Inhabited α] (w : List α) (j i : ℕ) :
    cyclicGet (w.rotate j) i = cyclicGet w (j + i) := by
  cases w with
  | nil => simp [cyclicGet]
  | cons a w =>
    have h : i % (a :: w).length < ((a :: w).rotate j).length := by
      rw [List.length_rotate]
      exact Nat.mod_lt _ (by simp)
    conv_lhs => rw [cyclicGet, List.length_rotate, ← List.getElem_eq_getD (h := h),
      List.getElem_rotate, List.getElem_eq_getD default, Nat.mod_add_mod, Nat.add_comm i j]
    rfl

-- Compare two periodic digit lists by the parity and direction of their first difference.
private def DigitWins (u v : List ℕ) : Prop :=
  ∃ k, (∀ i < k, cyclicGet u i = cyclicGet v i) ∧
    ((Odd k ∧ cyclicGet u k < cyclicGet v k) ∨ (Even k ∧ cyclicGet v k < cyclicGet u k))

private theorem digitWins_prefix (p u v : List ℕ) {a b : ℕ}
    (h : (Odd p.length ∧ a < b) ∨ (Even p.length ∧ b < a)) :
    DigitWins (p ++ a :: u) (p ++ b :: v) := by
  have hleft : p.length < (p ++ a :: u).length := by simp
  have hright : p.length < (p ++ b :: v).length := by simp
  refine ⟨p.length, ?_, ?_⟩
  · intro i hi
    rw [cyclicGet_inside (hi.trans hleft), cyclicGet_inside (hi.trans hright),
      List.getElem_append_left hi, List.getElem_append_left hi]
  · simpa only [cyclicGet_inside hleft, cyclicGet_inside hright,
      List.getElem_append_right (Nat.le_refl p.length), Nat.sub_self, List.getElem_cons_zero]
      using h

private theorem digitWins_of_slot (p u v : List Bool) {a b : Bool} (hne : a ≠ b)
    (hpar : (digits (p ++ [a])).length % 2 = 1) :
    DigitWins (digits (p ++ a :: u)) (digits (p ++ b :: v)) := by
  rw [digits_append, digits_append, digits_cons, digits_cons]
  rw [digits_append] at hpar
  cases a <;> cases b
  · exact (hne rfl).elim
  · have h : Even (digits p ++ [2]).length := by
      apply Nat.even_iff.mpr
      simp [digits, slotDigits, slotBlocks] at hpar ⊢
      omega
    simpa [slotDigits, slotBlocks, List.append_assoc] using
      digitWins_prefix (digits p ++ [2]) (digits u) (1 :: 2 :: 2 :: digits v)
        (a := 2) (b := 1) (Or.inr ⟨h, by decide⟩)
  · have h : Odd (digits p ++ [2]).length := by
      apply Nat.odd_iff.mpr
      simp [digits, slotDigits, slotBlocks] at hpar ⊢
      omega
    simpa [slotDigits, slotBlocks, List.append_assoc] using
      digitWins_prefix (digits p ++ [2]) (1 :: 2 :: 2 :: digits u) (digits v)
        (a := 1) (b := 2) (Or.inl ⟨h, by decide⟩)
  · exact (hne rfl).elim

private theorem digitWins_slot_rotate (n : ℕ) {j : ℕ} (hj₀ : 0 < j) (hj : j < (slots n).length) :
    DigitWins (digits (slots n)) (digits ((slots n).rotate j)) := by
  obtain ⟨k, hk, hagree, hne, hpar⟩ := slot_firstDiff n hj₀ hj
  let u := slots n
  let v := u.rotate j
  have hk' : k < v.length := by simpa [v, u] using hk
  have hp : u.take k = v.take k := by
    apply List.ext_getElem
    · simp [v, List.length_take]
    · intro i hi hi'
      rw [List.length_take, Nat.min_eq_left hk.le] at hi
      rw [List.getElem_take, List.getElem_take, ← cyclicGet_inside (hi.trans hk),
        ← cyclicGet_inside (hi.trans hk'), cyclicGet_rotate]
      exact hagree i hi
  have hab : u[k] ≠ v[k] := by
    rw [← cyclicGet_inside hk, ← cyclicGet_inside hk', cyclicGet_rotate]
    exact hne
  have hu : u.take k ++ u[k] :: u.drop (k + 1) = u := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hv : u.take k ++ v[k] :: v.drop (k + 1) = v := by
    rw [hp, ← List.drop_eq_getElem_cons hk', List.take_append_drop]
  have hpar' : (digits (u.take k ++ [u[k]])).length % 2 = 1 := by
    rwa [← List.take_succ_eq_append_getElem hk]
  change DigitWins (digits u) (digits v)
  simpa only [hu, hv] using
    digitWins_of_slot (u.take k) (u.drop (k + 1)) (v.drop (k + 1)) hab hpar'

private theorem exists_slot_at (w : List Bool) {r : ℕ} (hr : r < (digits w).length) :
    ∃ p b s q, w = p ++ b :: s ∧ r = (digits p).length + q ∧ q < (slotDigits b).length := by
  induction w generalizing r with
  | nil => simp [digits] at hr
  | cons b w ih =>
    by_cases h : r < (slotDigits b).length
    · exact ⟨[], b, w, r, rfl, by simp [digits], h⟩
    · rw [digits_cons, List.length_append] at hr
      obtain ⟨p, c, s, q, hc, hq, hqc⟩ := ih (r := r - (slotDigits b).length) (by omega)
      refine ⟨b :: p, c, s, q, congrArg (b :: ·) hc, ?_, hqc⟩
      rw [digits_cons, List.length_append]
      omega

private theorem offSlot_prefix (b : Bool) (w : List Bool) {q : ℕ}
    (hq₀ : 0 < q) (hq : q < (slotDigits b).length) :
    (∃ v, (slotDigits b).drop q ++ digits w ++ (slotDigits b).take q = 1 :: v) ∨
      (∃ v, (slotDigits b).drop q ++ digits w ++ (slotDigits b).take q = 2 :: 2 :: v) := by
  have hnext : ∃ v, digits w ++ (slotDigits b).take q = 2 :: v := by
    cases w with
    | nil =>
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
      cases b <;> exact ⟨_, rfl⟩
    | cons c w => cases c <;> exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hnext
  rw [List.append_assoc, hv]
  cases b <;> norm_num [slotDigits, slotBlocks] at hq
  · interval_cases q
    exact Or.inr ⟨v, rfl⟩
  · interval_cases q
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨v, rfl⟩

private theorem digitWins_rotate (n : ℕ) {r : ℕ} (hr₀ : 0 < r)
    (hr : r < (digits (slots n)).length) :
    DigitWins (digits (slots n)) ((digits (slots n)).rotate r) := by
  obtain ⟨p, b, s, q, hw, hrq, hq⟩ := exists_slot_at (slots n) hr
  have hrot : (digits (slots n)).rotate r = (digits (b :: (s ++ p))).rotate q := by
    rw [hrq, ← List.rotate_rotate, hw, digits_append, List.rotate_append_length_eq,
      ← digits_append, List.cons_append]
  by_cases hq₀ : q = 0
  · have hp : 0 < p.length := by
      cases p with
      | nil => simp [digits, hq₀] at hrq; omega
      | cons a t => simp
    have hplen : p.length < (slots n).length := by rw [hw]; simp
    have hslotsRot : (slots n).rotate p.length = b :: (s ++ p) := by
      rw [hw, List.rotate_append_length_eq, List.cons_append]
    simpa only [hrot, hq₀, List.rotate_zero, hslotsRot] using digitWins_slot_rotate n hp hplen
  · have hrot' : (digits (b :: (s ++ p))).rotate q =
        (slotDigits b).drop q ++ digits (s ++ p) ++ (slotDigits b).take q := by
      rw [digits_cons, List.rotate_eq_drop_append_take
        (by rw [List.length_append]; omega), List.drop_append_of_le_length hq.le,
        List.take_append_of_le_length hq.le]
    obtain ⟨t, ht⟩ := slots_head n
    rw [hrot, hrot']
    rcases offSlot_prefix b (s ++ p) (by omega) hq with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [hv, ht]
      exact digitWins_prefix [] (1 :: 1 :: 2 :: 2 :: digits t) v (Or.inr ⟨by decide, by decide⟩)
    · rw [hv, ht]
      exact digitWins_prefix [2] (1 :: 2 :: 2 :: digits t) v (Or.inl ⟨by decide, by decide⟩)


-- The period-doubling slot substitution satisfies the same concatenation
-- recursion as the ideal period words, with the same two initial digit strings.
private theorem digits_eq_flatten_slots (n : ℕ) :
    digits (slots n) = (idealPeriodWord (n + 1)).flatten ∧
      digits (slots (n + 1)) = (idealPeriodWord (n + 2)).flatten := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [slots_rec n, idealPeriodWord_point_lt_iff_flatten_rec (n := n + 1) (by omega),
      digits_append, digits_append, ih.1, ih.2]

end IdealPeriodOrbit

open IdealPeriodOrbit in
/-- **The ideal periodic point is the least point of its orbit.** Let $N$ be a natural number,
let $\alpha$ be a real number with $0 < \alpha \le \sqrt N - 1$, and let $T_\alpha$ be the
$N$-expansion map on $I_\alpha = [\alpha, \alpha + 1]$. Let $n \ge 1$, write $|d_n|$ for the
length of the digit string of the ideal period word $d_n$, and let $x \in I_\alpha$ be such that
for every $i \ge 0$ the digit of $T_\alpha^i(x)$ is entry $i \bmod |d_n|$ (counting from $0$) of
that digit string, so that the expansion of $x$ is purely periodic with period word $d_n$. Then
$x \le T_\alpha^j(x)$ for every $j \ge 0$.

The source assumes Phase I; only the assumption $0 < \alpha \le \sqrt N - 1$ is kept here.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 5 (`integers-2026-A75-lem-5`). -/
public theorem idealPeriodWord_point_le_orbit {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord n).flatten.getD (i % (idealPeriodWord n).flatten.length) 0 : ℤ))
    (j : ℕ) :
    x ≤ (nExpansionMap N α)^[j] x := by
  have hNreal : (0 : ℝ) < N := Real.sqrt_pos.mp (by linarith)
  have hN : 0 < N := by exact_mod_cast hNreal
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let w := digits (slots m)
  have hw : w = (idealPeriodWord (m + 1)).flatten := (digits_eq_flatten_slots m).1
  have hwpos : 0 < w.length := by
    rw [hw]
    exact idealPeriodWord_point_lt_iff_flatten_length_pos (by omega)
  let y := (nExpansionMap N α)^[j] x
  have hy : y ∈ Set.Icc α (α + 1) :=
    idealPeriodWord_point_lt_iff_iterate_mem_Icc hα hαN hx j
  have hdx (i : ℕ) : nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      (cyclicGet (α := ℕ) w i : ℤ) := by
    simpa only [cyclicGet, hw, show (default : ℕ) = 0 from rfl] using hxd i
  have hdy (i : ℕ) : nExpansionDigit N α ((nExpansionMap N α)^[i] y) =
      (cyclicGet (α := ℕ) (w.rotate j) i : ℤ) := by
    change nExpansionDigit N α ((nExpansionMap N α)^[i] ((nExpansionMap N α)^[j] x)) = _
    rw [← Function.iterate_add_apply, Nat.add_comm i j, hdx, cyclicGet_rotate]
  by_cases hj : j % w.length = 0
  · have hrot : w.rotate j = w := by rw [← List.rotate_mod, hj, List.rotate_zero]
    exact (idealPeriodWord_point_lt_iff_eq_of_eq_digits hN hα hαN hx hy
      fun i => by rw [hdx, hdy, hrot]).le
  · have hwin : DigitWins w (w.rotate (j % w.length)) :=
      digitWins_rotate m (Nat.pos_of_ne_zero hj) (Nat.mod_lt j hwpos)
    rw [List.rotate_mod] at hwin
    obtain ⟨k, hagree, hcmp⟩ := hwin
    have hagree' (i : ℕ) (hi : i < k) : nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
        nExpansionDigit N α ((nExpansionMap N α)^[i] y) := by
      rw [hdx, hdy, hagree i hi]
    rcases hcmp with ⟨hodd, hlt⟩ | ⟨heven, hlt⟩
    · have hlt' : nExpansionDigit N α ((nExpansionMap N α)^[k] x) <
          nExpansionDigit N α ((nExpansionMap N α)^[k] y) := by
        rw [hdx, hdy]
        exact_mod_cast hlt
      exact ((idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hx hy hagree' hlt').1 hodd).le
    · have hlt' : nExpansionDigit N α ((nExpansionMap N α)^[k] y) <
          nExpansionDigit N α ((nExpansionMap N α)^[k] x) := by
        rw [hdx, hdy]
        exact_mod_cast hlt
      exact ((idealPeriodWord_point_lt_iff_lt_of_first_diff hN hα hαN hy hx
        (fun i hi => (hagree' i hi).symm) hlt').2 heven).le

end

end MetaMathlibExt
