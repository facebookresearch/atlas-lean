/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic

/-!
# Rank and select on bitvectors

`brank bv k` counts the `true` bits among the first `k`;
`bselect bv k` finds the index of the `k`-th `true`
(0-indexed). Select at `i` implies the rank up to `i` is
exactly `k` and the bit at `i` is set. The succinct block
layout is not included here.
-/

@[expose] public section

/-- Rank: number of `true` in the first `k` bits (succinct
bitvector core of ALG-51). -/
def brank (bv : List Bool) (k : ℕ) : ℕ :=
  (bv.take k).count true

/-- Select: index of the `k`-th `true` (0-indexed `k`),
found by recursion on the list. -/
def bselect : List Bool → ℕ → Option ℕ
  | [], _ => none
  | false :: bs, k => (bselect bs k).map (· + 1)
  | true :: bs, 0 => some 0
  | true :: bs, k + 1 => (bselect bs k).map (· + 1)

private theorem brank_cons_false (bs : List Bool) (n : ℕ) :
    brank (false :: bs) (n + 1) = brank bs n := by
  unfold brank
  rw [List.take_succ_cons, List.count_cons_of_ne (by simp : false ≠ true)]

private theorem brank_cons_true (bs : List Bool) (n : ℕ) :
    brank (true :: bs) (n + 1) = brank bs n + 1 := by
  unfold brank
  rw [List.take_succ_cons, List.count_cons_self]

/-- Rank is monotone and bounded by the number of bits read. -/
theorem brank_le (bv : List Bool) (k : ℕ) :
    brank bv k ≤ k := by
  unfold brank
  calc (bv.take k).count true ≤ (bv.take k).length := List.count_le_length
    _ = min k bv.length := List.length_take
    _ ≤ k := Nat.min_le_left _ _

/-- If the `k`-th one exists at position `i`, then the rank
up to `i` is exactly `k` and the bit at `i` is `true`:
stated as: `bselect bv k = some i → brank bv i = k ∧
bv[i]? = some true`. -/
theorem bselect_spec (bv : List Bool) (k i : ℕ)
    (h : bselect bv k = some i) :
    brank bv i = k ∧ bv[i]? = some true := by
  induction bv generalizing k i with
  | nil => simp [bselect] at h
  | cons hd tl ih =>
    cases hd with
    | false =>
      simp only [bselect] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨hr, hg⟩ := ih _ _ hj
      refine ⟨?_, ?_⟩
      · rw [brank_cons_false]
        exact hr
      · rw [List.getElem?_cons_succ]
        exact hg
    | true =>
      cases k with
      | zero =>
        simp only [bselect] at h
        cases h
        exact ⟨rfl, rfl⟩
      | succ k =>
        simp only [bselect] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        obtain ⟨hr, hg⟩ := ih _ _ hj
        refine ⟨?_, ?_⟩
        · rw [brank_cons_true, hr]
        · rw [List.getElem?_cons_succ]
          exact hg

end
