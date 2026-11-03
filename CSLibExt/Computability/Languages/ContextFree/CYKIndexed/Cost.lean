/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  CSLibExt.Computability.Languages.ContextFree.CYKIndexed.Correctness
public import Mathlib.Tactic.Linarith

/-!
# Cubic cost of indexed CYK

Bounds cover the actual accumulated `TimeM` annotations: full membership
scans, split scans, production scans, all cells, row conversion, table
allocation/update, input conversion and the final membership test.
Equality costs and the number of enumerated rules are explicit constants.
This is the abstract indexed word model documented in `CYKIndexed`, not a
bound on Lean persistent-array copying, arbitrary-size integer arithmetic,
or the runtime of an arbitrary `DecidableEq` implementation.
-/

@[expose] public section

namespace Cslib.Language.CYKIndexed

variable {T N : Type*} [DecidableEq N]

/-- Exact charge for a full membership scan, including a failed scan. -/
theorem member_time (nc : ℕ) (a : N) (xs : List N) :
    (member nc a xs).time = 1 + xs.length * (nc + 3) := by
  induction xs with
  | nil => simp [member]
  | cons b bs ih => simp [member, ih, Nat.add_mul]; omega

variable [DecidableEq T]

/-- Even with duplicates, a cell never exceeds the rule enumeration length. -/
theorem cell_length (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (i len : ℕ)
    (rs : List (ContextFreeRule T N)) :
    (cell tc nc w tbl i len rs).ret.length ≤ rs.length := by
  induction rs with
  | nil => simp [cell]
  | cons r rs ih =>
      simp only [cell, List.length_cons]
      split
      · simpa only [List.length_cons, Nat.add_le_add_iff_right] using ih
      · exact ih.trans (Nat.le_succ _)

/-- All table cells, including invalid/default positions, have bounded
membership-scan length. This invariant is proved from construction. -/
theorem lookup_length (tc nc : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) (depth i len : ℕ) :
    (lookup (table tc nc w rs depth).ret i len).length ≤ rs.length := by
  induction depth with
  | zero =>
      simp only [table, lookup, Array.getElem?_replicate]
      split <;> simp
  | succ depth ih =>
      by_cases h : depth + 1 = len
      · subst len
        simp only [table, lookup, Array.set!,
          Array.getElem?_setIfInBounds, ite_true, table_size]
        by_cases hd : depth + 1 < w.size + 1
        · simp only [hd, ite_true, Option.getD_some,
            List.getElem?_toArray, row_get, Nat.zero_add]
          split
          · simpa using cell_length tc nc w
              (table tc nc w rs depth).ret i (depth + 1) rs
          · simp
        · simp [hd]
      · rw [lookup_table_other tc nc w rs depth i len h]
        exact ih

omit [DecidableEq T] in
/-- Each split pays for both indexed cell reads and both membership scans. -/
theorem splits_time_le (nc : ℕ) (tbl : Array (Array (List N)))
    (r : ℕ) (htbl : ∀ i len, (lookup tbl i len).length ≤ r)
    (i len : ℕ) (b c : N) (count : ℕ) :
    (splits nc tbl i len b c count).time ≤
      1 + count * (2 * r * (nc + 3) + 18) := by
  induction count with
  | zero => simp [splits]
  | succ count ih =>
      have hl := Nat.mul_le_mul_right (nc + 3) (htbl i (count + 1))
      have hr := Nat.mul_le_mul_right (nc + 3)
        (htbl (i + (count + 1)) (len - (count + 1)))
      simp only [splits, member_time]
      nlinarith

/-- Output inspection is bounded; only binary productions scan splits. -/
theorem fits_time_le (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (r : ℕ)
    (htbl : ∀ i len, (lookup tbl i len).length ≤ r)
    (i len : ℕ) (out : List (Symbol T N)) :
    (fits tc nc w tbl i len out).time ≤
      tc + 12 + len * (2 * r * (nc + 3) + 18) := by
  match out with
  | [.terminal a] => simp [fits]
  | [.nonterminal b, .nonterminal c] =>
      have h := splits_time_le nc tbl r htbl i len b c (len - 1)
      have hm := Nat.mul_le_mul_right (2 * r * (nc + 3) + 18)
        (Nat.sub_le len 1)
      simp only [fits]
      omega
  | [] | [.nonterminal _] | .terminal _ :: _ :: _ |
      .nonterminal _ :: .terminal _ :: _ |
      .nonterminal _ :: .nonterminal _ :: _ :: _ => simp [fits]; omega

/-- A cell charges every rule, its test, and its possible output cons. -/
theorem cell_time_le (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (r : ℕ)
    (htbl : ∀ i len, (lookup tbl i len).length ≤ r)
    (i len : ℕ) (rs : List (ContextFreeRule T N)) :
    (cell tc nc w tbl i len rs).time ≤
      1 + rs.length * (tc + 17 + len * (2 * r * (nc + 3) + 18)) := by
  induction rs with
  | nil => simp [cell]
  | cons rule rs ih =>
      have h := fits_time_le tc nc w tbl r htbl i len rule.output
      simp only [cell, List.length_cons]
      nlinarith

/-- Row cost counts all starts, not only successful or distinct factors. -/
theorem row_time_le (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (r : ℕ)
    (htbl : ∀ i len, (lookup tbl i len).length ≤ r)
    (len : ℕ) (rs : List (ContextFreeRule T N)) (i count : ℕ) :
    (row tc nc w tbl len rs i count).time ≤
      1 + count * (5 + rs.length *
        (tc + 17 + len * (2 * r * (nc + 3) + 18))) := by
  induction count generalizing i with
  | zero => simp [row]
  | succ count ih =>
      have hc := cell_time_le tc nc w tbl r htbl i len rs
      have hr := ih (i + 1)
      simp only [row]
      nlinarith

/-- Table cost includes allocation, every row conversion and every update.
The memory-size hypothesis needed for split costs is discharged internally. -/
theorem table_time_le (tc nc : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) (depth : ℕ) (hd : depth ≤ w.size) :
    (table tc nc w rs depth).time ≤ w.size + 4 + depth *
      (9 + (w.size + 1) * (7 + rs.length *
        (tc + 17 + w.size * (2 * rs.length * (nc + 3) + 18)))) := by
  induction depth with
  | zero => simp [table]
  | succ depth ih =>
      have hp := ih (by omega)
      have hr := row_time_le tc nc w (table tc nc w rs depth).ret
        rs.length (lookup_length tc nc w rs depth) (depth + 1) rs 0
        (w.size + 1)
      have hm := Nat.mul_le_mul_left ((w.size + 1) * rs.length)
        (Nat.mul_le_mul_right (2 * rs.length * (nc + 3) + 18) hd)
      simp only [table]
      nlinarith

/-- The linear row-conversion charge uses the actual number of entries. -/
theorem row_length (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (len : ℕ)
    (rs : List (ContextFreeRule T N)) (i count : ℕ) :
    (row tc nc w tbl len rs i count).ret.length = count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih => simp [row, ih]

omit [DecidableEq T] in
/-- Exact cost of the empty-input production scan. -/
theorem epsilon_time (nc : ℕ) (start : N)
    (rs : List (ContextFreeRule T N)) :
    (epsilon nc start rs).time = 1 + rs.length * (nc + 6) := by
  induction rs with
  | nil => simp [epsilon]
  | cons r rs ih => simp [epsilon, ih, Nat.add_mul]; omega

private theorem cubic_domination (n p q s : ℕ) :
    n + 4 + n * (9 + (n + 1) * (7 + p + n * q)) +
      1 + s + 3 * n + 12 ≤ (p + q + s + 40) * (n + 1) ^ 3 := by
  nlinarith only [Nat.zero_le ((p + s + 40) * n ^ 3),
    Nat.zero_le ((2 * q + 2 * p + 3 * s + 113) * n ^ 2),
    Nat.zero_le ((3 * q + 2 * p + 3 * s + 100) * n),
    Nat.zero_le (p + q + 23)]

/-- Explicit cubic bound, for every word including the empty word.
The coefficient depends only on the rule enumeration and equality costs;
no semantic or assumed recurrence hypothesis occurs in this cost theorem. -/
theorem recognizes_time_le (tc nc : ℕ) (start : N)
    (rs : List (ContextFreeRule T N)) (w : List T) :
    (recognizes tc nc start rs w).time ≤
      (rs.length * (tc + nc + 2 * rs.length * (nc + 3) + 38) + 40) *
        (w.length + 1) ^ 3 := by
  cases w with
  | nil =>
      have h := Nat.mul_le_mul_left rs.length
        (show nc + 6 ≤ tc + nc + 2 * rs.length * (nc + 3) + 38 by omega)
      simp only [recognizes, epsilon_time, List.length_nil,
        Nat.zero_add, one_pow, Nat.mul_one]
      omega
  | cons x xs =>
      have ht := table_time_le tc nc (x :: xs).toArray rs
        (x :: xs).length (by simp)
      have hm := Nat.mul_le_mul_right (nc + 3)
        (lookup_length tc nc (x :: xs).toArray rs (x :: xs).length
          0 (x :: xs).length)
      simp only [recognizes, List.size_toArray, member_time]
      simp only [List.size_toArray] at ht hm
      have hp := cubic_domination (x :: xs).length (rs.length * (tc + 17))
        (rs.length * (2 * rs.length * (nc + 3) + 18))
        (rs.length * (nc + 3))
      nlinarith only [ht, hm, hp]

/-- In the usual nonempty-input form, the bound is a constant times `n³`. -/
theorem recognizes_time_le_cubic (tc nc : ℕ) (start : N)
    (rs : List (ContextFreeRule T N)) (w : List T) (hw : w ≠ []) :
    (recognizes tc nc start rs w).time ≤
      8 * (rs.length *
        (tc + nc + 2 * rs.length * (nc + 3) + 38) + 40) * w.length ^ 3 := by
  have hn := List.length_pos_iff.mpr hw
  have hp := Nat.pow_le_pow_left
    (show w.length + 1 ≤ 2 * w.length by omega) 3
  have hm := Nat.mul_le_mul_left
    (rs.length * (tc + nc + 2 * rs.length * (nc + 3) + 38) + 40) hp
  have h := recognizes_time_le tc nc start rs w
  nlinarith only [h, hm]

end Cslib.Language.CYKIndexed
