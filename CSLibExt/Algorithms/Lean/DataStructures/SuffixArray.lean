/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Sort
public import Mathlib.Order.Defs.LinearOrder

/-!
# Suffix arrays

This file defines the suffix array of a list over a linearly ordered alphabet: the
starting indices of the suffixes, sorted by the suffixes themselves in lexicographic
order. The array is a permutation of `List.range s.length`, and mapping each index to
its suffix gives a pairwise sorted list. The longest-common-prefix length `lcp` is
defined directly on lists over any alphabet with decidable equality (no order is
needed), with its basic bounds, symmetry, agreement on the common-prefix
truncation, and a maximality characterization
(`le_lcp_iff : q ≤ lcp x y ↔ q ≤ min x.length y.length ∧ x.take q = y.take q`)
showing it is the *longest* such length, not merely an agreeing one. Only
suffix sorting and `lcpArray` require the linear order. The `lcpArray`
records the LCP length of each pair of adjacent suffixes in suffix-array order.

Suffixes here are the non-empty suffixes `s.drop i` for `i < s.length`; `suffixes`
is `List.tails`, which additionally ends with the empty suffix.

Out of scope: the linear-time Kasai construction of the LCP array and any linear or
near-linear suffix-array construction (the definition uses `List.mergeSort` with
suffix comparison, so no complexity bound is claimed). Suffix trees are out of scope
for this module; a suffix-tree representation belongs in its own module with a
source-indexed validity predicate and construction.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

namespace SuffixArray

variable {α : Type u} [LinearOrder α]

/-- The suffix of `s` starting at index `i`. Indices at or past the end give `[]`. -/
def suffix (s : List α) (i : Nat) : List α :=
  s.drop i

omit [LinearOrder α] in
@[simp] theorem suffix_zero (s : List α) : suffix s 0 = s :=
  List.drop_zero

omit [LinearOrder α] in
@[simp] theorem suffix_length (s : List α) (i : Nat) :
    (suffix s i).length = s.length - i :=
  List.length_drop

omit [LinearOrder α] in
theorem suffix_length_le (s : List α) (i : Nat) : (suffix s i).length ≤ s.length := by
  rw [suffix_length]
  exact Nat.sub_le s.length i

/-- All suffixes of `s`, longest first, ending with the empty suffix. -/
def suffixes (s : List α) : List (List α) :=
  s.tails

omit [LinearOrder α] in
@[simp] theorem suffixes_length (s : List α) : (suffixes s).length = s.length + 1 := by
  induction s with
  | nil => rfl
  | cons a as ih =>
      rw [show suffixes (a :: as) = (a :: as) :: suffixes as from rfl]
      simp [ih]

/-- The suffix array of `s`: the indices `0 … s.length - 1` sorted by their suffixes
in lexicographic order. Equal suffixes cannot occur for distinct in-range indices
(their lengths differ), so the sorted order agrees with the usual specification up
to the merge sort's handling of the comparison. -/
def suffixArray (s : List α) : List Nat :=
  (List.range s.length).mergeSort (fun i j => decide (suffix s i ≤ suffix s j))

/-- The suffix array is a permutation of all starting indices. -/
theorem suffixArray_perm (s : List α) :
    (suffixArray s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

@[simp] theorem suffixArray_length (s : List α) :
    (suffixArray s).length = s.length := by
  rw [(suffixArray_perm s).length_eq, List.length_range]

theorem mem_suffixArray_iff {s : List α} {i : Nat} :
    i ∈ suffixArray s ↔ i < s.length := by
  rw [(suffixArray_perm s).mem_iff, List.mem_range]

theorem suffixArray_nodup (s : List α) : (suffixArray s).Nodup :=
  (suffixArray_perm s).nodup_iff.mpr List.nodup_range

/-- The suffixes in suffix-array order are pairwise sorted in lexicographic order. -/
theorem pairwise_suffix_suffixArray (s : List α) :
    List.Pairwise (· ≤ ·) ((suffixArray s).map (suffix s)) := by
  have htrans : ∀ a b c : Nat,
      decide (suffix s a ≤ suffix s b) = true →
      decide (suffix s b ≤ suffix s c) = true →
      decide (suffix s a ≤ suffix s c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htotal : ∀ a b : Nat,
      (decide (suffix s a ≤ suffix s b) || decide (suffix s b ≤ suffix s a)) = true := by
    intro a b
    cases le_total (suffix s a) (suffix s b) with
    | inl h => simp [h]
    | inr h => simp [h]
  have h := List.pairwise_mergeSort htrans htotal (List.range s.length)
  rw [List.pairwise_map]
  exact h.imp (fun {a b} hab => of_decide_eq_true hab)

section

variable {α : Type u} [DecidableEq α]

/-- The length of the longest common prefix of two lists. Only equality on
the alphabet is tested, so no order instance is required. -/
def lcp : List α → List α → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0

@[simp] theorem lcp_nil_left (y : List α) : lcp ([] : List α) y = 0 :=
  rfl

@[simp] theorem lcp_nil_right (x : List α) : lcp x ([] : List α) = 0 := by
  cases x <;> rfl

@[simp] theorem lcp_self (x : List α) : lcp x x = x.length := by
  induction x with
  | nil => rfl
  | cons a as ih => simp [lcp, ih]

theorem lcp_le_left (x y : List α) : lcp x y ≤ x.length := by
  induction x generalizing y with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
      cases y with
      | nil => exact Nat.zero_le _
      | cons b bs =>
          by_cases h : a = b <;> simp [lcp, h, Nat.succ_le_succ (ih (y := bs))]

theorem lcp_le_right (x y : List α) : lcp x y ≤ y.length := by
  induction x generalizing y with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
      cases y with
      | nil => exact Nat.zero_le _
      | cons b bs =>
          by_cases h : a = b <;> simp [lcp, h, Nat.succ_le_succ (ih (y := bs))]

theorem lcp_le_min (x y : List α) : lcp x y ≤ min x.length y.length :=
  Nat.le_min.mpr ⟨lcp_le_left x y, lcp_le_right x y⟩

theorem lcp_comm (x y : List α) : lcp x y = lcp y x := by
  induction x generalizing y with
  | nil => simp
  | cons a as ih =>
      cases y with
      | nil => rfl
      | cons b bs =>
          by_cases h : a = b
          · subst h
            simp [lcp, ih]
          · simp [lcp, h, Ne.symm h]

/-- Both lists agree on their first `lcp x y` elements. -/
theorem take_lcp_eq (x y : List α) : x.take (lcp x y) = y.take (lcp x y) := by
  induction x generalizing y with
  | nil => simp
  | cons a as ih =>
      cases y with
      | nil => simp
      | cons b bs =>
          by_cases h : a = b
          · subst h
            simp [lcp, ih]
          · simp [lcp, h]

/-- Any shorter prefix length also agrees: truncating the common prefix
of length `lcp x y` at `q ≤ lcp x y` still gives equal prefixes. -/
theorem take_eq_of_le_lcp {x y : List α} {q : Nat} (h : q ≤ lcp x y) :
    x.take q = y.take q := by
  calc
    x.take q = (x.take (lcp x y)).take q := by
        rw [List.take_take, Nat.min_eq_left h]
    _ = (y.take (lcp x y)).take q := by rw [take_lcp_eq]
    _ = y.take q := by rw [List.take_take, Nat.min_eq_left h]

private theorem le_lcp_of_take_eq {x y : List α} {q : Nat}
    (hmin : q ≤ min x.length y.length) (htake : x.take q = y.take q) :
    q ≤ lcp x y := by
  induction x generalizing y q with
  | nil =>
      have hq : q ≤ 0 := by simpa using hmin
      simp [Nat.le_zero.mp hq]
  | cons a as ih =>
      cases y with
      | nil =>
          have hq : q ≤ 0 := by simpa using hmin
          simp [Nat.le_zero.mp hq]
      | cons b bs =>
          cases q with
          | zero => exact Nat.zero_le _
          | succ q =>
              have htake' : a :: as.take q = b :: bs.take q := htake
              injection htake' with hab hrest
              have hmin' : q ≤ min as.length bs.length := by
                simp only [List.length_cons] at hmin
                omega
              have hrec := ih hmin' hrest
              have hstep : lcp (a :: as) (b :: bs) = lcp as bs + 1 := by
                simp [lcp, hab]
              rw [hstep]
              omega

/-- Maximality of `lcp`: `q` is below the longest-common-prefix length
exactly when it fits in both lists and their first `q` elements agree.
In particular clients can derive `q ≤ lcp x y` from prefix agreement
without unfolding the recursion (a constant-zero function would not
satisfy this). -/
theorem le_lcp_iff {x y : List α} {q : Nat} :
    q ≤ lcp x y ↔ q ≤ min x.length y.length ∧ x.take q = y.take q :=
  ⟨fun h => ⟨le_trans h (lcp_le_min x y), take_eq_of_le_lcp h⟩,
    fun h => le_lcp_of_take_eq h.1 h.2⟩

/-- The LCP lengths of consecutive entries of an index list, in order. The result
has one entry per adjacent pair. -/
def adjLcp (s : List α) : List Nat → List Nat
  | [] => []
  | [_] => []
  | i :: j :: rest => lcp (suffix s i) (suffix s j) :: adjLcp s (j :: rest)

theorem adjLcp_length (s : List α) (l : List Nat) :
    (adjLcp s l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      cases l with
      | nil => rfl
      | cons j rest => simp [adjLcp, ih]

theorem le_of_mem_adjLcp {s : List α} {l : List Nat} {k : Nat}
    (h : k ∈ adjLcp s l) : k ≤ s.length := by
  induction l with
  | nil => simp [adjLcp] at h
  | cons i l ih =>
      cases l with
      | nil => simp [adjLcp] at h
      | cons j rest =>
          simp only [adjLcp, List.mem_cons] at h
          cases h with
          | inl h =>
              rw [h]
              exact le_trans (lcp_le_left _ _) (suffix_length_le s i)
          | inr h => exact ih h

end

/-- The LCP array of `s`: the LCP length of each pair of adjacent suffixes in
suffix-array order. This is the naïve value by definition; the linear-time Kasai
construction is out of scope. -/
def lcpArray (s : List α) : List Nat :=
  adjLcp s (suffixArray s)

@[simp] theorem lcpArray_length (s : List α) : (lcpArray s).length = s.length - 1 := by
  rw [lcpArray, adjLcp_length, suffixArray_length]

theorem le_of_mem_lcpArray {s : List α} {k : Nat} (h : k ∈ lcpArray s) :
    k ≤ s.length :=
  le_of_mem_adjLcp h

end SuffixArray

end Cslib.Algorithms.Lean
