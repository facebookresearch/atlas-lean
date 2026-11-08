/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Counting
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Radix sort

This module implements least-significant-digit radix sort from Cormen, Leiserson, Rivest, and
Stein, *Introduction to Algorithms*, 4th ed., Section 8.3. Digit vectors are fixed-width and stored
most-significant first. The implementation visits indices from `d - 1` down to `0`, applying the
stable counting sort from `CSLibExt.Algorithms.Lean.Sort.Counting` at every pass.

The radix is at least two. A pass charges exactly the counting-sort cost for `b` digit values;
selecting a digit is the pass's key-evaluation charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

/-- Stable least-significant-digit radix sort for fixed-width most-significant-first digits. -/
def radixSort {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (_hb : 2 ≤ b) : TimeM Nat (Array α) :=
  let rec loop : (remaining : Nat) → remaining ≤ d → Array α → TimeM Nat (Array α)
    | 0, _, current => pure current
    | remaining + 1, hremaining, current => do
        let i : Fin d := ⟨remaining, by omega⟩
        let current ← countingSort (fun x => (digits x)[i.val]'i.isLt) current
        loop remaining (by omega) current
  loop d (by omega) input

private theorem radixSort_loop_perm {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (remaining : Nat) (hremaining : remaining ≤ d)
    (input : Array α) :
    List.Perm (radixSort.loop digits remaining hremaining input).ret.toList input.toList := by
  induction remaining generalizing input with
  | zero => simp [radixSort.loop]
  | succ remaining ih =>
      simp only [radixSort.loop, ret_bind]
      exact (ih (by omega) _).trans (countingSort_correct _ input).2.1

private def SuffixLE {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (start : Nat) (x y : α) : Prop :=
  (∀ (j : Nat) (hj : j < d), start ≤ j → (digits x)[j] = (digits y)[j]) ∨
    ∃ (i : Nat) (hi : i < d), start ≤ i ∧
      (∀ (j : Nat) (hj : j < d), start ≤ j → j < i →
        (digits x)[j] = (digits y)[j]) ∧
      (digits x)[i] < (digits y)[i]

private theorem suffixLE_top {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (x y : α) : SuffixLE digits d x y := by
  left
  intro j hj hdj
  omega

private theorem suffixLE_step {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (start : Nat) (hstart : start < d) (x y : α)
    (h : (digits x)[start] < (digits y)[start] ∨
      (digits x)[start] = (digits y)[start] ∧ SuffixLE digits (start + 1) x y) :
    SuffixLE digits start x y := by
  rcases h with hlt | ⟨heq, htail⟩
  · right
    exact ⟨start, hstart, le_rfl, by
      intro j hj hsj hjs
      omega, hlt⟩
  · rcases htail with hall | ⟨i, hi, hsi, hbefore, hlt⟩
    · left
      intro j hj hsj
      by_cases hjs : j = start
      · simpa [hjs] using heq
      · exact hall j hj (by omega)
    · right
      exact ⟨i, hi, by omega, by
        intro j hj hsj hji
        by_cases hjs : j = start
        · simpa [hjs] using heq
        · exact hbefore j hj (by omega) hji, hlt⟩

private theorem suffixLE_zero_le {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) {x y : α} (h : SuffixLE digits 0 x y) :
    digits x ≤ digits y := by
  rw [Vector.le_iff_exists]
  rcases h with hall | ⟨i, hi, hsi, hbefore, hlt⟩
  · left
    apply Vector.ext
    intro j hj
    exact hall j hj (by omega)
  · right
    exact ⟨i, hi, by
      intro j hj
      exact hbefore j (by omega) (by omega) hj, hlt⟩

private theorem pairwise_lex_of_key_and_filters {α : Type u} {k : Nat}
    (key : α → Fin k) (R : α → α → Prop) (xs : List α)
    (hkey : List.Pairwise (fun x y => key x ≤ key y) xs)
    (hfilters : ∀ q : Fin k,
      List.Pairwise R (xs.filter fun x => key x == q)) :
    List.Pairwise
      (fun x y => key x < key y ∨ (key x = key y ∧ R x y)) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hkey ⊢
      constructor
      · intro y hy
        have hle := hkey.1 y hy
        by_cases hlt : key x < key y
        · exact Or.inl hlt
        · right
          have heq : key x = key y := by
            apply Fin.ext
            omega
          refine ⟨heq, ?_⟩
          have hg := hfilters (key x)
          simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte] at hg
          rw [List.pairwise_cons] at hg
          exact hg.1 y (List.mem_filter.mpr ⟨hy, by simp [← heq]⟩)
      · apply ih hkey.2
        intro q
        have hg := hfilters q
        by_cases hx : key x = q
        · subst q
          simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte] at hg
          simpa using (List.pairwise_cons.mp hg).2
        · have hb : (key x == q) = false := beq_false_of_ne hx
          simpa only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte] using hg

private theorem countingPass_suffix {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (start : Nat) (hstart : start < d)
    (input : Array α)
    (hsorted : List.Pairwise (SuffixLE digits (start + 1)) input.toList) :
    List.Pairwise (SuffixLE digits start)
      (countingSort (fun x => (digits x)[start]'hstart) input).ret.toList := by
  have hcorrect := countingSort_correct (fun x => (digits x)[start]'hstart) input
  have hgroups : ∀ q : Fin b,
      List.Pairwise (SuffixLE digits (start + 1))
        ((countingSort (fun x => (digits x)[start]'hstart) input).ret.toList.filter
          fun x => (digits x)[start]'hstart == q) := by
    intro q
    rw [hcorrect.2.2 q]
    exact hsorted.filter _
  exact (pairwise_lex_of_key_and_filters _ _ _ hcorrect.1 hgroups).imp fun h =>
    suffixLE_step digits start hstart _ _ h

private theorem radixSort_loop_suffix {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (remaining : Nat) (hremaining : remaining ≤ d)
    (input : Array α) (hsorted : List.Pairwise (SuffixLE digits remaining) input.toList) :
    List.Pairwise (SuffixLE digits 0)
      (radixSort.loop digits remaining hremaining input).ret.toList := by
  induction remaining generalizing input with
  | zero => simpa [radixSort.loop] using hsorted
  | succ remaining ih =>
      simp only [radixSort.loop, ret_bind]
      apply ih (by omega)
      exact countingPass_suffix digits remaining (by omega) input hsorted

private theorem filter_full_digit {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (xs : List α) (v : Vector (Fin b) d)
    (i : Fin d) :
    (xs.filter fun x => (digits x)[i.val]'i.isLt == v[i.val]'i.isLt).filter
        (fun x => digits x == v) =
      xs.filter fun x => digits x == v := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  by_cases h : digits x = v
  · subst v
    simp
  · have hb : (digits x == v) = false := beq_false_of_ne h
    simp [hb]

private theorem countingPass_full_stable {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (input : Array α) (i : Fin d)
    (v : Vector (Fin b) d) :
    (countingSort (fun x => (digits x)[i.val]'i.isLt) input).ret.toList.filter
        (fun x => digits x == v) =
      input.toList.filter fun x => digits x == v := by
  have hpass := (countingSort_correct (fun x => (digits x)[i.val]'i.isLt) input).2.2
    (v[i.val]'i.isLt)
  calc
    (countingSort (fun x => (digits x)[i.val]'i.isLt) input).ret.toList.filter
          (fun x => digits x == v) =
        ((countingSort (fun x => (digits x)[i.val]'i.isLt) input).ret.toList.filter
          fun x => (digits x)[i.val]'i.isLt == v[i.val]'i.isLt).filter
            (fun x => digits x == v) := (filter_full_digit digits _ v i).symm
    _ = (input.toList.filter
          fun x => (digits x)[i.val]'i.isLt == v[i.val]'i.isLt).filter
            (fun x => digits x == v) := congrArg (fun xs => xs.filter fun x => digits x == v) hpass
    _ = input.toList.filter (fun x => digits x == v) := filter_full_digit digits _ v i

private theorem radixSort_loop_full_stable {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (remaining : Nat) (hremaining : remaining ≤ d)
    (input : Array α) (v : Vector (Fin b) d) :
    (radixSort.loop digits remaining hremaining input).ret.toList.filter
        (fun x => digits x == v) =
      input.toList.filter fun x => digits x == v := by
  induction remaining generalizing input with
  | zero => simp [radixSort.loop]
  | succ remaining ih =>
      simp only [radixSort.loop, ret_bind]
      calc
        (radixSort.loop digits remaining _
            (countingSort (fun x => (digits x)[remaining]'(by omega)) input).ret).ret.toList.filter
              (fun x => digits x == v) =
            (countingSort (fun x => (digits x)[remaining]'(by omega)) input).ret.toList.filter
              (fun x => digits x == v) := ih (by omega) _
        _ = input.toList.filter (fun x => digits x == v) :=
          countingPass_full_stable digits input ⟨remaining, by omega⟩ v

private def digitListValue {b : Nat} (xs : List (Fin b)) : Nat :=
  Nat.ofDigits b (xs.reverse.map Fin.val)

private theorem digitListValue_cons {b : Nat} (x : Fin b) (xs : List (Fin b)) :
    digitListValue (x :: xs) = digitListValue xs + b ^ xs.length * x.val := by
  simpa [digitListValue] using
    (Nat.ofDigits_reverse_cons (b := b) (xs.map Fin.val) x.val)

private theorem digitListValue_lt_pow {b : Nat} (hb : 2 ≤ b) (xs : List (Fin b)) :
    digitListValue xs < b ^ xs.length := by
  unfold digitListValue
  rw [show xs.length = (xs.reverse.map Fin.val).length by simp]
  apply Nat.ofDigits_lt_base_pow_length (by omega)
  intro n hn
  simp only [List.mem_map, List.mem_reverse] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  exact x.isLt

private theorem digitListValue_le_of_lex {b : Nat} (hb : 2 ≤ b)
    (xs ys : List (Fin b)) (hlen : xs.length = ys.length) (hle : xs ≤ ys) :
    digitListValue xs ≤ digitListValue ys := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst ys
      exact le_rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htailLength : xs.length = ys.length := by simpa using hlen
          rw [List.cons_le_cons_iff] at hle
          rcases hle with hxy | ⟨hxy, htail⟩
          · rw [digitListValue_cons, digitListValue_cons, ← htailLength]
            have hlow := digitListValue_lt_pow hb xs
            have hdigit : x.val + 1 ≤ y.val := by omega
            apply Nat.le_of_lt
            calc
                digitListValue xs + b ^ xs.length * x.val <
                    b ^ xs.length + b ^ xs.length * x.val := Nat.add_lt_add_right hlow _
                _ = b ^ xs.length * (x.val + 1) := by
                  simp [Nat.mul_add, Nat.add_comm]
                _ ≤ b ^ xs.length * y.val := Nat.mul_le_mul_left _ hdigit
                _ ≤ digitListValue ys + b ^ xs.length * y.val := by omega
          · subst y
            rw [digitListValue_cons, digitListValue_cons, ← htailLength]
            exact Nat.add_le_add (ih ys htailLength htail) le_rfl

private theorem digitVectorValue_le {b d : Nat} (hb : 2 ≤ b)
    {xs ys : Vector (Fin b) d} (hxy : xs ≤ ys) :
    Nat.ofDigits b (xs.toList.reverse.map Fin.val) ≤
      Nat.ofDigits b (ys.toList.reverse.map Fin.val) := by
  apply digitListValue_le_of_lex hb xs.toList ys.toList (by simp)
  exact Vector.le_toList.mpr hxy

/-- Radix sort returns a lexicographically and numerically sorted stable permutation. -/
theorem radixSort_correct {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    List.Pairwise (fun x y => digits x ≤ digits y) (radixSort digits input hb).ret.toList ∧
      List.Perm (radixSort digits input hb).ret.toList input.toList ∧
      (∀ v : Vector (Fin b) d,
        (radixSort digits input hb).ret.toList.filter (fun x => digits x == v) =
          input.toList.filter fun x => digits x == v) ∧
      List.Pairwise
        (fun x y =>
          Nat.ofDigits b ((digits x).toList.reverse.map Fin.val) ≤
            Nat.ofDigits b ((digits y).toList.reverse.map Fin.val))
        (radixSort digits input hb).ret.toList := by
  have hstart : List.Pairwise (SuffixLE digits d) input.toList :=
    List.pairwise_of_forall fun x y => suffixLE_top digits x y
  have hsuffix := radixSort_loop_suffix digits d (by omega) input hstart
  have hlex : List.Pairwise (fun x y => digits x ≤ digits y)
      (radixSort.loop digits d (by omega) input).ret.toList :=
    hsuffix.imp fun h => suffixLE_zero_le digits h
  have hperm := radixSort_loop_perm digits d (by omega) input
  have hstable := radixSort_loop_full_stable digits d (by omega) input
  have hnumeric := hlex.imp fun h => digitVectorValue_le hb h
  unfold radixSort
  exact ⟨hlex, hperm, hstable, hnumeric⟩

private theorem radixSort_loop_time {α : Type u} {b d : Nat}
    (digits : α → Vector (Fin b) d) (remaining : Nat) (hremaining : remaining ≤ d)
    (input : Array α) :
    (radixSort.loop digits remaining hremaining input).time ≤
      remaining * (7 * input.size + 3 * b) := by
  induction remaining generalizing input with
  | zero => simp [radixSort.loop]
  | succ remaining ih =>
      simp only [radixSort.loop, time_bind]
      have hpass := countingSort_time
        (fun x => (digits x)[remaining]'(by omega)) input
      have hperm := (countingSort_correct
        (fun x => (digits x)[remaining]'(by omega)) input).2.1
      have hsize : (countingSort (fun x => (digits x)[remaining]'(by omega)) input).ret.size =
          input.size := by
        simpa using hperm.length_eq
      have hrec := ih
        (by omega)
        (countingSort (fun x => (digits x)[remaining]'(by omega)) input).ret
      rw [hsize] at hrec
      have hsum := Nat.add_le_add hpass hrec
      have heq : (7 * input.size + 3 * b) + remaining * (7 * input.size + 3 * b) =
          (remaining + 1) * (7 * input.size + 3 * b) := by
        simp [Nat.add_mul, Nat.add_comm]
      rw [← heq]
      exact hsum

/-- Radix sort uses at most `d * (7 * n + 3 * b)` charged operations. -/
theorem radixSort_time {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    (radixSort digits input hb).time ≤ d * (7 * input.size + 3 * b) := by
  unfold radixSort
  exact radixSort_loop_time digits d (by omega) input

end Cslib.Algorithms.Lean.TimeM
