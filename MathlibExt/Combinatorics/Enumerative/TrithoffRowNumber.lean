/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import MathlibExt.Combinatorics.Enumerative.TrithoffRowDifference

/-!
# Row numbers of the Trithoff array

If the Tribonacci representation of `n` ends in one, its one-based row number is `n` minus
the value of the remaining digits. The Tribonacci recurrence also gives a weighted digit
sum for that row number.
-/

namespace MetaMathlibExt

namespace trithoff_row_number_eq

private def Valid (w : List ℕ) : Prop :=
  (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w

/-- A one can be placed before this tail without creating three consecutive ones. -/
private def free (a : List ℕ) : Bool :=
  !(a.getD 0 0 == 1 && a.getD 1 0 == 1)

private theorem pair_prefix (a : List ℕ) :
    [1, 1] <+: a ↔ free a = false := by
  rcases a with _ | ⟨x, _ | ⟨y, a⟩⟩ <;> simp [free]
  omega

private theorem valid_cons (d : ℕ) (a : List ℕ) :
    Valid (d :: a) ↔ Valid a ∧ d ≤ 1 ∧ (d = 1 → free a = true) := by
  simp only [Valid, List.forall_mem_cons, List.infix_cons_iff, List.cons_prefix_cons,
    pair_prefix]
  cases free a <;> simp <;> grind

/-- Evaluate the digits after shifting all their weights by `k` places. -/
private def value (w : List ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3 + k)

@[simp] private theorem value_nil (k : ℕ) : value [] k = 0 := by simp [value]

private theorem value_cons (d : ℕ) (a : List ℕ) (k : ℕ) :
    value (d :: a) k = d * tribonacci (k + 3) + value a (k + 1) := by
  simp [value, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Increment a word. A carry replaces the low digit by zero and increments its tail. -/
private def inc : List ℕ → List ℕ
  | [] => [1]
  | d :: a => if d = 0 ∧ free a then 1 :: a else 0 :: inc a

/-- The gap to the next word at shift `k` depends on its initial run of ones. -/
private def gap (w : List ℕ) (k : ℕ) : ℕ :=
  if w.getD 0 0 = 0 then tribonacci (k + 3)
  else if free w then tribonacci (k + 2) + tribonacci (k + 1) else tribonacci (k + 2)

private theorem value_inc (w : List ℕ) (hw : Valid w) (k : ℕ) :
    value (inc w) k = value w k + gap w k := by
  induction w generalizing k with
  | nil => simp [inc, gap, value_cons]
  | cons d a ih =>
    obtain ⟨ha, hd, hf⟩ := (valid_cons d a).mp hw
    have step := ih ha (k + 1)
    have hrec := tribonacci.eq_4 k
    have hrec' := tribonacci.eq_4 (k + 1)
    have hbit : a.getD 0 0 ≤ 1 := by
      cases a with
      | nil => decide
      | cons e a => exact ha.1 e (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl <;>
      cases h : free a <;> rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbit with he | he <;>
      simp_all [inc, gap, value_cons, free, Nat.add_assoc] <;> omega

private theorem gap_zero (a : List ℕ) : gap a 0 = 1 := by
  unfold gap
  split <;> first | rfl | split <;> rfl

private theorem value_inc_zero (a : List ℕ) (ha : Valid a) :
    value (inc a) 0 = value a 0 + 1 := by rw [value_inc a ha, gap_zero]

private theorem value_of_zero_digits {a : List ℕ} (h : ∀ i, a.getD i 0 = 0) (k : ℕ) :
    value a k = 0 := by simp only [value, h, Nat.zero_mul, Finset.sum_const_zero]

/-- To undo a carry, put the largest admissible digit back before the previous tail. -/
private theorem zero_or_inc (w : List ℕ) (hw : Valid w) :
    (∀ i, w.getD i 0 = 0) ∨ ∃ v, Valid v ∧ w = inc v := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons d a ih =>
    obtain ⟨ha, hd, hf⟩ := (valid_cons d a).mp hw
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
    · rcases ih ha with hz | ⟨v, hv, rfl⟩
      · left
        intro i
        cases i with
        | zero => rfl
        | succ j => exact hz j
      · right
        cases h : free v
        · exact ⟨0 :: v, (valid_cons ..).2 (by simp [hv]), by simp [inc, h]⟩
        · exact ⟨1 :: v, (valid_cons ..).2 (by simp [hv, h]), by simp [inc]⟩
    · exact Or.inr ⟨0 :: a, (valid_cons ..).2 (by simp [ha]), by simp [inc, hf rfl]⟩

private theorem tail_digit (a : List ℕ) (i : ℕ) : a.tail.getD i 0 = a.getD (i + 1) 0 := by
  cases a <;> simp

private theorem inc_eq (w : List ℕ) :
    inc w = if w.getD 0 0 = 0 ∧ free w.tail then 1 :: w.tail else 0 :: inc w.tail := by
  cases w <;> rfl

/-- Increment respects equality of digit streams padded with zeros. -/
private theorem inc_congr {a b : List ℕ} (h : ∀ i, a.getD i 0 = b.getD i 0) (i : ℕ) :
    (inc a).getD i 0 = (inc b).getD i 0 := by
  induction i generalizing a b with
  | zero =>
    rw [inc_eq a, inc_eq b]
    simp only [free, tail_digit, h]
    split <;> rfl
  | succ i ih =>
    rw [inc_eq a, inc_eq b]
    simp only [free, tail_digit, h]
    split
    · exact (tail_digit a i).trans ((h _).trans (tail_digit b i).symm)
    · exact ih (fun j => (tail_digit a j).trans ((h _).trans (tail_digit b j).symm))

private theorem digits_of_value_zero {w : List ℕ} (hw : Valid w) (hz : value w 0 = 0) :
    ∀ i, w.getD i 0 = 0 := by
  rcases zero_or_inc w hw with h | ⟨v, hv, rfl⟩
  · exact h
  · rw [value_inc_zero v hv] at hz
    omega

private theorem exists_prev {w : List ℕ} {n : ℕ} (hw : Valid w) (hn : value w 0 = n + 1) :
    ∃ v, Valid v ∧ w = inc v ∧ value v 0 = n := by
  rcases zero_or_inc w hw with hz | ⟨v, hv, rfl⟩
  · rw [value_of_zero_digits hz] at hn
    omega
  · exact ⟨v, hv, rfl, by simpa [value_inc_zero v hv] using hn⟩

private theorem digits_unique (n : ℕ) {a b : List ℕ} (ha : Valid a) (hb : Valid b)
    (h₁ : value a 0 = n) (h₂ : value b 0 = n) : ∀ i, a.getD i 0 = b.getD i 0 := by
  induction n generalizing a b with
  | zero => exact fun i => (digits_of_value_zero ha h₁ i).trans (digits_of_value_zero hb h₂ i).symm
  | succ n ih =>
    obtain ⟨u, hu, rfl, h₃⟩ := exists_prev ha h₁
    obtain ⟨v, hv, rfl, h₄⟩ := exists_prev hb h₂
    exact inc_congr (ih hu hv h₃ h₄)

private def column (n : ℕ) : Prop :=
  0 < n ∧ ∃ w, IsTribonacciRepr w n ∧ w.getD 0 0 = 1

private theorem column_iff (w : List ℕ) (hw : Valid w) :
    column (value w 0) ↔ w.getD 0 0 = 1 := by
  constructor
  · rintro ⟨_, v, hv, hd⟩
    exact (digits_unique _ hw ⟨hv.1, hv.2.1⟩ rfl hv.2.2 0).trans hd
  · intro hd
    refine ⟨?_, w, ⟨hw.1, hw.2, rfl⟩, hd⟩
    cases w with
    | nil => contradiction
    | cons d a =>
      change d = 1 at hd
      rw [hd, value_cons]
      change 0 < 1 * 1 + _
      omega

/-- At a word with value `n`, its tail value plus its low digit counts the
integers with a zero low digit in the interval `[0, n)`. -/
private theorem count_column [DecidablePred column] (n : ℕ) (w : List ℕ) (hw : Valid w)
    (hn : value w 0 = n) :
    Nat.count column n + value w.tail 0 + w.getD 0 0 = n := by
  induction n generalizing w with
  | zero =>
    have hz := digits_of_value_zero hw hn
    rw [Nat.count_zero, hz, value_of_zero_digits (fun i => (tail_digit w i).trans (hz _))]
  | succ n ih =>
    obtain ⟨v, hv, rfl, hvn⟩ := exists_prev hw hn
    have hcount := ih v hv hvn
    have hcol : column n ↔ v.getD 0 0 = 1 := hvn ▸ column_iff v hv
    rw [Nat.count_succ, if_congr hcol rfl rfl]
    cases v with
    | nil => simpa [inc] using hcount
    | cons d a =>
      obtain ⟨ha, hd, hf⟩ := (valid_cons d a).mp hv
      change Nat.count column n + value a 0 + d = n at hcount
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl <;> cases h : free a <;>
        simp [inc, h, value_inc_zero a ha] <;> omega

/-- Removing the low digit lowers each remaining weight by one Tribonacci index. -/
private theorem weight_difference (a : List ℕ) :
    value (1 :: a) 0 = value a 0 + (1 + ∑ i ∈ Finset.range (a.length + 1),
      (1 :: a).getD i 0 * (tribonacci i + tribonacci (i + 1))) := by
  rw [value_cons, Finset.sum_range_succ']
  change 1 * 1 + value a 1 = value a 0 + (1 + (_ + 1 * (0 + 0)))
  have weights : value a 1 = value a 0 + ∑ i ∈ Finset.range a.length,
      a.getD i 0 * (tribonacci (i + 1) + tribonacci (i + 2)) := by
    unfold value
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add]
    congr 1
    rw [tribonacci.eq_4 (i + 1)]
    ac_rfl
  rw [weights]
  simp only [List.getD_cons_succ, Nat.add_zero, Nat.mul_zero, Nat.one_mul, Nat.add_assoc]
  ac_rfl

end trithoff_row_number_eq

open trithoff_row_number_eq

/-- **Row numbers of the Trithoff array.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers, and let $U_i = T_i + T_{i+1}$,
so that $U_0, U_1, U_2, \dots = 0, 1, 2, 3, 6, 11, \dots$. Let $n$ have Tribonacci
representation $a1$, where $a$ is a digit word written most significant digit first, and let
$[a]_T$ be the Tribonacci value of $a$. Then $n$ is the $(n - [a]_T)$-th smallest positive
integer whose Tribonacci representation ends in $1$ (OEIS A003265, the first column of the
Trithoff array), and $n - [a]_T = 1 + [a1]_U$, where $[a1]_U$ is the sum of the digits of $a1$
weighted by $U_0, U_1, U_2, \dots$ starting from the least significant digit.

The paper writes $U_i = T_{2,i-2}$; its alternative formula $T_{i+1} - T_i$ is shifted, and the
displayed values $0, 1, 2, 3, 6, 11, \dots$ are used.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 7 (`jis-2025-25.5.4-lem-7`). -/
public theorem trithoff_row_number_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr (1 :: a) n) :
    Nat.nth (fun m => 0 < m ∧ ∃ w,
        IsTribonacciRepr w m ∧ w.getD 0 0 = 1) (n - tribonacciValue a - 1) = n ∧
      n - tribonacciValue a = 1 + ∑ i ∈ Finset.range (a.length + 1),
        (1 :: a).getD i 0 * (tribonacci i + tribonacci (i + 1)) := by
  classical
  have hw : Valid (1 :: a) := ⟨h.1, h.2.1⟩
  have hn : value (1 :: a) 0 = n := h.2.2
  have hcol : column n := hn ▸ (column_iff _ hw).2 rfl
  have hc := count_column n (1 :: a) hw hn
  change Nat.count column n + tribonacciValue a + 1 = n at hc
  constructor
  · change Nat.nth column _ = n
    rw [show n - tribonacciValue a - 1 = Nat.count column n by omega]
    exact Nat.nth_count hcol
  · have hd := weight_difference a
    change value (1 :: a) 0 = tribonacciValue a + _ at hd
    omega

end MetaMathlibExt
