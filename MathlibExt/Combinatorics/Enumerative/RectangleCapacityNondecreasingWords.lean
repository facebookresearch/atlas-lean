/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rectangles of size `r × s` in nondecreasing words

Statements from Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing
and Smirnov Words*, Journal of Integer Sequences 27 (2024), Article 24.8.4. A word `w_1 ⋯ w_n`
over `[k] = {1, …, k}` is drawn as a bargraph (column `i` has height `w_i`); an occurrence of an
`r × s` rectangle (height `r`, width `s`) is a placement of the rectangle inside the bargraph.
We prove the generating function and coefficient formula for the total rectangle count.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of $r \times s$ rectangles in a bargraph.** Let $w = w_0 w_1 \cdots w_{m-1}$ be a word
of natural numbers, drawn as a bargraph whose column $i$ has height $w_i$. The number of
occurrences of an $r \times s$ rectangle (height $r$, width $s$) in $w$ is the number of pairs
$(i, y)$ of natural numbers with $i < m$, $i + s \le m$ and $y \le w_0 + \cdots + w_{m-1}$ such
that $y + r \le w_{i+j}$ for every $j < s$.

Here $(i, y)$ is the rectangle whose lower left cell is in column $i$ and row $y$, both counted
from $0$. For $s \ge 1$ the conditions $i < m$ and $y \le w_0 + \cdots + w_{m-1}$ follow from the
others; for $s = 0$ the count is $m(w_0 + \cdots + w_{m-1} + 1)$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Introduction and Figure 2. -/
def rectangleCapacity (r s : ℕ) (w : List ℕ) : ℕ :=
  ((Finset.range w.length ×ˢ Finset.range (w.sum + 1)).filter fun p =>
    p.1 + s ≤ w.length ∧ ∀ j < s, p.2 + r ≤ w.getD (p.1 + j) 0).card

/-- **Example: $3 \times 2$ rectangles in the word $345134$.** The bargraph of the word $345134$
contains exactly four rectangles of height $3$ and width $2$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Figure 2. -/
theorem rectangleCapacity_example : rectangleCapacity 3 2 [3, 4, 5, 1, 3, 4] = 4 := by
  decide

/-- **Total number of $r \times s$ rectangles in nondecreasing words.** For natural numbers $k$,
$r$, $s$ and $n$, this is the sum, over all nondecreasing words $w_1 \le w_2 \le \cdots \le w_n$ of
length $n$ over the alphabet $[k] = \{1, \dots, k\}$ (the set $W^{\nearrow}_{n,k}$), of the number
of $r \times s$ rectangles in the bargraph of $w$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollaries 2 and 6. -/
def nondecreasingRectangleTotal (k r s n : ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (Fin n → Fin k)).filter (fun w => Monotone w),
    rectangleCapacity r s (List.ofFn fun i => (w i : ℕ) + 1)

/-- **Example: $1 \times 2$ rectangles in nondecreasing words of length $2$.** The nondecreasing
words of length $2$ over $[2] = \{1, 2\}$ are $11$, $12$ and $22$, which contain $1$, $1$ and $2$
rectangles of size $1 \times 2$ respectively, so the total number of $1 \times 2$ rectangles over
all nondecreasing words of length $2$ over $[2]$ is $4$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 2. -/
theorem nondecreasingRectangleTotal_two_one_two_two : nondecreasingRectangleTotal 2 1 2 2 = 4 := by
  decide

namespace nondecreasingRectangleTotal_r_by_s

open Finset PowerSeries

private abbrev Word (k n : ℕ) := {w : Fin n → Fin k // Monotone w}

-- Split a nonempty word according to whether its first letter is the smallest letter.
private def prependZero {k n : ℕ} (w : Word (k + 1) n) : Word (k + 1) (n + 1) :=
  ⟨Fin.cons 0 w.val, by
    intro i j hij
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using w.property (Fin.succ_le_succ_iff.mp hij)⟩

private def raiseWord {k n : ℕ} (w : Word k n) : Word (k + 1) n :=
  ⟨fun i => (w.val i).succ, fun _ _ h => Fin.succ_le_succ_iff.mpr (w.property h)⟩

private noncomputable def splitWord (k n : ℕ) :
    Word (k + 1) n ⊕ Word k (n + 1) ≃ Word (k + 1) (n + 1) :=
  Equiv.ofBijective (Sum.elim prependZero raiseWord) <| by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          congr 1
          exact Subtype.ext (funext fun i => by
            simpa [prependZero] using congrArg (fun w => w.val i.succ) h)
        | inr y =>
          have := congrArg (fun w => w.val 0) h
          exact (Fin.succ_ne_zero (y.val 0) (by
            simpa [prependZero, raiseWord] using this.symm)).elim
      | inr x =>
        cases y with
        | inl y =>
          have := congrArg (fun w => w.val 0) h
          simp [prependZero, raiseWord] at this
        | inr y =>
          congr 1
          exact Subtype.ext (funext fun i => by
            simpa [raiseWord] using congrArg (fun w => w.val i) h)
    · intro w
      by_cases h : w.val 0 = 0
      · refine ⟨Sum.inl ⟨fun i => w.val i.succ, fun _ _ hij =>
          w.property (Fin.succ_le_succ_iff.mpr hij)⟩, Subtype.ext (funext ?_)⟩
        intro i
        cases i using Fin.cases <;> simp [prependZero, h]
      · have hp (i) : 0 < (w.val i).val := by
          have hle := w.property (Fin.zero_le i)
          have h0 : 0 < (w.val 0).val := Nat.pos_of_ne_zero (fun e => h (Fin.ext e))
          exact lt_of_lt_of_le h0 hle
        let v (i) : Fin k := ⟨(w.val i).val - 1, by have := hp i; have := (w.val i).isLt; omega⟩
        refine ⟨Sum.inr ⟨v, fun _ _ hij => Nat.sub_le_sub_right (w.property hij) 1⟩,
          Subtype.ext (funext fun i => Fin.ext ?_)⟩
        change (w.val i).val - 1 + 1 = _
        have := hp i
        omega

private theorem word_card (k n : ℕ) : Fintype.card (Word k n) = k.multichoose n := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [Word, Monotone]
    | succ n =>
      let : IsEmpty (Word 0 (n + 1)) := ⟨fun w => (w.val 0).elim0⟩
      simp
  | succ k ih =>
    induction n with
    | zero => simp [Word, Monotone]
    | succ n ihn =>
      rw [← Fintype.card_congr (splitWord k n), Fintype.card_sum, ih, ihn,
        Nat.multichoose_succ_succ, add_comm]

-- Weight a window by its first letter, indexed by its distance from the largest letter.
private def windows {k n : ℕ} (f : ℕ → ℕ) (q : ℕ) (w : Word k n) : ℕ :=
  ∑ i : Fin n, if i.val + q < n then f (k - 1 - (w.val i).val) else 0

private def total (f : ℕ → ℕ) (q k n : ℕ) : ℕ :=
  ∑ w : Word k n, windows f q w

private theorem total_succ (f : ℕ → ℕ) (q k n : ℕ) :
    total f q (k + 1) (n + 1) = total f q (k + 1) n + total f q k (n + 1) +
      (if q ≤ n then f k * (k + 1).multichoose n else 0) := by
  unfold total
  rw [← Equiv.sum_comp (splitWord k n), Fintype.sum_sum_type]
  change (∑ w : Word (k + 1) n, windows f q (prependZero w)) +
    (∑ w : Word k (n + 1), windows f q (raiseWord w)) = _
  have h₁ (w : Word (k + 1) n) : windows f q (prependZero w) =
      (if q ≤ n then f k else 0) + windows f q w := by
    simp [windows, prependZero, Fin.sum_univ_succ, Nat.succ_add]
  have h₂ (w : Word k (n + 1)) : windows f q (raiseWord w) = windows f q w := by
    unfold windows
    apply sum_congr rfl
    intro i _
    change (if _ then f (k + 1 - 1 - ((w.val i).val + 1)) else 0) = _
    rw [show k + 1 - 1 - ((w.val i).val + 1) = k - 1 - (w.val i).val by omega]
  simp_rw [h₁, h₂, sum_add_distrib]
  split_ifs <;> simp_all [word_card, add_comm, add_assoc, mul_comm]

private theorem capacity_eq_windows {k n : ℕ} (r q : ℕ) (w : Word k n) :
    rectangleCapacity r (q + 1) (List.ofFn fun i => (w.val i).val + 1) =
      windows (fun d => k + 1 - r - d) q w := by
  let l := List.ofFn fun i => (w.val i).val + 1
  have hl : l.length = n := List.length_ofFn
  have hget (i : ℕ) (hi : i < n) : l.getD i 0 = (w.val ⟨i, hi⟩).val + 1 := by
    rw [List.getD_eq_getElem l 0 (hl ▸ hi)]
    simp [l]
  change rectangleCapacity r (q + 1) l = _
  rw [rectangleCapacity, hl, card_filter, sum_product, ← Fin.sum_univ_eq_sum_range]
  unfold windows
  apply sum_congr rfl
  intro i _
  by_cases hfit : i.val + q < n
  · rw [ite_eq_left hfit, ← card_filter]
    have heq : ((range (l.sum + 1)).filter fun y =>
        i.val + (q + 1) ≤ n ∧ ∀ j < q + 1, y + r ≤ l.getD (i.val + j) 0) =
        range ((w.val i).val + 2 - r) := by
      ext y
      simp only [mem_filter, mem_range]
      have hsum : (w.val i).val + 1 ≤ l.sum :=
        List.le_sum_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
      constructor
      · rintro ⟨_, _, h⟩
        have hz := h 0 (Nat.zero_lt_succ _)
        rw [Nat.add_zero, hget _ i.isLt] at hz
        change y + r ≤ (w.val i).val + 1 at hz
        omega
      · intro hy
        refine ⟨by omega, by omega, fun j hj => ?_⟩
        rw [hget _ (by omega)]
        have hle : (w.val i).val ≤ (w.val ⟨i.val + j, by omega⟩).val :=
          w.property (Nat.le_add_right _ _)
        omega
    rw [heq, card_range]
    dsimp only
    have := (w.val i).isLt
    omega
  · simp [hfit, show ¬i.val + (q + 1) ≤ n by omega]

private theorem rectangleTotal_eq (k r q n : ℕ) :
    nondecreasingRectangleTotal k r (q + 1) n = total (fun d => k + 1 - r - d) q k n := by
  unfold nondecreasingRectangleTotal total
  rw [← sum_subtype_eq_sum_filter]
  simpa only [subtype_univ] using
    (sum_congr rfl fun (w : Word k n) _ => capacity_eq_windows r q w)

private abbrev Series := PowerSeries ℤ

private noncomputable def series (f : ℕ → ℕ) (q k : ℕ) : Series :=
  mk fun n => (total f q k n : ℤ)

private noncomputable def tailSeries (q k : ℕ) : Series :=
  mk fun n => ((q + n + k).choose k : ℤ)

private theorem total_empty (f : ℕ → ℕ) (q k : ℕ) : total f q k 0 = 0 := by
  simp [total, windows]

private theorem series_succ (f : ℕ → ℕ) (q k : ℕ) :
    series f q (k + 1) * (1 - X) = series f q k +
      X ^ (q + 1) * (C (f k : ℤ) * tailSeries q k) := by
  ext n
  rw [mul_sub, mul_one, map_sub, map_add, coeff_X_pow_mul', ← pow_one (X : Series),
    coeff_mul_X_pow']
  cases n with
  | zero => simp [series, total_empty]
  | succ n =>
    simp only [Nat.succ_sub_one, Nat.le_add_left, ite_true, series, coeff_mk, total_succ]
    by_cases h : q ≤ n
    · have hc : (k + n).choose n = (n + k).choose k := by
        rw [Nat.add_comm k n, Nat.choose_symm_add]
      simp [h, tailSeries, Nat.multichoose_eq, hc]
      ring
    · simp [h]

private theorem series_zero (f : ℕ → ℕ) (q : ℕ) : series f q 0 = 0 := by
  ext n
  cases n with
  | zero => simp [series, total_empty]
  | succ n =>
    let : IsEmpty (Word 0 (n + 1)) := ⟨fun w => (w.val 0).elim0⟩
    simp [series, total]

-- Clearing the denominator expresses the answer as a weighted sum of binomial tails.
private theorem series_normalized (f : ℕ → ℕ) (q k : ℕ) :
    series f q k * (1 - X) ^ (k + 1) =
      X ^ (q + 1) * ∑ d ∈ range k, C (f d : ℤ) * (tailSeries q d * (1 - X) ^ (d + 1)) := by
  induction k with
  | zero => simp [series_zero]
  | succ k ih =>
    rw [pow_succ' _ (k + 1), ← mul_assoc, series_succ, add_mul, ih, sum_range_succ]
    ring

private theorem tail_succ (q k : ℕ) :
    tailSeries q (k + 1) * (1 - X) = tailSeries q k + C (((q + k).choose (k + 1) : ℕ) : ℤ) := by
  ext n
  rw [mul_sub, mul_one, map_sub, map_add, ← pow_one (X : Series), coeff_mul_X_pow']
  cases n with
  | zero =>
    simp [tailSeries, Nat.choose_succ_succ', ← Nat.add_assoc]
  | succ n =>
    have e : q + (n + 1) + (k + 1) = (q + (n + 1) + k) + 1 := by omega
    rw [coeff_C]
    simp [tailSeries, e, Nat.choose_succ_succ', show q + n + (k + 1) = q + (n + 1) + k by omega]

private theorem coeff_denominator (k i : ℕ) :
    coeff i ((1 - X : Series) ^ k) = (-1 : ℤ) ^ i * k.choose i := by
  induction k generalizing i with
  | zero => cases i <;> simp
  | succ k ih =>
    rw [pow_succ, mul_sub, mul_one, map_sub, ← pow_one (X : Series), coeff_mul_X_pow']
    cases i with
    | zero => simp [ih]
    | succ i => simp [ih, Nat.choose_succ_succ', pow_succ]; ring

-- Pascal’s identity gives the coefficients of each tail after clearing its denominator.
private theorem coeff_tail (q k i : ℕ) :
    coeff i (tailSeries q k * (1 - X) ^ (k + 1)) =
      (-1 : ℤ) ^ i * q.multichoose i * (q + k).choose (q + i) := by
  cases q with
  | zero =>
    have e : tailSeries 0 k = mk (fun n => ((k + n).choose k : ℤ)) := by
      ext n
      simp [tailSeries, Nat.add_comm]
    rw [e, mk_add_choose_mul_one_sub_pow_eq_one]
    cases i <;> simp
  | succ q =>
    induction k with
    | zero =>
      have e : tailSeries (q + 1) 0 = (mk 1 : Series) := by
        ext n
        simp [tailSeries]
      rw [e, pow_one, mk_one_mul_one_sub_eq_one]
      cases i with
      | zero => simp
      | succ i => simp [Nat.choose_eq_zero_of_lt (show q + 1 < q + 1 + (i + 1) by omega)]
    | succ k ih =>
      rw [pow_succ' _ (k + 1), ← mul_assoc, tail_succ, add_mul, map_add, ih,
        coeff_C_mul, coeff_denominator]
      have hprod : (q + 1 + k).choose (k + 1) * (k + 1).choose i =
          (q + 1).multichoose i * (q + 1 + k).choose (q + i) := by
        have h := Nat.choose_mul (n := q + 1 + k) (k := q + i) (s := q) (by omega)
        rw [show q + 1 + k - q = k + 1 by omega, Nat.add_sub_cancel_left] at h
        rw [Nat.choose_symm_of_eq_add (show q + 1 + k = q + (k + 1) by omega),
          Nat.choose_symm_add] at h
        simpa [Nat.multichoose_eq, mul_comm] using h.symm
      rw [show q + 1 + (k + 1) = (q + 1 + k) + 1 by omega,
        show q + 1 + i = (q + i) + 1 by omega, Nat.choose_succ_succ']
      push_cast
      have hz : (((q + 1 + k).choose (k + 1) : ℕ) : ℤ) * ((k + 1).choose i : ℤ) =
          ((q + 1).multichoose i : ℤ) * ((q + 1 + k).choose (q + i) : ℤ) := by
        exact_mod_cast hprod
      linear_combination (-1 : ℤ) ^ i * hz

private theorem sum_choose (q i m : ℕ) :
    ∑ d ∈ range m, (q + d).choose (q + i) = (q + m).choose (q + i + 1) := by
  induction m with
  | zero => simp [Nat.choose_eq_zero_of_lt (show q < q + i + 1 by omega)]
  | succ m ih =>
    rw [sum_range_succ, ih, ← Nat.add_assoc, Nat.choose_succ_succ', add_comm]

-- Summing the hockey-stick identity twice accounts for the possible vertical placements.
private theorem sum_weighted_choose (q i m : ℕ) :
    ∑ d ∈ range m, (m - d) * (q + d).choose (q + i) = (q + m + 1).choose (q + i + 2) := by
  induction m with
  | zero => simp [Nat.choose_eq_zero_of_lt (show q + 1 < q + i + 2 by omega)]
  | succ m ih =>
    have step (d) (hd : d ∈ range (m + 1)) :
        (m + 1 - d) * (q + d).choose (q + i) =
          (m - d) * (q + d).choose (q + i) + (q + d).choose (q + i) := by
      rw [show m + 1 - d = (m - d) + 1 by have := mem_range.mp hd; omega, add_one_mul]
    rw [sum_congr rfl step, sum_add_distrib, sum_choose, sum_range_succ, ih]
    simp only [Nat.sub_self, zero_mul, add_zero, ← Nat.add_assoc]
    rw [Nat.choose_succ_succ' (q + m + 1) (q + i + 1), add_comm]

private def numeratorCoeff (m q i : ℕ) : ℤ :=
  (-1 : ℤ) ^ i * (q.multichoose i * (m + (q + 1)).choose (q + 1 + i + 1) : ℕ)

private theorem numerator (q k r : ℕ) (hr : 1 ≤ r) :
    let m := k + 1 - r
    ∑ d ∈ range k, C ((m - d : ℕ) : ℤ) * (tailSeries q d * (1 - X) ^ (d + 1)) =
      ∑ i ∈ range (m + 1), C (numeratorCoeff m q i) * X ^ i := by
  dsimp only
  let m := k + 1 - r
  have hm : m ≤ k := by dsimp [m]; omega
  ext i
  simp only [map_sum, coeff_C_mul, coeff_tail]
  have hsum : ∑ d ∈ range k, (m - d) * (q + d).choose (q + i) =
      (q + m + 1).choose (q + i + 2) := by
    rw [← sum_weighted_choose]
    symm
    apply sum_subset (range_mono hm)
    intro d _ hd
    simp only [mem_range, not_lt] at hd
    simp [Nat.sub_eq_zero_of_le hd]
  have hc : ∑ d ∈ range k, ((m - d : ℕ) : ℤ) *
      ((-1 : ℤ) ^ i * (q.multichoose i : ℤ) * ((q + d).choose (q + i) : ℤ)) =
      numeratorCoeff m q i := by
    have hz := congrArg (Nat.cast : ℕ → ℤ) hsum
    push_cast at hz
    unfold numeratorCoeff
    push_cast
    rw [show m + (q + 1) = q + m + 1 by omega, show q + 1 + i + 1 = q + i + 2 by omega,
      ← hz, ← mul_assoc, mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  rw [hc]
  change numeratorCoeff m q i = ∑ j ∈ range (m + 1), _
  by_cases hi : i < m + 1
  · simp [hi, m]
  · have hzero : m + (q + 1) < q + 1 + i + 1 := by omega
    simp [hi, numeratorCoeff, Nat.choose_eq_zero_of_lt hzero]

private theorem extract_coeff (F : Series) (a : ℕ → ℤ) (m k s n : ℕ) (hn : s ≤ n)
    (h : F * (1 - X) ^ (k + 1) = X ^ s * ∑ i ∈ range (m + 1), C (a i) * X ^ i) :
    coeff n F = ∑ i ∈ range (min m (n - s) + 1), a i * ((n - s - i + k).choose k : ℤ) := by
  let B : Series := mk fun j => ((k + j).choose k : ℤ)
  have hB : (1 - X) ^ (k + 1) * B = 1 := by
    rw [mul_comm]
    exact mk_add_choose_mul_one_sub_pow_eq_one ℤ k
  have hF : F = X ^ s * ((∑ i ∈ range (m + 1), C (a i) * X ^ i) * B) := by
    rw [← mul_assoc, ← h, mul_assoc, hB, mul_one]
  rw [hF, coeff_X_pow_mul', ite_eq_left hn, sum_mul, map_sum]
  symm
  apply sum_subset_zero_on_sdiff (range_mono (Nat.succ_le_succ (min_le_left _ _)))
  · intro i hi
    simp only [mem_sdiff, mem_range] at hi
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  · intro i hi
    have hle : i ≤ n - s := by have := mem_range.mp hi; omega
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hle]
    simp [B, Nat.add_comm]

end nondecreasingRectangleTotal_r_by_s

open nondecreasingRectangleTotal_r_by_s in
set_option linter.unusedVariables false in
/-- **Generating function for $r \times s$ rectangles in nondecreasing words.** Let $k \ge 1$,
$r \ge 1$ and $s \ge 1$, let $g_k(n)$ be the total number of $r \times s$ rectangles over all
nondecreasing words of length $n$ over $[k] = \{1, \dots, k\}$, and let $m = \max(k + 1 - r, 0)$.
Then, as formal power series over $\mathbb{Z}$,
$$
\Big(\sum_{n \ge 0} g_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{0 \le i \le k+1-r} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1} x^i,
$$
where the sum is empty when $r \ge k + 2$, and for every $n \ge s$,
$$
g_k(n) = \sum_{i=0}^{\min(m,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 6 (`jis-2024-24.8.4-cor-6`). -/
theorem nondecreasingRectangleTotal_r_by_s (k r s : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hs : 1 ≤ s) :
    PowerSeries.mk (fun n => (nondecreasingRectangleTotal k r s n : ℤ)) *
        (1 - PowerSeries.X) ^ (k + 1) =
      PowerSeries.X ^ s * ∑ i ∈ Finset.range (k + 2 - r),
        PowerSeries.C ((-1 : ℤ) ^ i *
          ((i + s - 2).choose i * (k + 1 - r + s).choose (s + i + 1) : ℕ)) * PowerSeries.X ^ i ∧
    ∀ n, s ≤ n → (nondecreasingRectangleTotal k r s n : ℤ) =
      ∑ i ∈ Finset.range (min (k + 1 - r) (n - s) + 1),
        (-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + 1 - r + s).choose (s + i + 1) *
          (n - s - i + k).choose k : ℕ) := by
  cases s with
  | zero => omega
  | succ q =>
    let m := k + 1 - r
    have h := series_normalized (fun d => m - d) q k
    rw [numerator q k r hr] at h
    have hF : PowerSeries.mk (fun n => (nondecreasingRectangleTotal k r (q + 1) n : ℤ)) *
        (1 - PowerSeries.X) ^ (k + 1) =
        PowerSeries.X ^ (q + 1) * ∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (numeratorCoeff m q i) * PowerSeries.X ^ i := by
      simpa only [series, rectangleTotal_eq] using h
    have ha (i : ℕ) : numeratorCoeff m q i = (-1 : ℤ) ^ i *
        ((i + (q + 1) - 2).choose i * (m + (q + 1)).choose (q + 1 + i + 1) : ℕ) := by
      rw [numeratorCoeff, Nat.multichoose_eq, show q + i - 1 = i + (q + 1) - 2 by omega]
    constructor
    · rw [hF]
      by_cases hrk : r ≤ k + 1
      · rw [show k + 2 - r = m + 1 by dsimp [m]; omega]
        simp only [ha, m]
      · have hm : m = 0 := by dsimp [m]; omega
        simp [show k + 2 - r = 0 by omega, hm, numeratorCoeff]
    · intro n hn
      have hc := extract_coeff _ _ m k (q + 1) n hn hF
      rw [PowerSeries.coeff_mk] at hc
      rw [hc]
      apply Finset.sum_congr rfl
      intro i _
      rw [ha]
      push_cast
      ring

/-- **Generating function for $1 \times s$ rectangles in nondecreasing words.** Let $k \ge 1$ and
$s \ge 1$, and let $f_k(n)$ be the total number of $1 \times s$ rectangles over all nondecreasing
words of length $n$ over $[k] = \{1, \dots, k\}$. Then, as formal power series over $\mathbb{Z}$,
$$
\Big(\sum_{n \ge 0} f_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{i=0}^{k-1} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1} x^i,
$$
and for every $n \ge s$,
$$
f_k(n) = \sum_{i=0}^{\min(k-1,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

Source: Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and
Smirnov Words*, Journal of Integer Sequences 27 (2024),
Article 24.8.4, Corollary 2 (`jis-2024-24.8.4-cor-2`). -/
theorem nondecreasingRectangleTotal_one_by_s (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    PowerSeries.mk (fun n => (nondecreasingRectangleTotal k 1 s n : ℤ)) *
        (1 - PowerSeries.X) ^ (k + 1) =
      PowerSeries.X ^ s * ∑ i ∈ Finset.range k,
        PowerSeries.C ((-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + s).choose (s + i + 1) : ℕ)) *
          PowerSeries.X ^ i ∧
    ∀ n, s ≤ n → (nondecreasingRectangleTotal k 1 s n : ℤ) =
      ∑ i ∈ Finset.range (min (k - 1) (n - s) + 1),
        (-1 : ℤ) ^ i * ((i + s - 2).choose i * (k + s).choose (s + i + 1) *
          (n - s - i + k).choose k : ℕ) := by
  obtain ⟨hseries, hcoeff⟩ := nondecreasingRectangleTotal_r_by_s k 1 s hk le_rfl hs
  have hzero : (k + s).choose (s + k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [Nat.add_sub_cancel] at hseries hcoeff
  constructor
  · simpa [Finset.sum_range_succ, hzero] using hseries
  · intro n hn
    by_cases h : n - s < k
    · simpa only [min_eq_right (show n - s ≤ k by omega),
        min_eq_right (show n - s ≤ k - 1 by omega)] using hcoeff n hn
    · rw [min_eq_left (by omega : k - 1 ≤ n - s), Nat.sub_add_cancel hk]
      simpa [min_eq_left (by omega : k ≤ n - s), Finset.sum_range_succ, hzero] using hcoeff n hn

end

end MetaMathlibExt
