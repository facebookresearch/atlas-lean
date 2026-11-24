/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic
-- Provides `Nat.instLattice`, through which the suprema in `wordCapacity` have always elaborated.
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Combinatorics.Enumerative.CatalanGrowthAreaDist

/-!
# Capacity of Catalan words

The capacity of a word of natural numbers, viewed as a bargraph, is the number of cells of water
it holds. This file defines capacity, Catalan words, and the capacity distribution of the Catalan
words with a given last letter, following Mansour and Shattuck.

The two Fibonacci identities express even Fibonacci numbers and binomial sums of odd Fibonacci
numbers as double sums of binomially weighted odd Fibonacci numbers. The second one gives
`catalanCapacityDist_eval_zero`, the number of Catalan words of capacity zero with a given last
letter $i \ge 2$. For restricted smooth words ending in $i \ge 3$,
`restrictedSmoothCapacityDist_eval_zero` expresses the count as a tail of a binomial row.
For smooth words ending in $i \ge 2$, `smoothCapacityDist_eval_zero` gives the corresponding tail
of row $n-2$.
-/

namespace MetaMathlibExt

open Finset

namespace fib_two_mul_eq_sum_sum_choose_mul_fib_odd

private theorem sum_pow_mul_fib (k : ℕ) :
    ∑ m ∈ range (k + 1), 2 ^ (k - m) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      Nat.fib (2 * k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    -- Every old term doubles, and the new term contributes the next odd Fibonacci number.
    have hpow (m : ℕ) (hm : m ∈ range (k + 1)) :
        2 ^ (k + 1 - m) = 2 * 2 ^ (k - m) := by
      rw [mem_range] at hm
      rw [show k + 1 - m = k - m + 1 by omega, pow_succ']
    rw [sum_congr rfl (fun m hm =>
      congrArg (· * (if m = 0 then 1 else Nat.fib (2 * m - 1))) (hpow m hm))]
    simp_rw [mul_assoc]
    rw [← mul_sum, ih]
    simp only [Nat.sub_self, pow_zero, one_mul, Nat.succ_ne_zero, ite_false]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega,
      Nat.fib_add_two (n := 2 * k + 2), Nat.fib_add_two (n := 2 * k + 1),
      show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    omega

end fib_two_mul_eq_sum_sum_choose_mul_fib_odd

/-- **A double-sum identity for even-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{k+2} = F_{k+1} + F_k$, and set $F_{-1} = 1$. For every
natural number $n \ge 1$,
$$F_{2n} = \sum_{j=1}^{n} \sum_{m=0}^{n-j} \binom{n-m-1}{j-1} F_{2m-1}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem fib_two_mul_eq_sum_sum_choose_mul_fib_odd (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.range (n - j + 1),
        (n - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- Fixing m first leaves the complete binomial row with upper index k - m.
  rw [sum_comm' (t' := range (k + 1)) (s' := fun m => Ico 1 (k - m + 2)) (fun j m => by
    simp only [mem_Icc, mem_range, mem_Ico]
    omega)]
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    ← fib_two_mul_eq_sum_sum_choose_mul_fib_odd.sum_pow_mul_fib]
  apply sum_congr rfl
  intro m hm
  rw [← sum_mul, sum_Ico_eq_sum_range]
  simp only [mem_range] at hm
  rw [show k + 1 - m - 1 = k - m by omega]
  simp [Nat.sum_range_choose]

namespace sum_choose_mul_fib_odd_eq_choose_add_sum

private theorem fib_odd_split (m : ℕ) :
    Nat.fib (2 * m + 1) = (if m = 0 then 1 else Nat.fib (2 * m - 1)) +
      ∑ r ∈ range m, Nat.fib (2 * r + 1) := by
  have h (k : ℕ) : ∑ r ∈ range k, Nat.fib (2 * r + 1) = Nat.fib (2 * k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 2 by omega, Nat.fib_add_two]
  rw [h]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ite_false]
    rw [show 2 * (m + 1) + 1 = (2 * (m + 1) - 1) + 2 by omega,
      Nat.fib_add_two, show 2 * (m + 1) - 1 + 1 = 2 * (m + 1) by omega]

private theorem sum_rows (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    (∑ m ∈ range (n + 1 - i), (n - m - 2).choose (i - 2) * Nat.fib (2 * m + 1)) =
      ∑ j ∈ Icc i n, ∑ m ∈ range (n - j + 1),
        (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  induction hd : n + 1 - i generalizing i with
  | zero =>
    simp [Icc_eq_empty_of_lt (show n < i by omega)]
  | succ d ih =>
    have hi' : i ≤ n := by omega
    rw [← insert_Icc_succ_left_eq_Icc hi', sum_insert (by simp), Nat.succ_eq_succ,
      ← ih (i + 1) (by omega) (by omega) (by omega)]
    have : d = n - i := by omega
    subst d
    -- Splitting each Fibonacci weight gives the row at i and a triangular sum.
    conv_lhs => enter [2, m, 2]; rw [fib_odd_split m]
    simp_rw [mul_add, sum_add_distrib, mul_sum]
    congr 1
    -- Reverse the triangular sum and sum each column by the hockey-stick identity.
    rw [sum_comm' (t' := range (n - i)) (s' := fun r => Ico (r + 1) (n - i + 1))
      (fun m r => by simp only [mem_range, mem_Ico]; omega)]
    refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.mp hr
    rw [← sum_mul]
    congr 1
    simp_rw [show ∀ m, n - m - 2 = n - 2 - m by omega]
    rw [sum_Ico_reflect (fun t => t.choose (i - 2)) _ (by omega),
      show n - 2 + 1 - (n - i + 1) = i - 2 by omega,
      show n - 2 + 1 - (r + 1) = (n - 2 - r - 1) + 1 by omega,
      Ico_add_one_right_eq_Icc, Nat.sum_Icc_choose,
      show n - 2 - r - 1 + 1 = n - 2 - r by omega,
      show i + 1 - 2 = i - 2 + 1 by omega]

end sum_choose_mul_fib_odd_eq_choose_add_sum

set_option linter.unusedVariables false in
/-- **A recursion for binomial sums of odd-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with the convention $F_{-1} = 1$. For all integers $n \ge 1$ and $2 \le i \le n + 1$,
$$\sum_{m=0}^{n-i+1} \binom{n-m-1}{i-2} F_{2m-1} =
\binom{n-1}{i-2} + \sum_{j=i}^{n} \sum_{m=0}^{n-j} \binom{n-m-2}{j-2} F_{2m-1}$$
(Mansour and Shattuck's Lemma 5, identity (21)). All differences in the binomial coefficients and
in the summation bounds are nonnegative.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem sum_choose_mul_fib_odd_eq_choose_add_sum (n i : ℕ) (hn : 1 ≤ n)
    (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    ∑ m ∈ Finset.range (n + 2 - i),
        (n - m - 1).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      (n - 1).choose (i - 2) +
        ∑ j ∈ Finset.Icc i n, ∑ m ∈ Finset.range (n - j + 1),
          (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) := by
  rw [show n + 2 - i = (n + 1 - i) + 1 by omega, sum_range_succ']
  simp only [Nat.sub_zero, ite_true, mul_one, Nat.succ_ne_zero, ite_false]
  rw [add_comm, ← sum_choose_mul_fib_odd_eq_choose_add_sum.sum_rows n i hi hin]
  congr 1

section CatalanCapacity

open Polynomial

@[expose] public section

/-- **Capacity of a word.** The capacity of a word $w = w_1 \cdots w_n$ of natural numbers,
viewed as a bargraph, is
$$\mathrm{cap}(w) = \sum_{i=1}^{n}
\max\Bigl(0, \min\bigl(\max_{j < i} w_j, \max_{j > i} w_j\bigr) - w_i\Bigr),$$
the number of cells of water held above the columns, where an empty maximum is $0$. In particular
the first and last columns hold no water.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of capacity. -/
public def wordCapacity {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n,
    (min ((Finset.univ.filter (· < i)).sup w) ((Finset.univ.filter (i < ·)).sup w) - w i)

/-- **Catalan words.** For a natural number $n$, the set $\mathcal{A}_n$ of Catalan words of length
$n$ consists of the words $w = w_1 w_2 \cdots w_n$ of positive integers with $w_1 = 1$ and
$w_{i+1} \le w_i + 1$ for $1 \le i < n$; for $n = 0$ it contains only the empty word.

Every letter of a Catalan word of length $n$ is at most $n$, so $\mathcal{A}_n$ is finite.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of Catalan words. -/
public def catalanWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧ ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1

/-- **Characterization of Catalan words.** For a natural number $n$, let $\mathcal{A}_n$ be the
set of Catalan words of length $n$, defined as the words $w = w_1 \cdots w_n$ with letters in
$\{1, \dots, n\}$ such that $w_1 = 1$ when $n \ge 1$ and $w_{k+1} \le w_k + 1$ for $1 \le k < n$.
A word $w = w_1 \cdots w_n$ of natural numbers belongs to $\mathcal{A}_n$ if and only if
$w_k \ge 1$ for every $k$, $w_1 = 1$ when $n \ge 1$, and $w_{k+1} \le w_k + 1$ for $1 \le k < n$.
In particular, the bound $w_k \le n$ on the letters is automatic.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of Catalan words. -/
public theorem mem_catalanWords_iff {n : ℕ} (w : Fin n → ℕ) :
    w ∈ catalanWords n ↔ (∀ i, 1 ≤ w i) ∧ (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 := by
  simp only [catalanWords, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, h0, hg⟩
    exact ⟨fun i => (hb i).1, h0, hg⟩
  · rintro ⟨h1, h0, hg⟩
    have key : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k + 1 := by
      intro k
      induction k with
      | zero => intro hk; rw [h0 ⟨0, hk⟩ rfl]
      | succ k ih =>
        intro hk
        have h₁ := hg ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
        have h₂ := ih (by omega)
        omega
    refine ⟨fun i => ⟨h1 i, ?_⟩, h0, hg⟩
    have := key i.val i.isLt
    rw [Fin.eta] at this
    omega

/-- **Capacity distribution.** For a finite set $S$ of words of length $n$ with letters in the
natural numbers, the capacity distribution of $S$ is the polynomial
$\sum_{w \in S} q^{\operatorname{cap}(w)}$ in $\mathbb{Z}[q]$, where $\operatorname{cap}(w)$ is the
capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def capacityDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordCapacity w

/-- **Capacity distribution of Catalan words with a given last letter.** For natural numbers $n$
and $i$, $a(n, i; q) \in \mathbb{Z}[q]$ is the capacity distribution of the Catalan words of
length $n$ whose last letter is $i$: the sum of $q^{\mathrm{cap}(w)}$ over all such words $w$,
where $\mathrm{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def catalanCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (catalanWords n) i)

namespace catalanCapacityDist_eval_zero

/-! A word has capacity zero exactly when no letter lies strictly below letters on both of its
sides. Appending a letter at most the current last letter keeps the capacity-zero words, and
appending a larger letter leaves only the weakly increasing words. -/

private theorem wordCapacity_eq_zero_iff {n : ℕ} (w : Fin n → ℕ) :
    wordCapacity w = 0 ↔ ∀ k, (∀ j, j < k → w j ≤ w k) ∨ (∀ j, k < j → w j ≤ w k) := by
  simp only [wordCapacity, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    Nat.sub_eq_zero_iff_le, min_le_iff, Finset.sup_le_iff, Finset.mem_filter, true_and]

private theorem wordCapacity_snoc_eq_zero_iff {n : ℕ} (w : Fin n → ℕ) (a : ℕ) :
    wordCapacity (Fin.snoc (α := fun _ => ℕ) w a) = 0 ↔
      ∀ k, (∀ j, j < k → w j ≤ w k) ∨ ((∀ j, k < j → w j ≤ w k) ∧ a ≤ w k) := by
  have h (i : Fin n) : ¬Fin.last n < i.castSucc := not_lt.mpr (Fin.castSucc_lt_last i).le
  rw [wordCapacity_eq_zero_iff, Fin.forall_fin_succ']
  simp [Fin.forall_fin_succ', Fin.castSucc_lt_last, h]

private theorem wordCapacity_snoc_eq_zero_iff_of_le {n : ℕ} (w : Fin (n + 1) → ℕ) {a : ℕ}
    (ha : a ≤ w (Fin.last n)) :
    wordCapacity (Fin.snoc (α := fun _ => ℕ) w a) = 0 ↔ wordCapacity w = 0 := by
  rw [wordCapacity_snoc_eq_zero_iff, wordCapacity_eq_zero_iff]
  refine forall_congr' fun k => or_congr_right ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rcases (Fin.le_last k).lt_or_eq with hk | rfl
  · exact ha.trans (h _ hk)
  · exact ha

private theorem le_last_of_mono {n : ℕ} {w : Fin (n + 1) → ℕ}
    (hw : ∀ k j, j < k → w j ≤ w k) (j : Fin (n + 1)) : w j ≤ w (Fin.last n) := by
  rcases (Fin.le_last j).lt_or_eq with hj | rfl
  · exact hw _ _ hj
  · exact le_rfl

private theorem wordCapacity_snoc_eq_zero_iff_of_lt {n : ℕ} (w : Fin (n + 1) → ℕ) {a : ℕ}
    (ha : w (Fin.last n) < a) :
    wordCapacity (Fin.snoc (α := fun _ => ℕ) w a) = 0 ↔ ∀ k j, j < k → w j ≤ w k := by
  rw [wordCapacity_snoc_eq_zero_iff]
  refine ⟨fun h => ?_, fun h k => Or.inl (h k)⟩
  -- The last letter is preceded only by smaller letters, as the appended letter exceeds it.
  have hlast : ∀ j, w j ≤ w (Fin.last n) := by
    rcases h (Fin.last n) with h' | h'
    · intro j
      rcases (Fin.le_last j).lt_or_eq with hj | rfl
      · exact h' j hj
      · exact le_rfl
    · exact absurd h'.2 (not_le.mpr ha)
  intro k
  rcases h k with h' | h'
  · exact h'
  · exact absurd (h'.2.trans (hlast k)) (not_le.mpr ha)

private theorem mono_snoc_iff {n : ℕ} (w : Fin n → ℕ) (a : ℕ) :
    (∀ k j, j < k → Fin.snoc (α := fun _ => ℕ) w a j ≤ Fin.snoc (α := fun _ => ℕ) w a k) ↔
      (∀ k j, j < k → w j ≤ w k) ∧ ∀ j, w j ≤ a := by
  have h (i : Fin n) : ¬Fin.last n < i.castSucc := not_lt.mpr (Fin.castSucc_lt_last i).le
  simp [Fin.forall_fin_succ', Fin.castSucc_lt_last, h]

/-! Catalan words of length $n + 2$ ending in $a \ge 1$ are the Catalan words of length $n + 1$
whose last letter is at least $a - 1$, followed by $a$. -/

private theorem mem_catalanWords_succ_iff {m : ℕ} (w : Fin (m + 1) → ℕ) :
    w ∈ catalanWords (m + 1) ↔
      (∀ i, 1 ≤ w i) ∧ w 0 = 1 ∧ ∀ i : Fin m, w i.succ ≤ w i.castSucc + 1 := by
  rw [mem_catalanWords_iff]
  refine and_congr_right fun _ => and_congr ⟨fun h => h 0 rfl, fun h i hi => ?_⟩
    ⟨fun h i => h _ _ (by simp), fun h i j hij => ?_⟩
  · rwa [show i = 0 from Fin.ext hi]
  · have hi : i.val < m := by omega
    have := h ⟨i.val, hi⟩
    rwa [show (⟨i.val, hi⟩ : Fin m).castSucc = i from Fin.ext rfl,
      show (⟨i.val, hi⟩ : Fin m).succ = j from Fin.ext (by simp [hij])] at this

private theorem snoc_mem_catalanWords {n : ℕ} (w : Fin (n + 1) → ℕ) (a : ℕ) :
    Fin.snoc (α := fun _ => ℕ) w a ∈ catalanWords (n + 2) ↔
      w ∈ catalanWords (n + 1) ∧ 1 ≤ a ∧ a ≤ w (Fin.last n) + 1 := by
  have h0 : Fin.snoc (α := fun _ => ℕ) w a 0 = w 0 :=
    Fin.snoc_castSucc (α := fun _ => ℕ) (p := w) (x := a) (i := 0)
  rw [mem_catalanWords_succ_iff, mem_catalanWords_succ_iff, h0]
  simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_castSucc,
    Fin.succ_last]
  tauto

private theorem letter_mem_Icc {n : ℕ} {w : Fin n → ℕ} (hw : w ∈ catalanWords n) (i : Fin n) :
    w i ∈ Finset.Icc 1 n := by
  simp only [catalanWords, Finset.mem_filter, Fintype.mem_piFinset] at hw
  exact hw.1 i

private theorem card_filter_last_eq {n : ℕ} (P : (Fin (n + 2) → ℕ) → Prop) [DecidablePred P]
    {a : ℕ} (ha : 1 ≤ a) :
    ((catalanWords (n + 2)).filter fun w => w (Fin.last (n + 1)) = a ∧ P w).card =
      ((catalanWords (n + 1)).filter fun w =>
        a ≤ w (Fin.last n) + 1 ∧ P (Fin.snoc (α := fun _ => ℕ) w a)).card := by
  symm
  apply Finset.card_nbij' (fun w => Fin.snoc (α := fun _ => ℕ) w a) Fin.init
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    exact ⟨(snoc_mem_catalanWords w a).mpr ⟨hw.1, ha, hw.2.1⟩, Fin.snoc_last .., hw.2.2⟩
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨hmem, hlast, hP⟩ := hw
    rw [← Fin.snoc_init_self w, hlast, snoc_mem_catalanWords] at hmem
    refine ⟨hmem.1, hmem.2.2, ?_⟩
    rw [← hlast, Fin.snoc_init_self]
    exact hP
  · intro w _
    exact Fin.init_snoc ..
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw
    rw [← hw.2.1]
    exact Fin.snoc_init_self w

private theorem wordsEndingIn_succ {n k : ℕ} (S : Finset (Fin (n + 1) → ℕ)) :
    wordsEndingIn S k = S.filter fun w => w (Fin.last n) = k := by
  unfold wordsEndingIn
  refine Finset.filter_congr fun w _ =>
    ⟨fun ⟨i, hi, hw⟩ => ?_, fun h => ⟨Fin.last n, by simp, h⟩⟩
  rwa [show i = Fin.last n from Fin.ext (by simp; omega)] at hw

/-- The weakly increasing Catalan words of length $n + 1$ ending in $k + 1$ are counted by
$\binom{n}{k}$: they rise by one at exactly $k$ of their $n$ steps. -/
private theorem card_mono : ∀ n k : ℕ,
    ((catalanWords (n + 1)).filter fun w =>
      w (Fin.last n) = k + 1 ∧ ∀ i j, j < i → w j ≤ w i).card = n.choose k
  | 0, 0 => by decide
  | 0, k + 1 => by
    rw [Nat.choose_zero_succ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw h
    have := ((mem_catalanWords_succ_iff w).mp hw).2.1
    rw [show Fin.last 0 = 0 from rfl] at h
    omega
  | n + 1, k => by
    rw [card_filter_last_eq _ (by omega : 1 ≤ k + 1), Finset.filter_congr
      (q := fun w => (w (Fin.last n) = k + 1 ∧ ∀ i j, j < i → w j ≤ w i) ∨
        (w (Fin.last n) = k ∧ ∀ i j, j < i → w j ≤ w i)) fun w _ => ?_]
    · rw [Finset.filter_or, Finset.card_union_of_disjoint
        (Finset.disjoint_filter.mpr fun w _ h1 h2 => by omega), card_mono n k]
      rcases k with _ | k
      · rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun w hw h => ?_)]
        · simp
        · have := ((mem_catalanWords_succ_iff w).mp hw).1 (Fin.last n)
          omega
      · rw [card_mono n k, Nat.choose_succ_succ', add_comm]
    · rw [mono_snoc_iff]
      constructor
      · rintro ⟨hk, hm, hle⟩
        have := hle (Fin.last n)
        by_cases h : w (Fin.last n) = k + 1
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨by omega, hm⟩
      · rintro (⟨hl, hm⟩ | ⟨hl, hm⟩) <;>
          exact ⟨by omega, hm, fun j => (le_last_of_mono hm j).trans (by omega)⟩

/-- The last-letter decomposition at capacity zero: for $i \ge 2$, a Catalan word of length
$n + 2$ ending in $i$ with capacity zero is a capacity-zero Catalan word ending in some $j \ge i$
followed by $i$, or a weakly increasing Catalan word ending in $i - 1$ followed by $i$. -/
private theorem card_zero_succ_succ (n i : ℕ) (hi : 2 ≤ i) :
    ((wordsEndingIn (catalanWords (n + 2)) i).filter fun w => wordCapacity w = 0).card =
      ∑ j ∈ Finset.Icc i (n + 1),
        ((wordsEndingIn (catalanWords (n + 1)) j).filter fun w => wordCapacity w = 0).card +
      n.choose (i - 2) := by
  rw [wordsEndingIn_succ, Finset.filter_filter, card_filter_last_eq _ (by omega : 1 ≤ i),
    Finset.filter_congr (q := fun w => (i ≤ w (Fin.last n) ∧ wordCapacity w = 0) ∨
        (w (Fin.last n) = i - 2 + 1 ∧ ∀ k j, j < k → w j ≤ w k)) fun w _ => ?_]
  · rw [Finset.filter_or, Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun w _ h1 h2 => by omega), card_mono n (i - 2),
      Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n))
        (t := Finset.Icc i (n + 1)) fun w hw => ?_]
    · congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [wordsEndingIn_succ, Finset.filter_filter, Finset.filter_filter]
      refine congrArg Finset.card (Finset.filter_congr fun w _ => ?_)
      rw [Finset.mem_Icc] at hj
      constructor
      · rintro ⟨⟨_, h0⟩, hj'⟩
        exact ⟨hj', h0⟩
      · rintro ⟨hj', h0⟩
        exact ⟨⟨hj' ▸ hj.1, h0⟩, hj'⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hw ⊢
      exact ⟨hw.2.1, (Finset.mem_Icc.mp (letter_mem_Icc hw.1 (Fin.last n))).2⟩
  · constructor
    · rintro ⟨hle, h0⟩
      by_cases h : i ≤ w (Fin.last n)
      · exact Or.inl ⟨h, (wordCapacity_snoc_eq_zero_iff_of_le w h).mp h0⟩
      · exact Or.inr ⟨by omega, (wordCapacity_snoc_eq_zero_iff_of_lt w (by omega)).mp h0⟩
    · rintro (⟨hle, h0⟩ | ⟨hl, hm⟩)
      · exact ⟨by omega, (wordCapacity_snoc_eq_zero_iff_of_le w hle).mpr h0⟩
      · exact ⟨by omega, (wordCapacity_snoc_eq_zero_iff_of_lt w (by omega)).mpr hm⟩

private theorem card_zero_eq : ∀ n i : ℕ, 2 ≤ i → i ≤ n →
    ((wordsEndingIn (catalanWords n) i).filter fun w => wordCapacity w = 0).card =
      ∑ m ∈ Finset.range (n - i + 1),
        (n - m - 2).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))
  | 0, _, hi, hin => by omega
  | 1, _, hi, hin => by omega
  | n + 2, i, hi, hin => by
    rw [card_zero_succ_succ n i hi, show n + 2 - i + 1 = n + 1 + 2 - i by omega]
    simp only [show ∀ m, n + 2 - m - 2 = n + 1 - m - 1 from fun m => by omega]
    -- The binomial sums of odd Fibonacci numbers satisfy the same recurrence.
    rw [sum_choose_mul_fib_odd_eq_choose_add_sum (n + 1) i (by omega) hi (by omega),
      show n + 1 - 1 = n from rfl, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    exact card_zero_eq (n + 1) j (by omega) hj.2

private theorem eval_zero_eq_card (n i : ℕ) :
    (catalanCapacityDist n i).eval 0 =
      (((wordsEndingIn (catalanWords n) i).filter fun w => wordCapacity w = 0).card : ℤ) := by
  rw [catalanCapacityDist, capacityDist, eval_finsetSum, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [zero_pow_eq]

end catalanCapacityDist_eval_zero

open catalanCapacityDist_eval_zero in
/-- **Zero-capacity Catalan words with a given last letter.** For $2 \le i \le n$, let
$a(n, i; q)$ be the capacity distribution of the Catalan words of length $n$ ending in $i$, so that
$a(n, i; 0)$ is the number of those words with capacity $0$. Then
$$
a(n, i; 0) = \sum_{m=0}^{n-i} \binom{n-m-2}{i-2} F_{2m-1},
$$
where $F_k$ is the $k$-th Fibonacci number ($F_1 = F_2 = 1$) and $F_{-1} = 1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`). -/
public theorem catalanCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (catalanCapacityDist n i).eval 0 =
      ∑ m ∈ Finset.range (n - i + 1),
        (((n - m - 2).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) : ℕ) : ℤ) := by
  rw [eval_zero_eq_card, card_zero_eq n i hi hin, Nat.cast_sum]

/-- **Smooth words.** For $n \ge 0$, the set $\mathcal{R}_n$ of smooth words of length $n$ consists
of the words $w = w_1 \cdots w_n$ of positive integers with $w_1 = 1$ (when $n \ge 1$) and
$|w_{i+1} - w_i| \le 1$ for $1 \le i < n$.

The letters of a smooth word of length $n$ are at most $n$, so $\mathcal{R}_n$ is finite.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public def smoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1

/-- **Characterization of smooth words.** For a natural number $n$, let $\mathcal{R}_n$ be the
set of smooth words of length $n$, defined as the words $w = w_1 \cdots w_n$ with letters in
$\{1, \dots, n\}$ such that $w_1 = 1$ when $n \ge 1$, and $w_{k+1} \le w_k + 1$ and
$w_k \le w_{k+1} + 1$ for $1 \le k < n$. A word $w = w_1 \cdots w_n$ of natural numbers belongs
to $\mathcal{R}_n$ if and only if $w_k \ge 1$ for every $k$, $w_1 = 1$ when $n \ge 1$, and
$w_{k+1} \le w_k + 1$ and $w_k \le w_{k+1} + 1$ for $1 \le k < n$. In particular, the bound
$w_k \le n$ on the letters is automatic.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public theorem mem_smoothWords_iff {n : ℕ} (w : Fin n → ℕ) :
    w ∈ smoothWords n ↔ (∀ i, 1 ≤ w i) ∧ (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1 := by
  simp only [smoothWords, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, h0, hg⟩
    exact ⟨fun i => (hb i).1, h0, hg⟩
  · rintro ⟨h1, h0, hg⟩
    have key : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k + 1 := by
      intro k
      induction k with
      | zero => intro hk; rw [h0 ⟨0, hk⟩ rfl]
      | succ k ih =>
        intro hk
        have h₁ := (hg ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).1
        have h₂ := ih (by omega)
        omega
    refine ⟨fun i => ⟨h1 i, ?_⟩, h0, hg⟩
    have := key i.val i.isLt
    rw [Fin.eta] at this
    omega

/-- **Restricted smooth words.** For $n \ge 0$, the set $\mathcal{R}^{\ast}_n$ of restricted smooth
words of length $n$ consists of the smooth words of length $n$ in which no two adjacent letters
are both equal to $1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of restricted smooth words. -/
public def restrictedSmoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (smoothWords n).filter fun w => ∀ i j : Fin n, j.val = i.val + 1 → ¬(w i = 1 ∧ w j = 1)

/-- **Capacity distribution of restricted smooth words with a given last letter.** For natural
numbers $n$ and $i$, $r^*(n, i; q)$ is the polynomial $\sum_w q^{\mathrm{cap}(w)}$ in
$\mathbb{Z}[q]$, where $w$ ranges over the restricted smooth words of length $n$ (smooth words
with no two adjacent letters equal to $1$) whose last letter is $i$, and $\mathrm{cap}(w)$ is the
capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `r*(n, i; q)`. -/
public noncomputable def restrictedSmoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (restrictedSmoothWords n) i)

namespace restrictedSmoothCapacityDist_eval_zero

open catalanCapacityDist_eval_zero

private theorem mem_restricted {n : ℕ} (w : Fin (n + 1) → ℕ) :
    w ∈ restrictedSmoothWords (n + 1) ↔ (∀ j, 1 ≤ w j) ∧ w 0 = 1 ∧
      ∀ j : Fin n, w j.succ ≤ w j.castSucc + 1 ∧ w j.castSucc ≤ w j.succ + 1 ∧
        ¬(w j.castSucc = 1 ∧ w j.succ = 1) := by
  simp only [restrictedSmoothWords, mem_filter, mem_smoothWords_iff]
  constructor
  · rintro ⟨⟨hp, h₀, hs⟩, hr⟩
    exact ⟨hp, h₀ 0 rfl, fun j =>
      ⟨(hs j.castSucc j.succ rfl).1, (hs j.castSucc j.succ rfl).2, hr _ _ rfl⟩⟩
  · rintro ⟨hp, h₀, hs⟩
    have adj (a b : Fin (n + 1)) (h : b.val = a.val + 1) :
        w b ≤ w a + 1 ∧ w a ≤ w b + 1 ∧ ¬(w a = 1 ∧ w b = 1) := by
      let j : Fin n := ⟨a, by omega⟩
      have hj : j.succ = b := Fin.ext h.symm
      simpa only [hj, show j.castSucc = a from Fin.ext rfl] using hs j
    exact ⟨⟨hp, fun j hj => (Fin.ext hj : j = 0) ▸ h₀,
      fun a b h => ⟨(adj a b h).1, (adj a b h).2.1⟩⟩, fun a b h => (adj a b h).2.2⟩

-- The appended letter is at least two, so the final pair cannot be a pair of ones.
private theorem snoc_mem {n : ℕ} (w : Fin (n + 1) → ℕ) {a : ℕ} (ha : 2 ≤ a) :
    Fin.snoc (α := fun _ => ℕ) w a ∈ restrictedSmoothWords (n + 2) ↔
      w ∈ restrictedSmoothWords (n + 1) ∧ a ≤ w (Fin.last n) + 1 ∧ w (Fin.last n) ≤ a + 1 := by
  have h₀ : Fin.snoc (α := fun _ => ℕ) w a 0 = w 0 :=
    Fin.snoc_castSucc (α := fun _ => ℕ) (p := w) (x := a) (i := 0)
  rw [mem_restricted, mem_restricted, h₀]
  simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_castSucc,
    Fin.succ_last, show 1 ≤ a by omega, show a ≠ 1 by omega, and_false, not_false_eq_true]
  tauto

private theorem card_snoc {n a : ℕ} (ha : 2 ≤ a)
    (P : (Fin (n + 2) → ℕ) → Prop) [DecidablePred P] :
    ((restrictedSmoothWords (n + 2)).filter fun w => w (Fin.last (n + 1)) = a ∧ P w).card =
      ((restrictedSmoothWords (n + 1)).filter fun w => (a ≤ w (Fin.last n) + 1 ∧
        w (Fin.last n) ≤ a + 1) ∧ P (Fin.snoc (α := fun _ => ℕ) w a)).card := by
  symm
  apply card_nbij' (fun w => Fin.snoc (α := fun _ => ℕ) w a) Fin.init
  · intro w hw
    simp only [mem_coe, mem_filter] at hw ⊢
    exact ⟨(snoc_mem w ha).mpr ⟨hw.1, hw.2.1⟩, Fin.snoc_last .., hw.2.2⟩
  · intro w hw
    simp only [mem_coe, mem_filter] at hw ⊢
    obtain ⟨hmem, hlast, hP⟩ := hw
    rw [← Fin.snoc_init_self w, hlast, snoc_mem _ ha] at hmem
    refine ⟨hmem.1, hmem.2, ?_⟩
    rwa [← hlast, Fin.snoc_init_self]
  · exact fun _ _ => Fin.init_snoc ..
  · intro w hw
    rw [← (mem_filter.mp hw).2.1]
    exact Fin.snoc_init_self w

private def monoCount (n a : ℕ) :=
  ((restrictedSmoothWords (n + 1)).filter fun w =>
    w (Fin.last n) = a ∧ ∀ k j, j < k → w j ≤ w k).card

private def zeroCount (n a : ℕ) :=
  ((restrictedSmoothWords (n + 1)).filter fun w =>
    w (Fin.last n) = a ∧ wordCapacity w = 0).card

private theorem monoCount_succ (n k : ℕ) :
    monoCount (n + 1) (k + 2) = monoCount n (k + 2) + monoCount n (k + 1) := by
  unfold monoCount
  rw [card_snoc (by omega : 2 ≤ k + 2), filter_congr
    (q := fun w => (w (Fin.last n) = k + 2 ∧ ∀ l j, j < l → w j ≤ w l) ∨
      (w (Fin.last n) = k + 1 ∧ ∀ l j, j < l → w j ≤ w l)) fun w _ => ?_]
  · rw [filter_or, card_union_of_disjoint (disjoint_filter.mpr fun w _ h h' => by omega)]
  · rw [mono_snoc_iff]
    constructor
    · rintro ⟨⟨hle, _⟩, hm, hbound⟩
      have := hbound (Fin.last n)
      exact (show w (Fin.last n) = k + 2 ∨ w (Fin.last n) = k + 1 by omega).imp
        (fun h => ⟨h, hm⟩) (fun h => ⟨h, hm⟩)
    · rintro (⟨hl, hm⟩ | ⟨hl, hm⟩) <;>
        exact ⟨⟨by omega, by omega⟩, hm, fun j => (le_last_of_mono hm j).trans (by omega)⟩

private theorem monoCount_one (n : ℕ) : monoCount (n + 1) 1 = 0 := by
  rw [monoCount, card_eq_zero, filter_eq_empty_iff]
  intro w hw ⟨hl, hm⟩
  obtain ⟨hp, h₀, hs⟩ := (mem_restricted w).mp hw
  have h := (hs 0).2.2
  have hle := le_last_of_mono hm (0 : Fin (n + 1)).succ
  have hpos := hp (0 : Fin (n + 1)).succ
  exact h ⟨h₀, by omega⟩

private theorem last_le_length {n : ℕ} {w : Fin (n + 1) → ℕ}
    (hw : w ∈ restrictedSmoothWords (n + 1)) : w (Fin.last n) ≤ n + 1 :=
  (mem_Icc.mp ((Fintype.mem_piFinset.mp (mem_filter.mp (mem_filter.mp hw).1).1) _)).2

-- A monotone restricted word starts with 12. Each later step is flat or rises by one.
private theorem monoCount_eq (n k : ℕ) : monoCount (n + 1) (k + 2) = n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => decide
    | succ k =>
      rw [Nat.choose_zero_succ, monoCount, card_eq_zero, filter_eq_empty_iff]
      rintro w hw ⟨hl, _⟩
      have hb := last_le_length hw
      rw [hl] at hb
      omega
  | succ n ih =>
    rw [monoCount_succ, ih]
    cases k with
    | zero => simp [monoCount_one]
    | succ k => rw [ih, Nat.choose_succ_succ']; omega

-- A final rise forces a monotone prefix. A flat step or fall preserves zero capacity.
private theorem zeroCount_succ (n k : ℕ) :
    zeroCount (n + 1) (k + 3) =
      zeroCount n (k + 3) + zeroCount n (k + 4) + monoCount n (k + 2) := by
  unfold zeroCount monoCount
  rw [card_snoc (by omega : 2 ≤ k + 3), filter_congr
    (q := fun w => ((w (Fin.last n) = k + 3 ∧ wordCapacity w = 0) ∨
      (w (Fin.last n) = k + 4 ∧ wordCapacity w = 0)) ∨
      (w (Fin.last n) = k + 2 ∧ ∀ l j, j < l → w j ≤ w l)) fun w _ => ?_]
  · rw [filter_or, card_union_of_disjoint (disjoint_filter.mpr fun w _ h h' => by
      rcases h with h | h <;> omega), filter_or,
      card_union_of_disjoint (disjoint_filter.mpr fun w _ h h' => by omega)]
  · by_cases h : k + 3 ≤ w (Fin.last n)
    · rw [wordCapacity_snoc_eq_zero_iff_of_le w h]
      omega
    · rw [wordCapacity_snoc_eq_zero_iff_of_lt w (by omega)]
      constructor
      · rintro ⟨⟨hle, _⟩, hm⟩
        exact Or.inr ⟨by omega, hm⟩
      · rintro ((h' | h') | ⟨hl, hm⟩)
        · omega
        · omega
        · exact ⟨⟨by omega, by omega⟩, hm⟩

-- Remove the first term of the new binomial tail and split all later terms by Pascal's rule.
private theorem tail_succ (n k : ℕ) :
    ∑ j ∈ Icc k (n + 1), (n + 1).choose j =
      (∑ j ∈ Icc k n, n.choose j) + (∑ j ∈ Icc (k + 1) n, n.choose j) + (n + 1).choose k := by
  by_cases hk : k ≤ n
  · simp only [← Ico_add_one_right_eq_Icc]
    rw [sum_eq_sum_Ico_succ_bot (by omega : k < n + 1 + 1),
      ← sum_Ico_add' _ k (n + 1) 1]
    simp_rw [Nat.choose_succ_succ']
    rw [sum_add_distrib, sum_Ico_add' _ k (n + 1) 1,
      sum_Ico_succ_top (by omega : k + 1 ≤ n + 1), Nat.choose_succ_self]
    omega
  · rw [Icc_eq_empty_of_lt (show n < k by omega),
      Icc_eq_empty_of_lt (show n < k + 1 by omega)]
    rcases (show n + 1 ≤ k by omega).eq_or_lt with rfl | h
    · simp
    · simp [Icc_eq_empty_of_lt h, Nat.choose_eq_zero_of_lt h]

private theorem zeroCount_eq (n k : ℕ) :
    zeroCount (n + 2) (k + 3) = ∑ j ∈ Icc k n, n.choose j := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => decide
    | succ k =>
      rw [Icc_eq_empty_of_lt (Nat.zero_lt_succ _), sum_empty, zeroCount, card_eq_zero,
        filter_eq_empty_iff]
      rintro w hw ⟨hl, _⟩
      have hb := last_le_length hw
      rw [hl] at hb
      omega
  | succ n ih =>
    rw [zeroCount_succ, ih, ih (k + 1), monoCount_eq, tail_succ]

private theorem eval_zero_eq_count (n i : ℕ) :
    (restrictedSmoothCapacityDist (n + 1) i).eval 0 = (zeroCount n i : ℤ) := by
  rw [restrictedSmoothCapacityDist, capacityDist, eval_finsetSum, zeroCount, ← filter_filter,
    ← wordsEndingIn_succ, card_filter]
  push_cast
  refine sum_congr rfl fun w _ => ?_
  simp [zero_pow_eq]

end restrictedSmoothCapacityDist_eval_zero

open restrictedSmoothCapacityDist_eval_zero in
/-- **Zero-capacity restricted smooth words with a given last letter.** For natural numbers $n$
and $i$ with $3 \le i \le n$, let $r^*(n, i; q)$ be the capacity distribution of the restricted
smooth words of length $n$ ending in $i$. Its value at $q = 0$, which is the number of such words
of capacity $0$, is
$$r^*(n, i; 0) = \sum_{j=i-3}^{n-3} \binom{n-3}{j}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 10 (`integers-2025-A5-thm-10`). -/
public theorem restrictedSmoothCapacityDist_eval_zero (n i : ℕ) (hi : 3 ≤ i)
    (hin : i ≤ n) :
    (restrictedSmoothCapacityDist n i).eval 0 =
      ∑ j ∈ Finset.Icc (i - 3) (n - 3), ((n - 3).choose j : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [eval_zero_eq_count, zeroCount_eq, Nat.cast_sum]
  simp

/-- **Capacity distribution of smooth words by last letter.** For $n, i \ge 0$, $r(n, i; q)$ is the
polynomial $\sum_w q^{\operatorname{cap}(w)} \in \mathbb{Z}[q]$, where $w$ runs over the smooth
words of length $n$ whose last letter is $i$ and $\operatorname{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `r(n, i; q)`. -/
public noncomputable def smoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (smoothWords n) i)

namespace smoothCapacityDist_eval_zero

open catalanCapacityDist_eval_zero

-- Raising the word by one and prepending a 1 puts a 2 at its second position.
private def raiseWord {n : ℕ} (w : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  Fin.cons 1 fun j => w j + 1

private theorem raiseWord_mem_iff {n : ℕ} (w : Fin (n + 1) → ℕ) (hp : ∀ j, 1 ≤ w j) :
    raiseWord w ∈ restrictedSmoothWords (n + 2) ↔ w ∈ smoothWords (n + 1) := by
  have hne (j) : w j ≠ 0 := Nat.ne_of_gt (hp j)
  have hstart : w 0 ≤ 1 ↔ w 0 = 1 := ⟨fun h => h.antisymm (hp 0), fun h => h.le⟩
  simp [raiseWord, restrictedSmoothWords, mem_smoothWords_iff, Fin.forall_fin_succ (n := n + 1),
    hp, Fin.val_eq_zero_iff, hne, hstart]

private theorem raiseWord_zero_iff {n : ℕ} (w : Fin n → ℕ) :
    wordCapacity (raiseWord w) = 0 ↔ wordCapacity w = 0 := by
  simp [wordCapacity_eq_zero_iff, raiseWord, Fin.forall_fin_succ (n := n)]

-- A return to 1 after the initial 12 would trap water between the 2 and the last letter.
private theorem tail_ge_two {n : ℕ} {v : Fin (n + 2) → ℕ}
    (hv : v ∈ restrictedSmoothWords (n + 2)) (hc : wordCapacity v = 0)
    (hl : 2 ≤ v (Fin.last (n + 1))) (j : Fin (n + 1)) : 2 ≤ v j.succ := by
  obtain ⟨hp, h₀, hadj⟩ := (restrictedSmoothCapacityDist_eval_zero.mem_restricted v).mp hv
  have hsecond : 2 ≤ v (0 : Fin (n + 1)).succ := by
    have h := (hadj 0).2.2
    have := hp (0 : Fin (n + 1)).succ
    simp only [Fin.castSucc_zero, h₀, true_and] at h
    omega
  rcases (wordCapacity_eq_zero_iff v).mp hc j.succ with h | h
  · rcases (Fin.zero_le j).lt_or_eq with hj | hj
    · exact hsecond.trans (h _ (Fin.succ_lt_succ_iff.mpr hj))
    · simpa [← hj] using hsecond
  · rcases (Fin.le_last j.succ).lt_or_eq with hj | hj
    · exact hl.trans (h _ hj)
    · rwa [hj]

private theorem card_zero_eq_restricted (n i : ℕ) (hi : 2 ≤ i) :
    ((smoothWords (n + 1)).filter fun w => w (Fin.last n) = i ∧ wordCapacity w = 0).card =
      ((restrictedSmoothWords (n + 2)).filter fun v =>
        v (Fin.last (n + 1)) = i + 1 ∧ wordCapacity v = 0).card := by
  apply card_bij (fun w _ => raiseWord w)
  · intro w hw
    obtain ⟨hw, hl, hc⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨(raiseWord_mem_iff w ((mem_smoothWords_iff w).mp hw).1).mpr hw,
      by simpa [← Fin.succ_last, raiseWord] using hl, (raiseWord_zero_iff w).mpr hc⟩
  · intro w _ u _ h
    funext j
    simpa [raiseWord] using congrFun h j.succ
  · intro v hv
    obtain ⟨hv, hl, hc⟩ := mem_filter.mp hv
    let w (j : Fin (n + 1)) := v j.succ - 1
    have htail := tail_ge_two hv hc (by omega : 2 ≤ v (Fin.last (n + 1)))
    have hp (j : Fin (n + 1)) : 1 ≤ w j := by
      dsimp [w]
      have := htail j
      omega
    have heq : raiseWord w = v := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ((restrictedSmoothCapacityDist_eval_zero.mem_restricted v).mp hv).2.1.symm
      · change v k.succ - 1 + 1 = v k.succ
        have := htail k
        omega
    refine ⟨w, mem_filter.mpr ⟨(raiseWord_mem_iff w hp).mp (heq ▸ hv), ?_,
      (raiseWord_zero_iff w).mp (heq ▸ hc)⟩, heq⟩
    simp [w, hl]

private theorem eval_zero_eq_card {n : ℕ} (S : Finset (Fin (n + 1) → ℕ)) (i : ℕ) :
    (capacityDist (wordsEndingIn S i)).eval 0 =
      (((S.filter fun w => w (Fin.last n) = i ∧ wordCapacity w = 0).card) : ℤ) := by
  rw [capacityDist, eval_finsetSum, ← filter_filter, ← wordsEndingIn_succ, card_filter]
  push_cast
  refine sum_congr rfl fun w _ => ?_
  simp [zero_pow_eq]

end smoothCapacityDist_eval_zero

open smoothCapacityDist_eval_zero in
/-- **Zero-capacity smooth words with a given last letter.** For $2 \le i \le n$, the number of
smooth words of length $n$ ending in $i$ with capacity $0$, that is, the value at $q = 0$ of their
capacity distribution $r(n, i; q)$, equals $\sum_{j=i-2}^{n-2} \binom{n-2}{j}$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 6 (`integers-2025-A5-thm-6`). -/
public theorem smoothCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (smoothCapacityDist n i).eval 0 = ∑ j ∈ Finset.Icc (i - 2) (n - 2), ((n - 2).choose j : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc
    _ = (restrictedSmoothCapacityDist (m + 2) (i + 1)).eval 0 := by
      rw [smoothCapacityDist, restrictedSmoothCapacityDist, eval_zero_eq_card, eval_zero_eq_card,
        card_zero_eq_restricted m i hi]
    _ = _ := by
      simpa using restrictedSmoothCapacityDist_eval_zero (m + 2) (i + 1) (by omega) (by omega)

end

end CatalanCapacity

end MetaMathlibExt
