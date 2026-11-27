/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Word models for generalized Rascal numbers -/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

/-- **Number of ascents of a word.** For a finite word
$w = w_1 w_2 \cdots w_n$ of natural numbers, the number of ascents
of $w$ is the number of indices $i$ with $1 \le i < n$ and
$w_i < w_{i+1}$. -/
def wordAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a < b then 1 else 0) + wordAscents (b :: t)

/-- **Binary words with few ascents.** For natural numbers $j$, $k$ and $n$, $B^{(j)}_k(n)$ is
the set of words $w$ of length $n$ over the alphabet $\{0, 1\}$ with exactly $k$ ones and at most
$j$ ascents, an ascent being a position $i$ with $w_i < w_{i+1}$, that is, a $0$ immediately
followed by a $1$. -/
def RascalWord (j k n : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ (∀ x ∈ w, x = 0 ∨ x = 1) ∧
      w.count 1 = k ∧ wordAscents w ≤ j }

/-- **Generalized Rascal numbers.** For natural numbers $j$, $k$ and $n$, the generalized Rascal
number $R^{(j)}_{n,k}$ is the number of binary words of length $n$ with exactly $k$ ones and at
most $j$ ascents, that is, the number of elements of $B^{(j)}_k(n)$; an ascent is a position at
which a $0$ is immediately followed by a $1$. -/
noncomputable def rascalGen (j k n : ℕ) : ℕ :=
  Nat.card (RascalWord j k n)

/-- **Generalized Rascal numbers at integer indices.** For a natural number $j$ and integers $n$
and $k$, $R^{(j)}_{n,k}$ is the generalized Rascal number of $n$ and $k$ (the number of binary
words of length $n$ with exactly $k$ ones and at most $j$ ascents) when $0 \le k \le n$, and $0$
otherwise. -/
noncomputable def rascalGenZ (j : ℕ) (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then (rascalGen j k.toNat n.toNat : ℤ) else 0

/-- **Ascent sequences.** A finite sequence $w_1 w_2 \cdots w_n$ of natural numbers is an
ascent sequence when $w_1 = 0$ (if $n \ge 1$) and
$w_i \le \operatorname{asc}(w_1 \cdots w_{i-1}) + 1$ for every $1 \le i \le n$, where
$\operatorname{asc}(v)$ counts the positions $j$ with $v_j < v_{j+1}$. In particular the empty
sequence is an ascent sequence. -/
def IsAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordAscents (w.take i) + 1

/-- **Avoiding the patterns 001 and 210.** A finite sequence $w$ of natural numbers avoids
$001$ and $210$ when it has no subsequence $x, x, y$ with $x < y$ and no subsequence $x, y, z$
with $x > y > z$. Subsequences need not consist of consecutive entries. -/
def Avoids001210 (w : List ℕ) : Prop :=
  ∀ x y z : ℕ, List.Sublist [x, y, z] w →
    ¬ (x = y ∧ y < z) ∧ ¬ (z < y ∧ y < x)

/-- **Ascent sequences avoiding 001 and 210.** For natural numbers $n$ and $k$, this is the set
of ascent sequences $w$ of length $n$ that avoid the patterns $001$ and $210$ and have exactly
$k$ ascents, an ascent of $w$ being a position $i$ with $w_i < w_{i+1}$. -/
def AscentSeqAvoid (n k : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ IsAscentSeq w ∧ Avoids001210 w ∧
      wordAscents w = k }

/-- **Number of ascent sequences avoiding 001 and 210.** For natural numbers $n$ and $k$, this
counts the ascent sequences of length $n$ with exactly $k$ ascents that avoid the patterns
$001$ and $210$. -/
noncomputable def apkCard (n k : ℕ) : ℕ :=
  Nat.card (AscentSeqAvoid n k)

-- Flip the bits in odd positions, numbering positions from one.
private def flipOdd : List ℕ → List ℕ
  | [] => []
  | [a] => [Equiv.swap 0 1 a]
  | a :: b :: t => Equiv.swap 0 1 a :: b :: flipOdd t

private theorem flipOdd_involutive : Function.Involutive flipOdd := by
  intro w
  fun_induction flipOdd w <;> simp [flipOdd, *]

private theorem flipOdd_mem_iff {w : List ℕ} (n : ℕ) :
    flipOdd w ∈ List.fixedLengthDigits (b := 2) (by decide) n ↔
      w ∈ List.fixedLengthDigits (b := 2) (by decide) n := by
  have swap_lt (a : ℕ) : Equiv.swap 0 1 a < 2 ↔ a < 2 := by
    by_cases h : a = 0 <;> by_cases h' : a = 1 <;> simp [*, Equiv.swap_apply_def]
  simp only [List.mem_fixedLengthDigits_iff]
  apply and_congr
  · suffices h : (flipOdd w).length = w.length by rw [h]
    fun_induction flipOdd w <;> simp [*]
  · fun_induction flipOdd w <;> simp only [List.forall_mem_cons, *]

-- The two adjacencies at an even position contribute one ascent between the two words.
private theorem paired_ascents (m : ℕ) (w : List ℕ) (hlen : w.length = 2 * m + 1)
    (hw : ∀ x ∈ w, x < 2) : wordAscents w + wordAscents (flipOdd w) = m := by
  induction m generalizing w with
  | zero =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
    rfl
  | succ m ih =>
    match w with
    | [] | [_] | [_, _] => simp at hlen
    | a :: b :: c :: t =>
      simp only [List.forall_mem_cons] at hw
      simp only [List.length_cons] at hlen
      have htail := ih (c :: t) (by simp; omega) (List.forall_mem_cons.mpr hw.2.2)
      obtain ⟨u, hu⟩ : ∃ u, flipOdd (c :: t) = Equiv.swap 0 1 c :: u := by
        cases t <;> exact ⟨_, rfl⟩
      rw [hu] at htail
      rw [flipOdd, hu]
      simp only [wordAscents]
      obtain ⟨ha, hb, hc, _⟩ := hw
      interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all <;> omega

private theorem sum_rascalGen_eq_card (j n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rascalGen j k n =
      ((List.fixedLengthDigits (b := 2) (by decide) n).filter (wordAscents · ≤ j)).card := by
  let words := (List.fixedLengthDigits (b := 2) (by decide) n).filter (wordAscents · ≤ j)
  have fiber (k : ℕ) : rascalGen j k n = (words.filter (fun w => w.count 1 = k)).card := by
    apply Nat.subtype_card
    intro w
    have bit (x : ℕ) : x < 2 ↔ x = 0 ∨ x = 1 := by omega
    simp [words, List.mem_fixedLengthDigits_iff, bit, and_assoc, and_left_comm, and_comm]
  simp_rw [fiber]
  apply Eq.symm
  apply Finset.card_eq_sum_card_fiberwise
  intro w hw
  have hlen := ((List.mem_fixedLengthDigits_iff _).mp (Finset.mem_filter.mp hw).1).1
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hlen ▸ List.count_le_length))

/-- **A power-of-two row sum of generalized Rascal numbers.** Write $R^{(j)}_{n,k}$ for the number
of binary words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions where a
$0$ is immediately followed by a $1$). For every natural number $j$,
$\sum_{k=0}^{4j+3} R^{(j)}_{4j+3,k} = 2^{4j+2}$.

This was Conjecture 7.5 of Gregory et al.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 21. -/
theorem sum_rascalGen_four_mul_add_three (j : ℕ) :
    ∑ k ∈ Finset.range (4 * j + 4),
        (rascalGen j k (4 * j + 3) : ℤ) = 2 ^ (4 * j + 2) := by
  let words := List.fixedLengthDigits (b := 2) (by decide) (4 * j + 3)
  have swaps (w : List ℕ) (hw : w ∈ words) :
      wordAscents w ≤ j ↔ ¬ wordAscents (flipOdd w) ≤ j := by
    obtain ⟨hlen, hbits⟩ := (List.mem_fixedLengthDigits_iff _).mp hw
    have := paired_ascents (2 * j + 1) w (by omega) hbits
    omega
  have equal : (words.filter (wordAscents · ≤ j)).card =
      (words.filter (fun w => ¬ wordAscents w ≤ j)).card := by
    apply Finset.card_bijective flipOdd flipOdd_involutive.bijective
    intro w
    simp only [Finset.mem_filter, flipOdd_mem_iff, words]
    exact and_congr_right (swaps w)
  have halves := Finset.card_filter_add_card_filter_not (s := words) (wordAscents · ≤ j)
  rw [← equal, List.card_fixedLengthDigits, pow_succ] at halves
  have half : (words.filter (wordAscents · ≤ j)).card = 2 ^ (4 * j + 2) := by omega
  rw [← Nat.cast_sum]
  exact_mod_cast (sum_rascalGen_eq_card j (4 * j + 3)).trans half

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
