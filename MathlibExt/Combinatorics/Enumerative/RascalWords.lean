/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
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

-- For binary digits, swapping 0 with the previous bit gives 1 exactly when the bit changes.
private def changeFlags (prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: w => Equiv.swap 0 prev b :: changeFlags b w

private def scanChanges (prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | f :: w =>
    let b := Equiv.swap 0 prev f
    b :: scanChanges b w

private def changeFlagsEquiv (prev : ℕ) : List ℕ ≃ List ℕ where
  toFun := changeFlags prev
  invFun := scanChanges prev
  left_inv w := by induction w generalizing prev <;> simp [changeFlags, scanChanges, *]
  right_inv w := by induction w generalizing prev <;> simp [changeFlags, scanChanges, *]

private theorem changeFlags_mem_iff (n : ℕ) (w : List ℕ) (prev : ℕ) (hp : prev < 2) :
    changeFlags prev w ∈ List.fixedLengthDigits (b := 2) (by decide) n ↔
      w ∈ List.fixedLengthDigits (b := 2) (by decide) n := by
  have hlen (l : List ℕ) (p : ℕ) : (changeFlags p l).length = l.length := by
    induction l generalizing p <;> simp [changeFlags, *]
  simp only [List.mem_fixedLengthDigits_iff, hlen]
  refine and_congr Iff.rfl ?_
  induction w generalizing prev with
  | nil => simp [changeFlags]
  | cons b w ih =>
    have hswap : Equiv.swap 0 prev b < 2 ↔ b < 2 := by
      by_cases h0 : b = 0
      · simp [h0, hp]
      by_cases hprev : b = prev
      · simp [hprev, hp]
      rw [Equiv.swap_apply_of_ne_of_ne h0 hprev]
    simp only [changeFlags, List.forall_mem_cons, hswap]
    exact and_congr_right (ih b)

-- A 0 sentinel makes the first change an ascent; a 1 sentinel makes the second an ascent.
private theorem ascents_eq_half_changes (w : List ℕ) (prev : ℕ) (hp : prev < 2)
    (hw : ∀ b ∈ w, b < 2) :
    wordAscents (prev :: w) = ((changeFlags prev w).count 1 + (1 - prev)) / 2 := by
  induction w generalizing prev with
  | nil => simp [wordAscents, changeFlags]; omega
  | cons b w ih =>
    rw [List.forall_mem_cons] at hw
    have htail := ih b hw.1 hw.2
    have hb := hw.1
    interval_cases prev <;> interval_cases b <;>
      simp [wordAscents, changeFlags] at htail ⊢ <;> omega

-- A binary word with k ones is specified by a k-element set of positions.
private theorem card_fixedLengthBits_count (n k : ℕ) :
    ((List.fixedLengthDigits (b := 2) (by decide) n).filter (fun w => w.count 1 = k)).card =
      n.choose k := by
  let word (s : Finset (Fin n)) : List ℕ := List.ofFn fun i => if i ∈ s then 1 else 0
  have hcard (s : Finset (Fin n)) : (word s).count 1 = s.card := by
    dsimp only [word]
    rw [List.count_ofFn]
    congr 1
    ext i
    simp
  rw [← show ((Finset.univ : Finset (Fin n)).powersetCard k).card = n.choose k by simp]
  symm
  refine Finset.card_bij (fun s _ => word s) ?_ ?_ ?_
  · intro s hs
    refine Finset.mem_filter.mpr ⟨(List.mem_fixedLengthDigits_iff _).mpr ⟨by simp [word], ?_⟩, ?_⟩
    · simp only [word, List.forall_mem_ofFn_iff]
      intro i
      split <;> decide
    · rw [hcard]
      exact (Finset.mem_powersetCard.mp hs).2
  · intro s _ t _ h
    have heq := List.ofFn_injective h
    ext i
    have hi := congrFun heq i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  · intro w hw
    obtain ⟨hw, hcount⟩ := Finset.mem_filter.mp hw
    obtain ⟨hlen, hbits⟩ := (List.mem_fixedLengthDigits_iff _).mp hw
    subst n
    let s : Finset (Fin w.length) := Finset.univ.filter fun i => w.get i = 1
    have hs : word s = w := calc
      word s = List.ofFn w.get := by
        unfold word
        congr 1
        funext i
        have hi := hbits (w.get i) (List.get_mem w i)
        have hb : w.get i = 0 ∨ w.get i = 1 := by omega
        rcases hb with h | h <;>
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, h, zero_ne_one,
            ite_false, ite_true]
      _ = w := List.ofFn_get w
    exact ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by rw [← hcard, hs, hcount]⟩, hs⟩

/-- **Row sums of generalized Rascal numbers.** Write $R^{(j)}_{n,k}$ for the number of binary
words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions where a $0$ is
immediately followed by a $1$). For all natural numbers $j$ and $n$,
$\sum_{k=0}^{n} R^{(j)}_{n,k} = \sum_{k=0}^{2j+1} \binom{n}{k}$, where $\binom{n}{k} = 0$ for
$k > n$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 20. -/
theorem sum_rascalGen_row (j n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (rascalGen j k n : ℤ) =
      ∑ k ∈ Finset.range (2 * j + 2), (Nat.choose n k : ℤ) := by
  let words := List.fixedLengthDigits (b := 2) (by decide) n
  let flags := words.filter (fun w => w.count 1 ≤ 2 * j + 1)
  have hflags : (words.filter (wordAscents · ≤ j)).card = flags.card := by
    apply Finset.card_bijective (changeFlags 1) (changeFlagsEquiv 1).bijective
    intro w
    simp only [flags, Finset.mem_filter, words, changeFlags_mem_iff n w 1 (by decide)]
    apply and_congr_right
    intro hw
    have hbits := ((List.mem_fixedLengthDigits_iff _).mp hw).2
    have hchanges := ascents_eq_half_changes w 1 (by decide) hbits
    have hsentinel : wordAscents (1 :: w) = wordAscents w := by
      cases w with
      | nil => rfl
      | cons b w =>
        have hb := hbits b (by simp)
        simp [wordAscents, show ¬ 1 < b by omega]
    rw [hsentinel] at hchanges
    omega
  have hcount : flags.card = ∑ k ∈ Finset.range (2 * j + 2), n.choose k := by
    calc
      flags.card = ∑ k ∈ Finset.range (2 * j + 2),
          (flags.filter (fun w => w.count 1 = k)).card := by
        apply Finset.card_eq_sum_card_fiberwise
        intro w hw
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hw).2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← card_fixedLengthBits_count n k]
        congr 1
        ext w
        simp only [flags, words, Finset.mem_filter, Finset.mem_range, and_assoc] at hk ⊢
        exact and_congr_right (fun _ => and_iff_right_of_imp (fun h => by omega))
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_rascalGen_eq_card, hflags, hcount]

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

-- Reverse the order of the letters and exchange 0 and 1.
private def reverseComplement (w : List ℕ) : List ℕ :=
  (w.map (Equiv.swap 0 1)).reverse

private theorem reverseComplement_involutive : Function.Involutive reverseComplement := by
  intro w
  simp [reverseComplement, List.map_map, Function.comp_def]

private theorem wordAscents_append_pair (w : List ℕ) (a b : ℕ) :
    wordAscents (w ++ [a, b]) = wordAscents (w ++ [a]) + (if a < b then 1 else 0) := by
  induction w using wordAscents.induct <;> simp_all [wordAscents, Nat.add_assoc]

private theorem reverseComplement_cons (a : ℕ) (w : List ℕ) :
    reverseComplement (a :: w) = reverseComplement w ++ [Equiv.swap 0 1 a] := by
  simp only [reverseComplement, List.map_cons, List.reverse_cons]

-- Reversing an adjacent pair and swapping its bits sends 01 to 01.
private theorem wordAscents_reverseComplement (w : List ℕ) (hw : ∀ x ∈ w, x = 0 ∨ x = 1) :
    wordAscents (reverseComplement w) = wordAscents w := by
  induction w using wordAscents.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 a b t ih =>
    rw [reverseComplement_cons a, reverseComplement_cons b, List.append_assoc,
      List.singleton_append, wordAscents_append_pair, ← reverseComplement_cons,
      ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)), wordAscents]
    obtain rfl | rfl := hw a (by simp)
    all_goals obtain rfl | rfl := hw b (by simp)
    all_goals simp [Nat.add_comm]

private theorem count_reverseComplement (w : List ℕ) (hw : ∀ x ∈ w, x = 0 ∨ x = 1) :
    (reverseComplement w).count 1 = w.length - w.count 1 := by
  have hcount : (w.map (Equiv.swap 0 1)).count 1 = w.count 0 := by
    simpa only [Equiv.swap_apply_left] using
      List.count_map_of_injective w (Equiv.swap 0 1) (Equiv.swap 0 1).injective 0
  have hzero : w.count 0 = w.countP (fun x => ¬ (x == 1)) := by
    rw [List.count_eq_countP]
    apply List.countP_congr
    intro x hx
    obtain rfl | rfl := hw x hx <;> decide
  have hsum := List.length_eq_countP_add_countP (· == 1) (l := w)
  rw [← List.count_eq_countP, ← hzero] at hsum
  rw [reverseComplement, List.count_reverse, hcount]
  omega

private def reverseComplementWord {j k n k' : ℕ} (w : RascalWord j k n) (h : k' = n - k) :
    RascalWord j k' n := by
  obtain ⟨w, hlen, hbinary, hcount, hasc⟩ := w
  refine ⟨reverseComplement w, ?_, ?_, ?_, ?_⟩
  · simpa [reverseComplement] using hlen
  · intro x hx
    rw [reverseComplement, List.mem_reverse, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain rfl | rfl := hbinary a ha <;> simp
  · rw [count_reverseComplement w hbinary, hlen, hcount, h]
  · rwa [wordAscents_reverseComplement w hbinary]

private theorem rascalGen_reflect (j k n : ℕ) (hk : k ≤ n) :
    rascalGen j (n - k) n = rascalGen j k n := by
  apply Eq.symm
  exact Nat.card_congr
    { toFun := fun w => reverseComplementWord w rfl
      invFun := fun w => reverseComplementWord w (by omega)
      left_inv := fun w => Subtype.ext (reverseComplement_involutive w.1)
      right_inv := fun w => Subtype.ext (reverseComplement_involutive w.1) }

/-- **Alternating row sums of generalized Rascal numbers vanish on odd rows.** Write
$R^{(j)}_{n,k}$ for the number of binary words of length $n$ with exactly $k$ ones and at most
$j$ ascents (positions where a $0$ is immediately followed by a $1$). For all natural numbers
$j$ and $m$, $\sum_{k=0}^{2m+1} (-1)^k R^{(j)}_{2m+1,k} = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 23. -/
theorem sum_rascalGen_alternating_odd (j m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * (rascalGen j k (2 * m + 1) : ℤ) = 0 := by
  let n := 2 * m + 1
  let f (k : ℕ) : ℤ := (-1 : ℤ) ^ k * (rascalGen j k n : ℤ)
  have hodd : (-1 : ℤ) ^ n = -1 := by
    simp [n, pow_succ, pow_mul]
  have hpair (k : ℕ) (hk : k ≤ n) : f (n - k) = -f k := by
    have hsign : (-1 : ℤ) ^ (n - k) = -((-1 : ℤ) ^ k) := by
      calc
        (-1 : ℤ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
          rw [← pow_add, show n + k = n - k + 2 * k by omega, pow_add, pow_mul,
            neg_one_sq, one_pow, mul_one]
        _ = _ := by rw [hodd, neg_one_mul]
    simp only [f, rascalGen_reflect j k n hk, hsign, neg_mul]
  change (∑ k ∈ Finset.range (n + 1), f k) = 0
  have hcancel : (∑ k ∈ Finset.range (n + 1), f k) = -(∑ k ∈ Finset.range (n + 1), f k) :=
    calc
      _ = ∑ k ∈ Finset.range (n + 1), f (n - k) := by
        simpa only [Nat.add_sub_cancel] using (Finset.sum_range_reflect f (n + 1)).symm
      _ = ∑ k ∈ Finset.range (n + 1), -f k := by
        refine Finset.sum_congr rfl fun k hk => hpair k ?_
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      _ = _ := Finset.sum_neg_distrib f
  omega

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
