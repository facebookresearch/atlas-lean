/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
import MathlibExt.Combinatorics.Words.FibonacciFactorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Interval
import all Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD

/-!
# Endpoints of upper Wythoff unsum gap words

The finite Fibonacci word splits into its two preceding words. Splitting both summands
at these boundaries lets us recognize sums of two distinct upper Wythoff numbers in
a bounded window. We use this to determine the gaps adjacent to every marker.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Unsums of upper Wythoff numbers.** A positive integer $p$ is an *upper Wythoff number* when
the letter at index $p - 1$ (indices start at $0$) of the infinite Fibonacci word
$0100101001001\ldots$ is $1$; that is, the upper Wythoff numbers are the positions of the letter
$1$ in the Fibonacci word counted from one. A positive integer $x$ is an *unsum* (OEIS A260317)
if there are no upper Wythoff numbers $p < q$ with $p + q = x$.

The source writes the Fibonacci word over the letters $a$ and $b$; its letter $b$ is the letter
$1$ here.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2, defining unsums as the members of OEIS A260317. -/
public def IsUpperWythoffUnsum (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    fibInf (p - 1) = true ∧ fibInf (q - 1) = true

/-- Being an unsum is decidable; the instance is classical (noncomputable). The structural
instance would evaluate `fibInf (q - 1)`, which builds the Fibonacci-word iterate
`fibWord (q + 1)` of Fibonacci-number length, so `decide` would exhaust memory at modest
inputs. Small values are decided through a fixed prefix of the Fibonacci word instead (see
`upperWythoff_small` and `isUpperWythoffUnsum_small`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable instance instDecidablePredNatIsUpperWythoffUnsum :
    DecidablePred IsUpperWythoffUnsum := Classical.decPred _

namespace upperWythoffUnsumPalindrome_head_getLast

private theorem fibInf_eq_fibWord_seven {k : ℕ} (hk : k < 34) :
    fibInf k = (fibWord 7).getD k false := by
  have : (fibWord 7).length = 34 := by decide
  exact (fibInf_agrees 7 k (by omega)).symm

private def unsumCheck (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    (fibWord 7).getD (p - 1) false = true ∧ (fibWord 7).getD (q - 1) false = true

private instance decidableUnsumCheck : DecidablePred unsumCheck := fun x => by
  unfold unsumCheck; infer_instance

private theorem isUpperWythoffUnsum_iff_check {x : ℕ} (hx : x ≤ 34) :
    IsUpperWythoffUnsum x ↔ unsumCheck x := by
  unfold IsUpperWythoffUnsum unsumCheck
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [fibInf_eq_fibWord_seven (by omega)]
    · rwa [fibInf_eq_fibWord_seven (by omega)]
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [← fibInf_eq_fibWord_seven (by omega)]
    · rwa [← fibInf_eq_fibWord_seven (by omega)]

end upperWythoffUnsumPalindrome_head_getLast

open upperWythoffUnsumPalindrome_head_getLast

/-- **The upper Wythoff numbers below 30.** The positive integers $p < 30$ such that the letter at
index $p - 1$ (indices start at $0$) of the infinite Fibonacci word is $1$, that is, the upper
Wythoff numbers below $30$, are exactly $2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoff_small :
    (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      {2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28} := by
  have : (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      (Finset.range 30).filter (fun p => 0 < p ∧ (fibWord 7).getD (p - 1) false = true) := by
    refine Finset.filter_congr fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [fibInf_eq_fibWord_seven (by omega)]
  rw [this]
  decide +kernel

private theorem upperWythoffUnsumPalindrome_head_getLast.count_unsum_eq
    {n : ℕ} (hn : n ≤ 34) :
    Nat.count IsUpperWythoffUnsum n = Nat.count unsumCheck n := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [Finset.mem_range] at hx
  exact isUpperWythoffUnsum_iff_check (by omega)

/-- **The unsums up to 21.** The unsums (OEIS A260317) that are at most $21$ are exactly
$1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem isUpperWythoffUnsum_small :
    (Finset.range 22).filter IsUpperWythoffUnsum =
      {1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21} := by
  have : (Finset.range 22).filter IsUpperWythoffUnsum = (Finset.range 22).filter unsumCheck := by
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    exact isUpperWythoffUnsum_iff_check (by omega)
  rw [this]
  decide +kernel

/-- **Gaps between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums (OEIS A260317): the
positive integers that are not a sum $p + q$ of upper Wythoff numbers $p < q$. For $i \ge 0$,
the $i$-th gap between consecutive unsums (counted from zero) is $a_{i+2} - a_{i+1}$; this
is OEIS A260311 shifted by one.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumGap (i : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsum (i + 1) - Nat.nth IsUpperWythoffUnsum i

private theorem upperWythoffUnsumPalindrome_head_getLast.nth_unsum
    {i n : ℕ} (hn : n ≤ 34) (h : unsumCheck n)
    (hc : Nat.count unsumCheck n = i) : Nat.nth IsUpperWythoffUnsum i = n := by
  rw [← hc, ← count_unsum_eq hn]
  exact Nat.nth_count ((isUpperWythoffUnsum_iff_check hn).mpr h)

/-- **The first thirteen gaps between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums
(OEIS A260317) and let $g_i = a_{i+2} - a_{i+1}$ for $i \ge 0$. Then the gaps
$g_0, g_1, \dots, g_{12}$ are $1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumGap_small :
    (List.range 13).map upperWythoffUnsumGap = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2] := by
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, upperWythoffUnsumGap]
  rw [nth_unsum (i := 0) (n := 1) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 1) (n := 2) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 2) (n := 3) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 3) (n := 4) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 4) (n := 5) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 5) (n := 6) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 6) (n := 8) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 7) (n := 10) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 8) (n := 11) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 9) (n := 13) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 10) (n := 14) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 11) (n := 16) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 12) (n := 19) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 13) (n := 21) (by omega) (by decide +kernel) (by decide +kernel)]

/-- **Markers among the unsum gaps.** A natural number $i$ is a *marker* if $i \ge 10$ and the
$i$-th gap between consecutive unsums of upper Wythoff numbers (counted from zero) equals $2$.

The source marks the entries $2$ of A260311 that follow the irregular prefix $1111122121$ of
length ten.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public def IsUpperWythoffUnsumMarker (i : ℕ) : Prop :=
  10 ≤ i ∧ upperWythoffUnsumGap i = 2

/-- **Markers in the gaps between unsums.** Call a gap index $i$ a marker if $i \ge 10$ and the
$i$-th gap between consecutive unsums (counted from zero) equals $2$. For $j \ge 0$, the
$j$-th marker is the $j$-th marker in increasing order, counted from zero, so the $0$-th
marker is the smallest one.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumMarker (j : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsumMarker j

/-- **Words between markers in the unsum gap sequence.** Let $g_0, g_1, g_2, \ldots$ be the
gaps between consecutive unsums, and call an index $i \ge 10$ with $g_i = 2$ a marker. Let
$m_0 < m_1 < m_2 < \cdots$ be the markers in increasing order. For each $j$, the $j$-th word
between markers is $g_{m_j + 1} g_{m_j + 2} \cdots g_{m_{j+1} - 1}$, the word of the gaps
strictly between the $j$-th and the $(j+1)$-th marker.

The source writes the gap sequence after its prefix as $2 W_1 2 W_1 2 W_2 2 W_2 2 W_3 2 \cdots$,
so these words are $W_1, W_1, W_2, W_2, \ldots$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumWord (j : ℕ) : List ℕ :=
  (List.range' (upperWythoffUnsumMarker j + 1)
    (upperWythoffUnsumMarker (j + 1) - upperWythoffUnsumMarker j - 1)).map upperWythoffUnsumGap

/-- **The words $W_i$ of the unsum gap sequence.** For $i \ge 1$, the word $W_i$ is the word of
gaps strictly between the $(2i-2)$-th and $(2i-1)$-th markers of the unsum gap sequence, with
markers counted from zero; for $i = 0$ the definition gives the same word as for $i = 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumPalindrome (i : ℕ) : List ℕ :=
  upperWythoffUnsumWord (2 * i - 2)

private theorem upperWythoffUnsumPalindrome_head_getLast.gap_eq
    (i : ℕ) (h : i < 13) :
    upperWythoffUnsumGap i = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2].getD i 0 := by
  rw [← upperWythoffUnsumGap_small]
  simp [h]

/-- **The first two markers.** Call a gap index $i$ a marker if $i \ge 10$ and the $i$-th gap
between consecutive unsums (counted from zero) equals $2$. The smallest marker is $10$ and
the second smallest is $12$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumMarker_zero_one :
    upperWythoffUnsumMarker 0 = 10 ∧ upperWythoffUnsumMarker 1 = 12 := by
  have h10 : IsUpperWythoffUnsumMarker 10 := ⟨le_rfl, gap_eq 10 (by omega)⟩
  have h0 : upperWythoffUnsumMarker 0 = 10 := by
    unfold upperWythoffUnsumMarker
    rw [Nat.nth_zero]
    exact le_antisymm (Nat.sInf_le h10) (le_csInf ⟨10, h10⟩ fun i hi => hi.1)
  refine ⟨h0, ?_⟩
  have h12 : IsUpperWythoffUnsumMarker 12 := ⟨by omega, gap_eq 12 (by omega)⟩
  have h11 : ¬ IsUpperWythoffUnsumMarker 11 := fun h => by
    have := h.2
    rw [gap_eq 11 (by omega)] at this
    simp at this
  unfold upperWythoffUnsumMarker at h0 ⊢
  rw [Nat.nth_eq_sInf]
  refine le_antisymm (Nat.sInf_le ⟨h12, fun k hk => ?_⟩) (le_csInf ⟨12, h12, fun k hk => ?_⟩ ?_)
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · rintro x ⟨hx, hlt⟩
    have := hlt 0 (by omega)
    rw [h0] at this
    by_contra hx12
    obtain rfl : x = 11 := by omega
    exact h11 hx

/-- **The first palindrome.** Let $g_k$ be the $k$-th gap between consecutive unsums
(OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the markers, the indices
$k \ge 10$ with $g_k = 2$, in increasing order. The word $W_1$ of the gaps $g_k$ with
$m_0 < k < m_1$, in increasing order of $k$, consists of the single digit $3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumPalindrome_one : upperWythoffUnsumPalindrome 1 = [3] := by
  obtain ⟨h0, h1⟩ := upperWythoffUnsumMarker_zero_one
  simp only [upperWythoffUnsumPalindrome, upperWythoffUnsumWord, Nat.reduceMul, Nat.sub_self,
    zero_add, h0, h1]
  simp [gap_eq 11 (by omega)]

end

namespace upperWythoffUnsumPalindrome_head_getLast

-- At level zero the long and short words have lengths 34 and 21. This leaves
-- room to inspect nine consecutive sums, including windows crossing a word boundary.
private def word (n : ℕ) (short : Bool) : List Bool :=
  if short then fibWord (n + 6) else fibWord (n + 7)

private def width (n : ℕ) (short : Bool) : ℕ := (word n short).length

private theorem splitWord (n : ℕ) :
    word (n + 1) false = word n false ++ word n true :=
  fibWord_add_two (n + 6)

private theorem widths (n : ℕ) :
    width (n + 1) false = width n false + width n true ∧ width (n + 1) true = width n false := by
  exact ⟨by simp [width, splitWord], rfl⟩

private theorem widthBounds (n : ℕ) :
    9 ≤ width n true ∧ width n true + 9 ≤ width n false := by
  induction n with
  | zero => decide
  | succ n ih => obtain ⟨h, h'⟩ := widths n; omega

private def offset (n : ℕ) (bit : Bool) : ℕ := if bit then width n false else 0

private def hit (n : ℕ) (s : Bool) (a : ℕ) : Prop :=
  a < width n s ∧ (word n s).getD a false = true

private theorem splitHit (n : ℕ) (s : Bool) (a : ℕ) :
    hit (n + 1) s a ↔ ∃ b : Bool, (s && b) = false ∧
      ∃ i, hit n b i ∧ a = offset n b + i := by
  cases s
  · simp only [Bool.false_and, true_and, Bool.exists_bool, offset, Bool.false_eq_true,
      ite_false, zero_add, exists_eq_right', ite_true]
    unfold hit
    rw [(widths n).1, splitWord]
    by_cases h : a < width n false
    · rw [List.getD_append _ _ _ _ h]
      constructor
      · exact fun ⟨_, ha⟩ => Or.inl ⟨h, ha⟩
      · rintro (⟨_, ha⟩ | ⟨i, _, he⟩)
        · exact ⟨by omega, ha⟩
        · omega
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
      change (_ ∧ (word n true).getD (a - width n false) false = true) ↔ _
      constructor
      · rintro ⟨ha, hbit⟩
        exact Or.inr ⟨a - width n false, ⟨by omega, hbit⟩, by omega⟩
      · rintro (⟨hlt, _⟩ | ⟨i, ⟨hi, hbit⟩, rfl⟩)
        · omega
        · simpa using And.intro (by omega : width n false + i < width n false + width n true) hbit
  · simp [offset, hit, width, word]

-- The remaining two summands lie in suffix words of the indicated sizes.
-- When their prefixes coincide, the suffix positions must still be distinct.
-- The residual target is translated by c times the long width plus d times the short width.
private structure Piece where
  left : Bool
  right : Bool
  distinct : Bool
  c : ℤ
  d : ℤ
  deriving DecidableEq, Ord

private def realizes (n : ℕ) (p : Piece) (z : ℤ) : Prop :=
  ∃ a b : ℕ, hit n p.left a ∧ hit n p.right b ∧ (p.distinct = true → a ≠ b) ∧
    (a : ℤ) + b = z + p.c * width n false + p.d * width n true

-- Selecting right-hand blocks translates positions by the old short width, which
-- is the new long width. The old long width is the sum of the two new widths.
private def child (p : Piece) (x a b : Bool) : Piece where
  left := a
  right := b
  distinct := p.distinct && (a == b)
  c := p.c + p.d + x.toNat - a.toNat - b.toNat
  d := p.c

private theorem offset_cast (n : ℕ) (b : Bool) :
    (offset n b : ℤ) = (b.toNat : ℤ) * width n false := by cases b <;> simp [offset]

private theorem distinct_iff {n i j : ℕ} {a b : Bool} (e : Bool)
    (hi : hit n a i) (hj : hit n b j) :
    (e = true → offset n a + i ≠ offset n b + j) ↔
      ((e && (a == b)) = true → i ≠ j) := by
  obtain ⟨hi, _⟩ := hi
  obtain ⟨hj, _⟩ := hj
  cases e <;> cases a <;> cases b <;> simp [offset] <;> omega

private theorem splitRealizes (n : ℕ) (p : Piece) (x : Bool) (z : ℤ) :
    realizes (n + 1) p (offset n x + z) ↔ ∃ a b : Bool,
      (p.left && a) = false ∧ (p.right && b) = false ∧ realizes n (child p x a b) z := by
  have eqn (a b : Bool) (i j : ℕ) :
      ((offset n a + i : ℕ) : ℤ) + (offset n b + j : ℕ) =
        offset n x + z + p.c * width (n + 1) false + p.d * width (n + 1) true ↔
      (i : ℤ) + j = z + (child p x a b).c * width n false + (child p x a b).d * width n true := by
    simp only [(widths n).1, (widths n).2, Nat.cast_add, offset_cast, child]
    ring_nf
    omega
  constructor
  · rintro ⟨i', j', hi, hj, hd, he⟩
    obtain ⟨a, ha, i, hi', rfl⟩ := (splitHit ..).mp hi
    obtain ⟨b, hb, j, hj', rfl⟩ := (splitHit ..).mp hj
    exact ⟨a, b, ha, hb, i, j, hi', hj', (distinct_iff _ hi' hj').mp hd, (eqn ..).mp he⟩
  · rintro ⟨a, b, ha, hb, i, j, hi, hj, hd, he⟩
    exact ⟨_, _, (splitHit ..).mpr ⟨_, ha, _, hi, rfl⟩, (splitHit ..).mpr ⟨_, hb, _, hj, rfl⟩,
      (distinct_iff _ hi hj).mpr hd, (eqn ..).mpr he⟩

-- Write the translation as (c + d) * short + c * (long - short).
-- Discard a piece if even the extreme sums miss the whole window.
private def dead (p : Piece) : Bool := decide
  (2 ≤ p.c ∧ 2 ≤ p.c + p.d ∨
   p.c ≤ -1 ∧ p.c + p.d ≤ -1 ∧ (p.c ≤ -2 ∨ p.c + p.d ≤ -2))

private theorem dead_spec {n : ℕ} {p : Piece} {z : ℤ}
    (hz : 0 ≤ z) (hz' : z < (width n false : ℤ) + 8) (hp : realizes n p z) : dead p = false := by
  obtain ⟨a, b, ⟨ha, _⟩, ⟨hb, _⟩, _, eq⟩ := hp
  have bounds := widthBounds n
  have leWidth (s : Bool) : width n s ≤ width n false := by cases s <;> omega
  have ha' := ha.trans_le (leWidth _)
  have hb' := hb.trans_le (leWidth _)
  have hs : (9 : ℤ) ≤ width n true := by omega
  have hd : (9 : ℤ) ≤ (width n false : ℤ) - width n true := by omega
  have hd0 : 0 ≤ (width n false : ℤ) - width n true := by omega
  suffices ¬ (2 ≤ p.c ∧ 2 ≤ p.c + p.d ∨ _) by simpa only [dead, decide_eq_false_iff_not]
  rintro (⟨hc, hcd⟩ | ⟨hc, hcd, hh⟩)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc) hd0,
      mul_nonneg (sub_nonneg.mpr hcd) (Int.natCast_nonneg (width n true))]
  · rcases hh with hc' | hcd'
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc') hd0,
        mul_nonneg (sub_nonneg.mpr hcd) (Int.natCast_nonneg (width n true))]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc) hd0,
        mul_nonneg (sub_nonneg.mpr hcd') (Int.natCast_nonneg (width n true))]

private def digits (short : Bool) : List Bool := if short then [false] else [false, true]

private theorem mem_digits (a s : Bool) : a ∈ digits s ↔ (s && a) = false := by
  cases a <;> cases s <;> decide

private def children (p : Piece) (x : Bool) : List Piece :=
  (((digits p.left).flatMap fun a => (digits p.right).map (child p x a)).filter fun q => !dead q)

private theorem child_spec {n : ℕ} {p : Piece} {x : Bool} {z : ℤ}
    (hz : 0 ≤ z) (hz' : z < (width n false : ℤ) + 8) :
    realizes (n + 1) p (offset n x + z) ↔ ∃ q ∈ children p x, realizes n q z := by
  rw [splitRealizes]
  simp only [children, List.mem_filter, List.mem_flatMap, List.mem_map, mem_digits,
    Bool.not_eq_true']
  constructor
  · rintro ⟨a, b, ha, hb, hr⟩
    exact ⟨_, ⟨⟨a, ha, b, hb, rfl⟩, dead_spec hz hz' hr⟩, hr⟩
  · rintro ⟨_, ⟨⟨a, ha, b, hb, rfl⟩, _⟩, hr⟩
    exact ⟨a, b, ha, hb, hr⟩

-- The two flags distinguish the first block (the irregular prefix) and the last
-- block (where a pair of unsums witnesses unboundedness).
private structure Frame where
  short : Bool
  initial : Bool
  finalBlock : Bool
  pieces : List Piece
  deriving DecidableEq

private def root : Frame := ⟨false, true, true, [⟨false, false, true, 0, 0⟩]⟩

private def advance (f : Frame) (x : Bool) : Frame where
  short := x
  initial := f.initial && !x
  finalBlock := f.finalBlock && (f.short != x)
  pieces := (f.pieces.flatMap (children · x)).eraseDups.insertionSort fun p q => (compare p q).isLE

private def missing (n : ℕ) (f : Frame) (z : ℕ) : Prop :=
  ¬ ∃ p ∈ f.pieces, realizes n p z

private theorem missing_advance (n : ℕ) (f : Frame) (x : Bool) {z : ℕ}
    (hz : z < width n false + 8) :
    missing (n + 1) f (offset n x + z) ↔ missing n (advance f x) z := by
  simp only [missing, advance, Nat.cast_add,
    child_spec (show (0 : ℤ) ≤ z by omega) (show (z : ℤ) < width n false + 8 by omega),
    List.mem_insertionSort, List.mem_eraseDups, List.mem_flatMap]
  grind

-- Offsets refer to zero-based positions of the summands. A missing sum at offset 3
-- therefore means that the original positive integer z + 5 is an unsum.
private def markerAt (u : ℕ → Prop) (z : ℕ) : Prop :=
  u (z + 3) ∧ ¬ u (z + 4) ∧ u (z + 5)

private def localPattern (f : Frame) (u : ℕ → Prop) (z : ℕ) : Prop :=
  ((f.initial = false ∨ 9 ≤ z) → markerAt u z →
    (¬ u (z + 6) ∧ ¬ u (z + 7) ∧ u (z + 8)) ∧
    ((f.initial = false ∨ 9 < z) → u z ∧ ¬ u (z + 1) ∧ ¬ u (z + 2)))

private def positions (s : Bool) : Finset ℕ :=
  (Finset.range (width 0 s)).filter fun i => (word 0 s).getD i false = true

private def smallSums (a b e : Bool) : Finset ℤ :=
  ((positions a ×ˢ positions b).filter fun ij => e = true → ij.1 ≠ ij.2).image
    fun ij => (ij.1 : ℤ) + ij.2

-- Bit k records whether two allowed positions in the base words have sum k.
-- The finite set equality below checks these masks directly against the words.
private def sumMask : Bool → Bool → Bool → ℕ
  | false, false, false => 0x496d6f6f6b7b5b5a4
  | false, false, true => 0x9696f6b6b6b5a4a0
  | false, true, false => 0x16f6f6b7b5b5a4
  | false, true, true => 0x16f6b6b6b5a4a0
  | true, false, false => 0x16f6f6b7b5b5a4
  | true, false, true => 0x16f6b6b6b5a4a0
  | true, true, false => 0x56b7b5b5a4
  | true, true, true => 0x12b6b5a4a0

private def containsSum (a b e : Bool) (k : ℤ) : Bool :=
  decide (0 ≤ k ∧ k < 67) && (sumMask a b e).testBit k.toNat

private theorem masks_correct : ∀ a b e : Bool,
    (Finset.Ico (0 : ℤ) 67).filter (fun k => (sumMask a b e).testBit k.toNat) =
      smallSums a b e := by decide +kernel

private theorem containsSum_iff (a b e : Bool) (k : ℤ) :
    containsSum a b e k ↔ k ∈ smallSums a b e := by
  rw [← masks_correct]
  simp [containsSum]

private def baseMissing (f : Frame) (z : ℕ) : Bool :=
  !f.pieces.any fun p => containsSum p.left p.right p.distinct (z + p.c * 34 + p.d * 21)

private theorem baseMissing_spec (f : Frame) (z : ℕ) :
    baseMissing f z = true ↔ missing 0 f z := by
  have h₀ : width 0 false = 34 := by decide
  have h₁ : width 0 true = 21 := by decide
  have spec (p : Piece) : (z : ℤ) + p.c * 34 + p.d * 21 ∈ smallSums p.left p.right p.distinct ↔
      realizes 0 p z := by
    simp only [realizes, h₀, h₁, smallSums, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, positions, Finset.mem_range, hit, Prod.exists, Nat.cast_ofNat]
    tauto
  simp only [baseMissing, Bool.not_eq_true', ← Bool.not_eq_true,
    List.any_eq_true, containsSum_iff, spec, missing]

-- Starting at the root, visit frames in breadth-first order, taking left children
-- before right children and identifying repeated frames. Each row gives the frame
-- and its two child indices (the right index is unused for a short word).
-- The low three bits record the flags; subsequent bits select pieces in
-- lexicographic order. Only coefficients -1, 0, 1 occur. Checking each transition
-- against the unrestricted subdivision proves that the table is closed.
private def alphabet : List Piece := do
  let l ← [false, true]
  let r ← [false, true]
  let e ← [false, true]
  let c ← [-1, 0, 1]
  let d ← [-1, 0, 1]
  return ⟨l, r, e, c, d⟩

private def selectPieces : List Piece → ℕ → List Piece
  | [], _ => []
  | p :: ps, k =>
    let tail := selectPieces ps (k / 2)
    if k % 2 = 1 then p :: tail else tail

private def decodeFrame (k : ℕ) : Frame :=
  ⟨k.testBit 0, k.testBit 1, k.testBit 2, selectPieces alphabet (k / 8)⟩

private abbrev RowIndex := Fin 75

private def rows : Array (ℕ × RowIndex × RowIndex) :=
  #[(0x10006, 1, 2), (0x10000410002, 1, 3), (0x80000080002080005, 4, 0),
    (0x80000080002080041, 5, 0), (0x100000110004500084, 6, 7), (0x100000110004500090, 6, 8),
    (0x800000890022408480, 9, 10), (0x4000400480012040445, 11, 0), (0x4000400480012040441, 12, 0),
    (0x800910024482880, 13, 14), (0x4400890022410441, 15, 0), (0x800130004c20894, 16, 17),
    (0x800130004c20890, 16, 18), (0x1040009900265004c0, 19, 20), (0x820400c80032008641, 21, 0),
    (0x800910024410c90, 22, 23), (0x840008900224804c0, 24, 25), (0x4204004c0013000645, 26, 0),
    (0x4204004c0013000641, 27, 0), (0x800800990026408c90, 28, 29), (0x4004400c900324404c1, 30, 0),
    (0x800930024c82990, 31, 32), (0x4800990026410cc0, 33, 34), (0xa4400c80032080641, 35, 0),
    (0x100800910024500c90, 36, 37), (0x8044008900224084c1, 38, 0), (0x800130004c10994, 39, 40),
    (0x800130004c10990, 39, 41), (0x4800990026482cc0, 42, 43), (0x24400c90032410641, 44, 0),
    (0x800930024c20c90, 45, 46), (0x1044009900265004c0, 19, 20), (0x822400cc0033008641, 21, 0),
    (0x4800990026410cd0, 33, 34), (0xa4400c900324806c1, 35, 0), (0x100800930024d00d90, 47, 48),
    (0x804800990026408cc0, 49, 50), (0x4024400c80032040641, 51, 0), (0x800910024482c90, 52, 53),
    (0x44008900224104c0, 15, 54), (0xa24004c0013080645, 55, 0), (0xa24004c0013080641, 56, 0),
    (0x104800990026500cd0, 57, 58), (0x824400c900324086c1, 59, 0), (0x800930024c10d90, 60, 61),
    (0x84800990026480cc0, 42, 43), (0x424400cc0033000641, 44, 0), (0x804c00990026408cc0, 49, 50),
    (0x4026400cc0033040641, 51, 0), (0x4800990026482cd0, 42, 43), (0x24400c900324106c1, 44, 0),
    (0x800930024c20d90, 62, 63), (0x104800990026500cc0, 57, 58), (0x824400c80032008641, 59, 0),
    (0x844008900224804c1, 24, 0), (0x100800130004d00994, 64, 65), (0x100800130004d00990, 64, 66),
    (0x804800990026408cd0, 49, 50), (0x4024400c900324406c1, 51, 0), (0x800930024c82d90, 67, 68),
    (0x4c00990026410cc0, 33, 34), (0xa6400cc0033080641, 35, 0), (0x84c00990026480cc0, 42, 43),
    (0x426400cc0033000641, 44, 0), (0x8044008900224084c0, 38, 69), (0x40224004c0013040645, 70, 0),
    (0x40224004c0013040641, 71, 0), (0x104c00990026500cc0, 57, 58), (0x826400cc0033008641, 59, 0),
    (0x44008900224104c1, 15, 0), (0x800130004c20994, 72, 73), (0x800130004c20990, 72, 74),
    (0x844008900224804c0, 24, 25), (0x4224004c0013000645, 26, 0), (0x4224004c0013000641, 27, 0)]

private def frame (i : RowIndex) : Frame := decodeFrame rows[i.val]!.1

private def nextRow (i : RowIndex) (x : Bool) : RowIndex :=
  if x then rows[i.val]!.2.2 else rows[i.val]!.2.1

private def Known (f : Frame) : Prop := ∃ i, frame i = f

private theorem root_mem : Known root := ⟨0, by decide +kernel⟩

private theorem transitions : ∀ (i : RowIndex) (x : Bool), ((frame i).short && x) = false →
    advance (frame i) x = frame (nextRow i x) := by decide +kernel

private theorem closed (f : Frame) (hf : Known f) (x : Bool) (hx : (f.short && x) = false) :
    Known (advance f x) := by
  obtain ⟨i, rfl⟩ := hf
  exact ⟨nextRow i x, (transitions i x hx).symm⟩

private def checkBase (f : Frame) : Bool :=
  (List.range (width 0 f.short)).all fun z =>
    let u := baseMissing f
    let mark := u (z + 3) && !u (z + 4) && u (z + 5)
    (!( (!f.initial || decide (9 ≤ z)) && mark) ||
      (!u (z + 6) && !u (z + 7) && u (z + 8) &&
       (!(!f.initial || decide (9 < z)) || (u z && !u (z + 1) && !u (z + 2))))) &&
    (!(f.finalBlock && decide (z + 7 = width 0 f.short)) || mark)

private theorem checked : ∀ i : RowIndex, checkBase (frame i) = true := by decide +kernel

private theorem baseCase (f : Frame) (hf : Known f) {z : ℕ} (hz : z < width 0 f.short) :
    localPattern f (missing 0 f) z ∧
    (f.finalBlock = true → z + 7 = width 0 f.short → markerAt (missing 0 f) z) := by
  obtain ⟨i, rfl⟩ := hf
  have h := List.all_eq_true.mp (checked i) z (List.mem_range.mpr hz)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq,
    ← Bool.not_eq_true, baseMissing_spec] at h
  unfold localPattern markerAt
  grind [baseMissing_spec]

private theorem subdivide (n : ℕ) (s : Bool) {z : ℕ} (hz : z < width (n + 1) s) :
    ∃ x : Bool, (s && x) = false ∧ ∃ i < width n x, z = offset n x + i := by
  cases s
  · rw [(widths n).1] at hz
    by_cases h : z < width n false
    · exact ⟨false, rfl, z, h, by simp [offset]⟩
    · exact ⟨true, rfl, z - width n false, by omega, by simp [offset]; omega⟩
  · exact ⟨false, rfl, z, hz, by simp [offset]⟩

private theorem allLevels (n : ℕ) (f : Frame) (hf : Known f) {z : ℕ} (hz : z < width n f.short) :
    localPattern f (missing n f) z ∧
    (f.finalBlock = true → z + 7 = width n f.short → markerAt (missing n f) z) := by
  induction n generalizing f z with
  | zero => exact baseCase f hf hz
  | succ n ih =>
    obtain ⟨x, hx, i, hi, rfl⟩ := subdivide n f.short hz
    let g := advance f x
    obtain ⟨hp, he⟩ := ih g (closed f hf x hx) hi
    have bounds := widthBounds n
    have hi' : i < width n false := by cases x <;> omega
    have trans (k : ℕ) (hk : k ≤ 8) :
        missing (n + 1) f (offset n x + i + k) ↔ missing n g (i + k) := by
      rw [Nat.add_assoc]
      exact missing_advance n f x (by omega)
    have init (k : ℕ) (h : f.initial = false ∨ k ≤ offset n x + i) :
        g.initial = false ∨ k ≤ i := by
      cases x <;> simp_all [offset, g, advance]
    have endBlock (h : f.finalBlock = true) (heq : offset n x + i + 7 = width (n + 1) f.short) :
        g.finalBlock = true ∧ i + 7 = width n x := by
      cases hs : f.short <;> cases x <;>
        simp_all [offset, g, advance, (widths n).1, (widths n).2] <;> omega
    have h₀ := trans 0 (by decide)
    simp only [Nat.add_zero] at h₀
    unfold localPattern markerAt at *
    simp (disch := decide) only [trans, h₀]
    constructor
    · intro h hm
      obtain ⟨hn, hb⟩ := hp (init 9 h) hm
      exact ⟨hn, fun h' => hb (init 10 h')⟩
    · intro h h'
      obtain ⟨ha, hb⟩ := endBlock h h'
      exact he ha hb

private theorem missing_root (n z : ℕ) (h : z < width n false) :
    missing n root z ↔ IsUpperWythoffUnsum (z + 2) := by
  have hit_iff {a : ℕ} : hit n false a ↔ a < width n false ∧ fibInf a = true := by
    unfold hit
    constructor <;> rintro ⟨ha, hbit⟩ <;> refine ⟨ha, ?_⟩
    · rwa [← fibInf_agrees (n + 7) a ha]
    · exact (fibInf_agrees (n + 7) a ha).trans hbit
  simp only [missing, root, List.mem_singleton, exists_eq_left, realizes, hit_iff, true_implies,
    zero_mul, add_zero, IsUpperWythoffUnsum]
  constructor
  · intro hn
    refine ⟨by omega, ?_⟩
    rintro ⟨p, hp, q, hq, hp₀, hpq, he, h₁, h₂⟩
    exact hn ⟨p - 1, q - 1, ⟨by omega, h₁⟩, ⟨by omega, h₂⟩, by omega, by omega⟩
  · rintro ⟨_, hn⟩ ⟨a, b, ⟨_, ha⟩, ⟨_, hb⟩, hd, he⟩
    rcases lt_or_gt_of_ne hd with hlt | hgt
    · exact hn ⟨a + 1, by omega, b + 1, by omega, by omega, by omega, by omega, ha, hb⟩
    · exact hn ⟨b + 1, by omega, a + 1, by omega, by omega, by omega, by omega, hb, ha⟩

private theorem localUnsums {m : ℕ} (hm : 14 ≤ m) (h₀ : IsUpperWythoffUnsum m)
    (h₁ : ¬ IsUpperWythoffUnsum (m + 1)) (h₂ : IsUpperWythoffUnsum (m + 2)) :
    (¬ IsUpperWythoffUnsum (m + 3) ∧ ¬ IsUpperWythoffUnsum (m + 4) ∧
      IsUpperWythoffUnsum (m + 5)) ∧
    (14 < m → IsUpperWythoffUnsum (m - 3) ∧ ¬ IsUpperWythoffUnsum (m - 2) ∧
      ¬ IsUpperWythoffUnsum (m - 1)) := by
  let z := m - 5
  have hw : m + 6 < width m false := by
    have := fibWord_length (m + 7)
    change _ < (fibWord (m + 7)).length
    omega
  have ⟨h, _⟩ := allLevels m root root_mem (z := z) (by change z < width m false; dsimp [z]; omega)
  unfold localPattern markerAt at h
  have bridge (j : ℕ) (hj : j ≤ 8) :
      missing m root (z + j) ↔ IsUpperWythoffUnsum (z + j + 2) :=
    missing_root _ _ (by dsimp [z]; omega)
  have h' := bridge 0 (by decide)
  simp only [Nat.add_zero] at h'
  simp (disch := decide) only [bridge, h'] at h
  simp only [show root.initial = true from rfl, Bool.true_eq_false, false_or] at h
  dsimp [z] at h
  grind

-- The two unsums at the right edge of every sufficiently long Fibonacci word
-- give markers of unbounded size.
private theorem unboundedPairs (B : ℕ) :
    ∃ m, B < m ∧ IsUpperWythoffUnsum m ∧ ¬ IsUpperWythoffUnsum (m + 1) ∧
      IsUpperWythoffUnsum (m + 2) := by
  let w := width B false
  have hw : B + 7 < w := fibWord_length (B + 7)
  let z := w - 7
  have hz : z + 7 = w := by dsimp [z]; omega
  have he := (allLevels B root root_mem (z := z) (by change z < w; omega)).2 rfl hz
  unfold markerAt at he
  have bridge (j : ℕ) (hj : j ≤ 5) :
      missing B root (z + j) ↔ IsUpperWythoffUnsum (z + j + 2) :=
    missing_root _ _ (by change z + j < w; omega)
  simp (disch := decide) only [bridge] at he
  exact ⟨z + 5, by omega, he.1, he.2.1, he.2.2⟩

private theorem infiniteUnsums : (Set.ofPred IsUpperWythoffUnsum).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  obtain ⟨m, hm, h, _⟩ := unboundedPairs b
  exact ⟨m, h, hm⟩

private noncomputable abbrev unsum := Nat.nth IsUpperWythoffUnsum

private noncomputable abbrev rank := Nat.count IsUpperWythoffUnsum

private theorem rank_two {m : ℕ} (h : IsUpperWythoffUnsum m) (h' : ¬ IsUpperWythoffUnsum (m + 1)) :
    rank (m + 2) = rank m + 1 := by
  rw [show m + 2 = (m + 1) + 1 by omega]
  simp [rank, Nat.count_succ, h, h']

private theorem rank_three {m : ℕ} (h : IsUpperWythoffUnsum m)
    (h' : ¬ IsUpperWythoffUnsum (m + 1)) (h'' : ¬ IsUpperWythoffUnsum (m + 2)) :
    rank (m + 3) = rank m + 1 := by
  rw [show m + 3 = (m + 2) + 1 by omega, rank, Nat.count_succ, ite_eq_right h'', Nat.add_zero]
  exact rank_two h h'

private theorem gap_at_pair {m : ℕ} (h₀ : IsUpperWythoffUnsum m)
    (h₁ : ¬ IsUpperWythoffUnsum (m + 1))
    (h₂ : IsUpperWythoffUnsum (m + 2)) : upperWythoffUnsumGap (rank m) = 2 := by
  rw [upperWythoffUnsumGap, ← rank_two h₀ h₁, Nat.nth_count h₂, Nat.nth_count h₀]
  omega

private theorem infiniteMarkers : (Set.ofPred IsUpperWythoffUnsumMarker).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  obtain ⟨m, hm, h₀, h₁, h₂⟩ := unboundedPairs (unsum (b + 10))
  have hlt : b + 10 < rank m := (Nat.nth_lt_nth infiniteUnsums).mp (by rwa [Nat.nth_count h₀])
  exact ⟨rank m, ⟨by omega, gap_at_pair h₀ h₁ h₂⟩, by omega⟩

private theorem neighbors {k : ℕ} (hk : IsUpperWythoffUnsumMarker k) :
    upperWythoffUnsumGap (k + 1) = 3 ∧ (10 < k → upperWythoffUnsumGap (k - 1) = 3) := by
  obtain ⟨hk₀, hk₂⟩ := hk
  let m := unsum k
  have h10 : unsum 10 = 14 := nth_unsum (by decide) (by decide +kernel) (by decide +kernel)
  have hmono := Nat.nth_strictMono infiniteUnsums
  have hm : 14 ≤ m := h10 ▸ hmono.monotone hk₀
  have h₀ : IsUpperWythoffUnsum m := Nat.nth_mem_of_infinite infiniteUnsums _
  have hlt := hmono (Nat.lt_succ_self k)
  change unsum (k + 1) - m = 2 at hk₂
  have hs : unsum (k + 1) = m + 2 := by omega
  have h₂ : IsUpperWythoffUnsum (m + 2) := hs ▸ Nat.nth_mem_of_infinite infiniteUnsums (k + 1)
  have h₁ : ¬ IsUpperWythoffUnsum (m + 1) := by
    intro h
    have := Nat.le_nth_of_lt_nth_succ (p := IsUpperWythoffUnsum) (k := k)
      (a := m + 1) (by change m + 1 < unsum (k + 1); omega) h
    change m + 1 ≤ m at this
    omega
  obtain ⟨⟨hn₁, hn₂, hn₃⟩, hp⟩ := localUnsums hm h₀ h₁ h₂
  have hr : rank m = k := Nat.count_nth_of_infinite infiniteUnsums k
  constructor
  · have h := rank_three (m := m + 2) h₂ hn₁ hn₂
    rw [rank_two h₀ h₁, hr] at h
    change unsum ((k + 1) + 1) - unsum (k + 1) = 3
    rw [← h, show unsum (rank (m + 2 + 3)) = m + 5 from Nat.nth_count hn₃, hs]
    omega
  · intro hk'
    have hm' : 14 < m := h10 ▸ hmono hk'
    obtain ⟨h₃, hp₂, hp₁⟩ := hp hm'
    let a := m - 3
    have ha : a + 3 = m := by dsimp [a]; omega
    have h := rank_three (m := a) h₃ (by rwa [show a + 1 = m - 2 by dsimp [a]; omega])
      (by rwa [show a + 2 = m - 1 by dsimp [a]; omega])
    rw [ha, hr] at h
    change unsum (k - 1 + 1) - unsum (k - 1) = 3
    rw [show k - 1 + 1 = k by omega, show k - 1 = rank a by omega,
      show unsum (rank a) = a from Nat.nth_count h₃]
    change m - (m - 3) = 3
    omega

private theorem endpoints (j : ℕ) :
    (upperWythoffUnsumWord j).head? = some 3 ∧ (upperWythoffUnsumWord j).getLast? = some 3 := by
  let a := upperWythoffUnsumMarker j
  let b := upperWythoffUnsumMarker (j + 1)
  have ha : IsUpperWythoffUnsumMarker a := Nat.nth_mem_of_infinite infiniteMarkers j
  have hb : IsUpperWythoffUnsumMarker b := Nat.nth_mem_of_infinite infiniteMarkers (j + 1)
  have hab : a < b := Nat.nth_strictMono infiniteMarkers (Nat.lt_succ_self j)
  have hfirst := (neighbors ha).1
  have hlast := (neighbors hb).2 (ha.1.trans_lt hab)
  have hsep : a + 1 < b := by
    obtain ⟨_, hg⟩ := hb
    by_contra! h
    rw [show b = a + 1 by omega, hfirst] at hg
    exact (by decide : (3 : ℕ) ≠ 2) hg
  change ((List.range' (a + 1) (b - a - 1)).map _).head? = _ ∧
    ((List.range' (a + 1) (b - a - 1)).map _).getLast? = _
  simp [List.head?_range', List.getLast?_range', show b - a - 1 ≠ 0 by omega, hfirst,
    show a + 1 + (b - a - 1) - 1 = b - 1 by omega, hlast]

end upperWythoffUnsumPalindrome_head_getLast

/-- **The palindromes begin and end with the digit 3.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ is nonempty, its first digit is $3$, and its last digit
is $3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 5 (`jis-2025-25.3.8-lem-5`). -/
public theorem upperWythoffUnsumPalindrome_head_getLast {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).head? = some 3 ∧
      (upperWythoffUnsumPalindrome i).getLast? = some 3 := by
  cases i with
  | zero => omega
  | succ i => exact upperWythoffUnsumPalindrome_head_getLast.endpoints _

end MetaMathlibExt
