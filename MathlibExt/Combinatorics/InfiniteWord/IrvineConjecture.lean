/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Nth
public import MathlibExt.Combinatorics.InfiniteWord.Gutkovskiy
public import MathlibExt.Combinatorics.InfiniteWord.KimberlingBlock
import Mathlib.Tactic.NormNum

/-! # Irvine's conjecture for Gutkovskiy's sequence

The successive differences of Gutkovskiy's sequence form Kimberling's word. We identify their
finite prefixes using the morphism `0 ↦ 11`, `1 ↦ 110`, then sum the differences. For `n ≥ 1`,
if `A_n` and `B_n` are the one-based positions of the `n`-th one and zero, respectively, then
`A_(B_n)` is either `A_n + B_n - 1` or `A_n + B_n`. The index zero is immediate from the
convention `A_0 = B_0 = 0`.

## References

* Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24 (2024),
  Article A51, pp. 1–17, Section 2 and Theorems 1 and 3. We use prefix counts instead of Walnut
  for Theorem 3; Section 8 gives the same auxiliary identity `B_n = 2 * A_n + n`.
* Robbert Fokkink, Gerard Francis Ortega, and Dan Rust, *Corner the empress*, in *Games of No
  Chance 6*, MSRI Publications 71 (2025), pp. 475–489, Sections 4 and 5. Table 4 gives the
  auxiliary identity, and Section 5 records the conjecture for the morphism `1 ↦ 110`, `0 ↦ 11`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Each Kimberling block is a prefix of the next.** Let $h$ be Kimberling's morphism on
$\{0, 1\}$, $h(1) = 110$ and $h(0) = 11$, and let $K_n = h^n(1)$. Then for every $n \ge 0$, the
word $K_n$ is a prefix of $K_{n+1}$.

Indeed $h(1) = 110$ begins with $1$, so $h^n(1)$ is a prefix of $h^n(110) = h^{n+1}(1)$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_prefix_succ (n : ℕ) :
    kimberlingBlock n <+: kimberlingBlock (n + 1) := by
  induction n with
  | zero => exact ⟨[true, false], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨morphExtend kimberlingMorphism t, ?_⟩
    change morphExtend kimberlingMorphism (kimberlingBlock n) ++ _ =
      morphExtend kimberlingMorphism (kimberlingBlock (n + 1))
    rw [← ht, morphExtend_append]

/-- **Kimberling's blocks form a prefix chain.** Let $h$ be Kimberling's morphism on $\{0, 1\}$,
$h(1) = 110$ and $h(0) = 11$, and let $K_n = h^n(1)$. Then $K_m$ is a prefix of $K_n$ for all
natural numbers $m \le n$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_prefix {m n : ℕ} (h : m ≤ n) :
    kimberlingBlock m <+: kimberlingBlock n := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (kimberlingBlock_prefix_succ _)

/-- **Lower bound on the length of the Kimberling blocks.** Let $h$ be Kimberling's morphism on
the alphabet $\{0, 1\}$, given by $h(1) = 110$ and $h(0) = 11$, and let $K_n = h^n(1)$. For every
natural number $n$, the word $K_n$ has length at least $2^n$.

This holds because the image of each letter under $h$ has length at least $2$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem two_pow_le_length_kimberlingBlock (n : ℕ) :
    2 ^ n ≤ (kimberlingBlock n).length := by
  have hext : ∀ w : List Bool, 2 * w.length ≤ (morphExtend kimberlingMorphism w).length := by
    intro w
    induction w with
    | nil => simp [morphExtend]
    | cons b w ih =>
      have e : morphExtend kimberlingMorphism (b :: w) =
          kimberlingMorphism b ++ morphExtend kimberlingMorphism w := rfl
      rw [e, List.length_append, List.length_cons]
      cases b <;> simp [kimberlingMorphism] <;> omega
  induction n with
  | zero => simp [kimberlingBlock, morphIterate]
  | succ n ih =>
    have := hext (kimberlingBlock n)
    change _ ≤ (morphExtend kimberlingMorphism (kimberlingBlock n)).length
    rw [pow_succ]
    omega

/-- **Kimberling's word.** Let $K_n$ be the $n$-th Kimberling block, a finite word over
$\{0, 1\}$. Kimberling's word $k = k_1 k_2 k_3 \cdots = 1101101111\cdots$ (OEIS A285431) is the
infinite word over $\{0, 1\}$ whose letter $k_{i+1}$, for $i \ge 0$, is the $(i+1)$-th letter of
$K_m$, where $m = \lfloor \log_2 i \rfloor + 1$ for $i \ge 1$ and $m = 1$ for $i = 0$. The block
$K_m$ has length at least $2^m > i$, so this letter exists.

Every block $K_n$ is a prefix of $k$, so $k$ is the common extension of the blocks.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2 (the limit word `k`) and Section 5 (`k'_n = k_{n+1}`). -/
public def kimberlingWord (i : ℕ) : Bool :=
  (kimberlingBlock (Nat.log 2 i + 1)).getD i false

/-- **Every Kimberling block is a prefix of Kimberling's word.** Let $k = k_1 k_2 k_3 \cdots$ be
Kimberling's word and $K_n$ the $n$-th Kimberling block. For all natural numbers $i$ and $n$ with
$i < |K_n|$, the letter $k_{i+1}$ equals the $(i+1)$-th letter of $K_n$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingWord_eq_getD {i n : ℕ} (hi : i < (kimberlingBlock n).length) :
    kimberlingWord i = (kimberlingBlock n).getD i false := by
  have hi' : i < (kimberlingBlock (Nat.log 2 i + 1)).length :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) i)
      (two_pow_le_length_kimberlingBlock _)
  unfold kimberlingWord
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hi, Option.getD_some]
  rcases le_total (Nat.log 2 i + 1) n with h | h
  · exact (kimberlingBlock_prefix h).getElem hi'
  · exact ((kimberlingBlock_prefix h).getElem hi).symm

-- The parity-sum formula gives monotonicity; the original recurrence then bounds each step.
private theorem gutkovskiy_monotone : Monotone gutkovskiy := by
  apply monotone_nat_of_le_succ
  intro n
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add n
  have hs := gutkovskiy_eq_two_mul_sum_mod_two_add (n + 1)
  rw [Finset.sum_range_succ] at hs
  omega

private theorem gutkovskiy_succ_le (n : ℕ) : gutkovskiy (n + 1) ≤ gutkovskiy n + 1 := by
  cases n with
  | zero => simp only [gutkovskiy_initial.1, gutkovskiy_initial.2.1, zero_add, le_refl]
  | succ n =>
    have h : gutkovskiy n ≤ gutkovskiy (n + 1) := gutkovskiy_monotone (Nat.le_succ n)
    have hhalf : gutkovskiy n / 2 ≤ gutkovskiy (n + 1) / 2 := by omega
    have hsub := gutkovskiy_monotone hhalf
    have h₁ := gutkovskiy_succ n
    have h₂ : gutkovskiy (n + 2) = n + 2 - gutkovskiy (gutkovskiy (n + 1) / 2) :=
      gutkovskiy_succ (n + 1)
    change gutkovskiy (n + 2) ≤ gutkovskiy (n + 1) + 1
    omega

private def increment (n : ℕ) : Bool := decide (gutkovskiy n < gutkovskiy (n + 1))

private theorem gutkovskiy_succ_eq_add_increment (n : ℕ) :
    gutkovskiy (n + 1) = gutkovskiy n + (increment n).toNat := by
  have hlo : gutkovskiy n ≤ gutkovskiy (n + 1) := gutkovskiy_monotone (Nat.le_succ n)
  have hhi := gutkovskiy_succ_le n
  by_cases h : gutkovskiy n < gutkovskiy (n + 1) <;> simp [increment, h] <;> omega

-- The block for `increment m` starts at `2 * m + gutkovskiy m`.
private def blockStart (m : ℕ) : ℕ := 2 * m + gutkovskiy m

private theorem blockStart_succ (m : ℕ) :
    blockStart (m + 1) = blockStart m + (2 + (increment m).toNat) := by
  unfold blockStart
  rw [gutkovskiy_succ_eq_add_increment m]
  omega

-- From the even value at the start, the next two recurrence calls both read `gutkovskiy m`.
private theorem next_two_at_blockStart (m : ℕ) (h : gutkovskiy (blockStart m) = 2 * m) :
    gutkovskiy (blockStart m + 1) = 2 * m + 1 ∧
      gutkovskiy (blockStart m + 2) = 2 * m + 2 := by
  have h₁ : gutkovskiy (blockStart m + 1) = 2 * m + 1 := by
    rw [gutkovskiy_succ, h, show 2 * m / 2 = m by omega]
    unfold blockStart
    omega
  refine ⟨h₁, ?_⟩
  rw [gutkovskiy_succ (blockStart m + 1), h₁, show (2 * m + 1) / 2 = m by omega]
  unfold blockStart
  omega

private theorem gutkovskiy_at_blockStart (m : ℕ) : gutkovskiy (blockStart m) = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h₂ := (next_two_at_blockStart m ih).2
    have hstart := blockStart_succ m
    have hincr := gutkovskiy_succ_eq_add_increment m
    cases h : increment m
    · simp only [h, Bool.toNat_false, Nat.add_zero] at hstart
      rw [hstart, h₂]
      omega
    · simp only [h, Bool.toNat_true] at hstart hincr
      rw [hstart, gutkovskiy_succ (blockStart m + 2), h₂,
        show (2 * m + 2) / 2 = m + 1 by omega]
      unfold blockStart
      omega

-- The first two steps are ones. If the block has a third step, its endpoint is already the
-- start of the next block, and that endpoint has the same value as at offset two.
private theorem morphism_increment (m : ℕ) :
    kimberlingMorphism (increment m) =
      (List.range (2 + (increment m).toNat)).map (fun j ↦ increment (blockStart m + j)) := by
  have h₀ := gutkovskiy_at_blockStart m
  obtain ⟨h₁, h₂⟩ := next_two_at_blockStart m h₀
  have hb₀ : increment (blockStart m + 0) = true := by simp [increment, h₀, h₁]
  have hb₁ : increment (blockStart m + 1) = true := by simp [increment, h₁, h₂]
  cases h : increment m
  · change [true, true] = [increment (blockStart m + 0), increment (blockStart m + 1)]
    rw [hb₀, hb₁]
  · have hnext := gutkovskiy_at_blockStart (m + 1)
    rw [blockStart_succ m, h] at hnext
    have hb₂ : increment (blockStart m + 2) = false := by
      change gutkovskiy (blockStart m + 3) = 2 * (m + 1) at hnext
      simp only [increment, h₂, hnext, decide_eq_false_iff_not]
      omega
    change [true, true, false] =
      [increment (blockStart m + 0), increment (blockStart m + 1), increment (blockStart m + 2)]
    rw [hb₀, hb₁, hb₂]

private theorem morphExtend_increment_prefix (m : ℕ) :
    morphExtend kimberlingMorphism ((List.range m).map increment) =
      (List.range (blockStart m)).map increment := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, morphExtend_append, ih, blockStart_succ m,
      List.range_add, List.map_append]
    simp only [List.map_singleton, List.map_map, Function.comp_def, morphExtend,
      List.flatMap_singleton, morphism_increment]

private theorem kimberlingBlock_eq_increment_prefix (n : ℕ) :
    kimberlingBlock n = (List.range (kimberlingBlock n).length).map increment := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : kimberlingBlock (n + 1) =
        (List.range (blockStart (kimberlingBlock n).length)).map increment :=
      (congrArg (morphExtend kimberlingMorphism) ih).trans (morphExtend_increment_prefix _)
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_range] at hlen
    simpa only [← hlen] using h

private theorem kimberlingWord_eq_increment (i : ℕ) : kimberlingWord i = increment i := by
  have hi : i < (kimberlingBlock i).length :=
    (Nat.lt_pow_self (by decide : 1 < 2)).trans_le (two_pow_le_length_kimberlingBlock i)
  rw [kimberlingWord_eq_getD hi]
  have h := kimberlingBlock_eq_increment_prefix i
  rw [List.getD_eq_getElem?_getD, h]
  simp [hi]

/-- **Irvine's conjecture for Gutkovskiy's sequence.** Let $g_0, g_1, \dots$ be Gutkovskiy's
sequence and let $k_1 k_2 k_3 \cdots$ be Kimberling's word, with its letters read as the numbers
$0$ and $1$. Then $g_n = k_1 + \dots + k_n$ for every $n \ge 0$ (the empty sum when $n = 0$).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 1 (`integers-2024-A51-thm-1`). -/
public theorem gutkovskiy_eq_sum_kimberlingWord (n : ℕ) :
    gutkovskiy n = ∑ i ∈ Finset.range n, (kimberlingWord i).toNat := by
  induction n with
  | zero => simp [gutkovskiy_initial.1]
  | succ n ih =>
    rw [Finset.sum_range_succ, kimberlingWord_eq_increment, ← ih,
      gutkovskiy_succ_eq_add_increment]

/-- **Positions of the ones in Kimberling's word.** Let $k = k_1 k_2 k_3 \cdots$ be Kimberling's
word over $\{0, 1\}$. For $n \ge 1$, $A_n$ is the position of the $n$-th $1$ in $k$, that is, the
$n$-th smallest index $j \ge 1$ with $k_j = 1$; by convention $A_0 = 0$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 8 (the sequence `A_n`). -/
public noncomputable def kimberlingOnePosition (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun i ↦ kimberlingWord i = true) (n - 1) + 1

/-- **Positions of the zeros in Kimberling's word.** Let $k = k_1 k_2 k_3 \cdots$ be Kimberling's
word over $\{0, 1\}$. For $n \ge 1$, $B_n$ is the position of the $n$-th $0$ in $k$, that is, the
$n$-th smallest index $j \ge 1$ with $k_j = 0$; by convention $B_0 = 0$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 8 (the sequence `B_n`). -/
public noncomputable def kimberlingZeroPosition (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun i ↦ kimberlingWord i = false) (n - 1) + 1

/-- If the letter at zero-based index `i` is a one and the preceding prefix contains `n` ones,
then the one-based position of the `(n + 1)`-st one is `i + 1`. -/
public theorem kimberlingOnePosition_eq_succ_of_count {n i : ℕ} (hi : kimberlingWord i = true)
    (hc : Nat.count (fun j ↦ kimberlingWord j = true) i = n) :
    kimberlingOnePosition (n + 1) = i + 1 := by
  simp only [kimberlingOnePosition, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [← hc, Nat.nth_count hi]

/-- If the letter at zero-based index `i` is a zero and the preceding prefix contains `n` zeros,
then the one-based position of the `(n + 1)`-st zero is `i + 1`. -/
public theorem kimberlingZeroPosition_eq_succ_of_count {n i : ℕ} (hi : kimberlingWord i = false)
    (hc : Nat.count (fun j ↦ kimberlingWord j = false) i = n) :
    kimberlingZeroPosition (n + 1) = i + 1 := by
  simp only [kimberlingZeroPosition, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [← hc, Nat.nth_count hi]

/-- **Position of the first one in Kimberling's word.** The position $A_1$ of the first $1$ in
Kimberling's word $k = k_1 k_2 k_3 \cdots$, counted from $1$, is $A_1 = 1$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingOnePosition_one : kimberlingOnePosition 1 = 1 :=
  kimberlingOnePosition_eq_succ_of_count (n := 0) (i := 0) (by decide) (by decide)

/-- **The first zero of Kimberling's word.** Let $B_n$ be the position of the $n$-th $0$ in
Kimberling's word $k = k_1 k_2 k_3 \cdots$. Then $B_1 = 3$: the first $0$ of $k$ is $k_3$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingZeroPosition_one : kimberlingZeroPosition 1 = 3 :=
  kimberlingZeroPosition_eq_succ_of_count (n := 0) (i := 2) (by decide) (by decide)

section Positions

local notation "g" => gutkovskiy

private theorem count_kimberlingWord (b : Bool) (n : ℕ) :
    Nat.count (fun i ↦ kimberlingWord i = b) n = if b then g n else n - g n := by
  induction n with
  | zero => simp [gutkovskiy_initial.1]
  | succ n ih =>
    rw [Nat.count_succ, ih, kimberlingWord_eq_increment, gutkovskiy_succ_eq_add_increment]
    have h := gutkovskiy_le n
    cases b <;> cases increment n
    all_goals simp
    omega

-- Each substituted letter contributes its two initial ones, at the first two steps of its block.
private theorem kimberlingOnePosition_spec (n : ℕ) (hn : 1 ≤ n) :
    kimberlingOnePosition n = n + g ((n - 1) / 2) ∧
      g (kimberlingOnePosition n - 1) = n - 1 ∧ g (kimberlingOnePosition n) = n := by
  let m := (n - 1) / 2
  let i := n + g m - 1
  have h₀ := gutkovskiy_at_blockStart m
  obtain ⟨h₁, h₂⟩ := next_two_at_blockStart m h₀
  have hstart : blockStart m = 2 * m + g m := rfl
  have hm : 2 * m + 1 ≤ n ∧ n ≤ 2 * m + 2 := by dsimp [m]; omega
  have ⟨hpre, hpost⟩ : g i = n - 1 ∧ g (i + 1) = n := by
    by_cases h : n = 2 * m + 1
    · rw [show i = blockStart m by dsimp [i]; omega, h₀, h₁]
      omega
    · rw [show i = blockStart m + 1 by dsimp [i]; omega, h₁, Nat.add_assoc, h₂]
      omega
  have hw : kimberlingWord i = true := by
    rw [kimberlingWord_eq_increment, increment]
    exact decide_eq_true (by omega)
  have hc : Nat.count (fun j ↦ kimberlingWord j = true) i = n - 1 := by
    simpa [count_kimberlingWord] using hpre
  have hpos := kimberlingOnePosition_eq_succ_of_count hw hc
  rw [show n - 1 + 1 = n by omega] at hpos
  rw [hpos]
  refine ⟨?_, by simpa only [Nat.add_sub_cancel] using hpre, hpost⟩
  change n + g m - 1 + 1 = n + g m
  omega

-- The `n`-th zero is the final letter of the substituted block of the `n`-th one.
private theorem kimberlingZeroPosition_spec (n : ℕ) (hn : 1 ≤ n) :
    kimberlingZeroPosition n = 2 * kimberlingOnePosition n + n ∧
      kimberlingZeroPosition n - 1 - g (kimberlingZeroPosition n - 1) = n - 1 ∧
      kimberlingZeroPosition n - g (kimberlingZeroPosition n) = n := by
  obtain ⟨hA, hpre, hpost⟩ := kimberlingOnePosition_spec n hn
  let a := kimberlingOnePosition n
  change g (a - 1) = n - 1 at hpre
  change g a = n at hpost
  have ha : 0 < a := by dsimp [a]; omega
  let t := blockStart a
  have ht : t = 2 * a + n := by simp only [t, blockStart, hpost]
  have hbefore : t - 1 = blockStart (a - 1) + 2 := by
    rw [blockStart, hpre]
    omega
  have hg : g (t - 1) = 2 * a := by
    rw [hbefore, (next_two_at_blockStart _ (gutkovskiy_at_blockStart _)).2]
    omega
  have hgt : g t = 2 * a := gutkovskiy_at_blockStart a
  have hs : t - 1 + 1 = t := by omega
  have hw : kimberlingWord (t - 1) = false := by
    rw [kimberlingWord_eq_increment, increment, hs, hg, hgt]
    simp
  have hc : Nat.count (fun j ↦ kimberlingWord j = false) (t - 1) = n - 1 := by
    simp only [count_kimberlingWord, Bool.false_eq_true, ite_false, hg]
    omega
  have hpos := kimberlingZeroPosition_eq_succ_of_count hw hc
  rw [show n - 1 + 1 = n by omega, hs] at hpos
  rw [hpos]
  exact ⟨ht, by omega, by omega⟩

-- The recurrence makes `m + 1 - g (m + 1) = g k` at `k = g m / 2`.
-- The two successive values `g m` and `g (m + 1)` locate `2 * k + 1` between
-- `g (m + 1) - 1` and `g (m + 1) + 1`, letting the two bounds feed each other.
private theorem gutkovskiy_bounds_odd (m : ℕ) :
    2 * g m - 1 ≤ g (2 * m + 1) ∧ g (2 * m + 1) ≤ 2 * g m + 2 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero => simp [gutkovskiy_initial.1, gutkovskiy_initial.2.1]
    | succ m =>
      let k := g m / 2
      have hm := gutkovskiy_le m
      have hk : k < m + 1 := by dsimp [k]; omega
      obtain ⟨hlow, hhigh⟩ := ih k hk
      have hstep := gutkovskiy_succ_le m
      have hmono : g m ≤ g (m + 1) := gutkovskiy_monotone (Nat.le_succ m)
      have hrec : g (m + 1) = m + 1 - g k := gutkovskiy_succ m
      have hgk := gutkovskiy_le k
      have hbetween : g (m + 1) - 1 ≤ 2 * k + 1 ∧ 2 * k + 1 ≤ g (m + 1) + 1 := by
        dsimp [k]
        omega
      constructor
      · by_cases h : g (m + 1) = 0
        · simp [h]
        · obtain ⟨hpos, _, hcount⟩ := kimberlingOnePosition_spec (2 * g (m + 1) - 1) (by omega)
          rw [show (2 * g (m + 1) - 1 - 1) / 2 = g (m + 1) - 1 by omega] at hpos
          have hsmall := gutkovskiy_monotone hbetween.1
          rw [← hcount]
          exact gutkovskiy_monotone (by omega)
      · obtain ⟨hpos, hcount, _⟩ := kimberlingOnePosition_spec (2 * g (m + 1) + 3) (by omega)
        rw [show (2 * g (m + 1) + 3 - 1) / 2 = g (m + 1) + 1 by omega] at hpos
        have hlarge := gutkovskiy_monotone hbetween.2
        have hle : 2 * (m + 1) + 1 ≤ kimberlingOnePosition (2 * g (m + 1) + 3) - 1 := by
          omega
        have := gutkovskiy_monotone hle
        omega

/-- **Positions of ones at the positions of zeros in Kimberling's word.** Let
$k = k_1 k_2 k_3 \cdots$ be Kimberling's word, and for $n \ge 1$ let $A_n$ and $B_n$ be the
positions (counted from $1$) of the $n$-th $1$ and of the $n$-th $0$ in $k$. Then for every
$n \ge 1$, either $A_{B_n} = A_n + B_n - 1$ or $A_{B_n} = A_n + B_n$.

This answers a problem of Fokkink, Ortega and Rust.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 3 (`integers-2024-A51-thm-3`). -/
public theorem kimberlingOnePosition_kimberlingZeroPosition {n : ℕ} (hn : 1 ≤ n) :
    kimberlingOnePosition (kimberlingZeroPosition n) + 1 =
        kimberlingOnePosition n + kimberlingZeroPosition n ∨
      kimberlingOnePosition (kimberlingZeroPosition n) =
        kimberlingOnePosition n + kimberlingZeroPosition n := by
  let r := (n - 1) / 2
  let s := kimberlingOnePosition n + r
  have hA : kimberlingOnePosition n = n + g r := (kimberlingOnePosition_spec n hn).1
  have hB := (kimberlingZeroPosition_spec n hn).1
  have hAB := (kimberlingOnePosition_spec (kimberlingZeroPosition n) (by omega)).1
  rw [show (kimberlingZeroPosition n - 1) / 2 = s by rw [hB]; dsimp [s, r]; omega] at hAB
  -- The prefix of length `s` lies after at least `r` zeros but before the `(r + 2)`-nd zero.
  suffices r ≤ s - g s ∧ s - g s ≤ r + 1 by
    have hgs := gutkovskiy_le s
    dsimp [s] at *
    omega
  have hs : 3 * r + g r + 1 ≤ s ∧ s ≤ 3 * r + g r + 2 := by
    dsimp [s, r] at *
    omega
  by_cases hr : r = 0
  · rw [hr, gutkovskiy_initial.1] at hs
    have : s = 1 ∨ s = 2 := by omega
    rcases this with h | h <;> simp [hr, h, gutkovskiy_initial.2.1, gutkovskiy_initial.2.2.1]
  let p := (r - 1) / 2
  have hparity : 2 * p + 1 ≤ r ∧ r ≤ 2 * p + 2 := by dsimp [p]; omega
  obtain ⟨hlow, hhigh⟩ := gutkovskiy_bounds_odd p
  have hmono₁ := gutkovskiy_monotone hparity.1
  have hmono₂ := gutkovskiy_monotone hparity.2
  have hstep : g (2 * p + 2) ≤ g (2 * p + 1) + 1 := gutkovskiy_succ_le (2 * p + 1)
  have hnext : g p ≤ g (p + 1) := gutkovskiy_monotone (Nat.le_succ p)
  obtain ⟨hleft, _, hcount₁⟩ := kimberlingZeroPosition_spec r (by omega)
  obtain ⟨hright, hcount₂, _⟩ := kimberlingZeroPosition_spec (r + 2) (by omega)
  rw [(kimberlingOnePosition_spec r (by omega)).1] at hleft
  change kimberlingZeroPosition r = 2 * (r + g p) + r at hleft
  rw [(kimberlingOnePosition_spec (r + 2) (by omega)).1,
    show (r + 2 - 1) / 2 = p + 1 by dsimp [p]; omega] at hright
  have hzeros : Monotone (fun j : ℕ ↦ j - g j) := by
    intro a b hab
    simpa [count_kimberlingWord] using Nat.count_monotone (fun i ↦ kimberlingWord i = false) hab
  have hlo : kimberlingZeroPosition r ≤ s := by omega
  have hhi : s ≤ kimberlingZeroPosition (r + 2) - 1 := by omega
  have hlower : kimberlingZeroPosition r - g (kimberlingZeroPosition r) ≤ s - g s := hzeros hlo
  have hupper : s - g s ≤
      kimberlingZeroPosition (r + 2) - 1 - g (kimberlingZeroPosition (r + 2) - 1) := hzeros hhi
  rw [hcount₁] at hlower
  rw [hcount₂] at hupper
  exact ⟨hlower, by omega⟩

end Positions

/-- **The Kimberling position identity at index zero.** With the conventions $A_0 = B_0 = 0$,
the equality branch of the identity holds at $n = 0$: $A_{B_0} = A_0 + B_0 = 0$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 3 and Table 3. -/
public theorem kimberlingOnePosition_kimberlingZeroPosition_zero :
    kimberlingOnePosition (kimberlingZeroPosition 0) =
        kimberlingOnePosition 0 + kimberlingZeroPosition 0 ∧
      kimberlingOnePosition 0 + kimberlingZeroPosition 0 = 0 := by
  simp [kimberlingOnePosition, kimberlingZeroPosition]

end

end MetaMathlibExt
