/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.InfiniteWord.Gutkovskiy
public import MathlibExt.Combinatorics.InfiniteWord.KimberlingBlock
import Mathlib.Tactic.NormNum

/-! # Irvine's conjecture for Gutkovskiy's sequence

The successive differences of Gutkovskiy's sequence form Kimberling's word. We identify their
finite prefixes using the morphism `0 ↦ 11`, `1 ↦ 110`, then sum the differences.
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

end

end MetaMathlibExt
