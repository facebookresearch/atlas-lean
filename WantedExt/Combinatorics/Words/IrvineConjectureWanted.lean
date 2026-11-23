/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import WantedExt.Combinatorics.Words.MetaAutomaticSequencesWanted

/-! # Irvine's conjecture on Gutkovskiy's sequence (Shallit)

Statements from Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*,
INTEGERS 24 (2024), Article A51. Letters `0, 1` of Kimberling's word are `false, true`, and
the word `k = k₁k₂⋯` is indexed from `0` (`kimberlingWord i = k_{i+1}`, the paper's `k'_i`);
the paper's convention `k₀ = 0` only shifts indices. The numbers `K_n = |K_n|` are the lengths
`(kimberlingBlock n).length`.
-/

namespace MetaMathlibExt

open Filter

@[expose] public section

/-- **Kimberling's morphism.** Kimberling's morphism $h$ sends each letter of the alphabet
$\{0, 1\}$ to a finite word over $\{0, 1\}$, by $h(1) = 110$ and $h(0) = 11$.

The letters $0$ and $1$ are represented by the Boolean values false and true.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1 and Section 2 (the morphism `h`). -/
public def kimberlingMorphism : Bool → List Bool
  | true => [true, true, false]
  | false => [true, true]

/-- **Kimberling's blocks.** Let $h$ be Kimberling's morphism on the alphabet $\{0, 1\}$, given by
$h(1) = 110$ and $h(0) = 11$ and extended to finite words by concatenation. For each natural
number $n$, the $n$-th Kimberling block is the finite word $K_n = h^n(1)$, the $n$-th iterate of
$h$ applied to the one-letter word $1$. Thus $K_0 = 1$, $K_1 = 110$ and $K_2 = 11011011$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2 (`K_n = h^n(1)`). -/
public def kimberlingBlock (n : ℕ) : List Bool :=
  morphIterate kimberlingMorphism n [true]

/-- **The first Kimberling block.** For Kimberling's morphism $h$ on $\{0, 1\}$, given by
$h(1) = 110$ and $h(0) = 11$, the block $K_1 = h(1)$ is the word $110$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_one : kimberlingBlock 1 = [true, true, false] := rfl

/-- **The second Kimberling block.** For Kimberling's morphism $h$ on $\{0, 1\}$, given by
$h(1) = 110$ and $h(0) = 11$, the block $K_2 = h^2(1)$ is the word $11011011$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_two :
    kimberlingBlock 2 = [true, true, false, true, true, false, true, true] := rfl

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

/-- **The first letters of Kimberling's word.** The first four letters of Kimberling's word
$k = k_1 k_2 k_3 \cdots$ are $k_1 k_2 k_3 k_4 = 1101$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 1. -/
public theorem kimberlingWord_initial :
    kimberlingWord 0 = true ∧ kimberlingWord 1 = true ∧ kimberlingWord 2 = false ∧
      kimberlingWord 3 = true := by
  decide

/-- **The 101st letter of Kimberling's word.** The letter $k_{101}$ of Kimberling's word
$k = k_1 k_2 k_3 \cdots$ is $0$ (OEIS A285431).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingWord_hundred : kimberlingWord 100 = false := by
  decide +kernel

/-- **Table of Gutkovskiy's sequence.** The Gutkovskiy tables $T_0, T_1, \dots$ are finite lists
of natural numbers, indexed from $0$, defined by $T_0 = [0]$ and, for $n \ge 0$, $T_{n+1}$ is
$T_n$ with the entry $(n + 1) - T_n[\lfloor T_n[n]/2 \rfloor]$ appended at the end. Here $T_n[j]$
is the entry of $T_n$ at index $j$, or $0$ if $T_n$ has fewer than $j + 1$ entries, and the
subtraction is truncated at $0$.

$T_n$ has $n + 1$ entries and lists the terms $g_0, \dots, g_n$ of Gutkovskiy's sequence, so each
step reads only values already computed.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiyTable : ℕ → Array ℕ
  | 0 => #[0]
  | n + 1 =>
    let a := gutkovskiyTable n
    a.push ((n + 1) - a.getD (a.getD n 0 / 2) 0)

/-- **Gutkovskiy's sequence.** Gutkovskiy's sequence (OEIS A286389) is the sequence of natural
numbers $g_0, g_1, \dots$ with $g_0 = 0$ and $g_n = n - g_{\lfloor g_{n-1}/2 \rfloor}$ for
$n \ge 1$ (subtraction of natural numbers, truncated at $0$).

Formally, $g_n$ is defined as $T_n[n]$, the entry at index $n$ of the Gutkovskiy table $T_n$, and
the recurrence is proved from the table.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiy (n : ℕ) : ℕ :=
  (gutkovskiyTable n).getD n 0

/-- **Number of entries of the Gutkovskiy table.** For every natural number $n$, the Gutkovskiy
table up to index $n$, the array of the values $g_0, \dots, g_n$ of Gutkovskiy's sequence, has
exactly $n + 1$ entries.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem size_gutkovskiyTable (n : ℕ) : (gutkovskiyTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gutkovskiyTable, ih]

/-- **Entries of the Gutkovskiy table.** For natural numbers $k \le n$, the entry at index $k$
(counting from $0$) of the Gutkovskiy table $T_n$ is the term $g_k$ of Gutkovskiy's sequence.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem getD_gutkovskiyTable {k n : ℕ} (h : k ≤ n) :
    (gutkovskiyTable n).getD k 0 = gutkovskiy k := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [← ih (by omega)]
      simp only [gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable]
      simp [show k ≠ n + 1 by omega]
    · obtain rfl : k = n + 1 := by omega
      rfl

/-- **Gutkovskiy's sequence is bounded by the index.** For every natural number $n$, the term
$g_n$ of Gutkovskiy's sequence satisfies $g_n \le n$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_le (n : ℕ) : gutkovskiy n ≤ n := by
  cases n with
  | zero => decide
  | succ n =>
    have : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
        ((gutkovskiyTable n).getD n 0 / 2) 0 := by
      simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
    omega

/-- **Recurrence for Gutkovskiy's sequence.** For every natural number $n$, Gutkovskiy's sequence
satisfies $g_{n+1} = (n + 1) - g_{\lfloor g_n/2 \rfloor}$ (subtraction of natural numbers,
truncated at $0$).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_succ (n : ℕ) :
    gutkovskiy (n + 1) = (n + 1) - gutkovskiy (gutkovskiy n / 2) := by
  have h1 : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
      ((gutkovskiyTable n).getD n 0 / 2) 0 := by
    simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
  rw [h1, getD_gutkovskiyTable le_rfl, getD_gutkovskiyTable
    (le_trans (Nat.div_le_self _ _) (gutkovskiy_le n))]

/-- **First terms of Gutkovskiy's sequence.** The first four terms of Gutkovskiy's sequence are
$g_0 = 0$, $g_1 = 1$, $g_2 = 2$ and $g_3 = 2$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 1. -/
public theorem gutkovskiy_initial :
    gutkovskiy 0 = 0 ∧ gutkovskiy 1 = 1 ∧ gutkovskiy 2 = 2 ∧ gutkovskiy 3 = 2 := by
  have h0 : gutkovskiy 0 = 0 := rfl
  have h1 : gutkovskiy 1 = 1 := by rw [gutkovskiy_succ, h0, h0]
  have h2 : gutkovskiy 2 = 2 := by rw [gutkovskiy_succ, h1, h0]
  have h3 : gutkovskiy 3 = 2 := by rw [gutkovskiy_succ, h2, h1]
  exact ⟨h0, h1, h2, h3⟩

/-- **Gutkovskiy's sequence at $100$.** The term $g_{100}$ of Gutkovskiy's sequence is $74$, in
agreement with OEIS A286389.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_hundred : gutkovskiy 100 = 74 := by
  decide +kernel

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

/-- **Position of the first one in Kimberling's word.** The position $A_1$ of the first $1$ in
Kimberling's word $k = k_1 k_2 k_3 \cdots$, counted from $1$, is $A_1 = 1$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingOnePosition_one : kimberlingOnePosition 1 = 1 := by
  simp only [kimberlingOnePosition, one_ne_zero, ↓reduceIte, Nat.sub_self]
  rw [Nat.nth_zero_of_zero (p := fun i ↦ kimberlingWord i = true) kimberlingWord_initial.1]

/-- **The first zero of Kimberling's word.** Let $B_n$ be the position of the $n$-th $0$ in
Kimberling's word $k = k_1 k_2 k_3 \cdots$. Then $B_1 = 3$: the first $0$ of $k$ is $k_3$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingZeroPosition_one : kimberlingZeroPosition 1 = 3 := by
  have hc : Nat.count (fun i ↦ kimberlingWord i = false) 2 = 0 := by decide
  have h := Nat.nth_count (p := fun i ↦ kimberlingWord i = false) kimberlingWord_initial.2.2.1
  rw [hc] at h
  simp only [kimberlingZeroPosition, one_ne_zero, ↓reduceIte, Nat.sub_self]
  rw [h]

/-- **Recursive structure of Kimberling's blocks.** Let $h$ be Kimberling's morphism on $\{0, 1\}$,
$h(1) = 110$ and $h(0) = 11$, and let $K_n = h^n(1)$. Then for every $n \ge 2$,
$K_n = K_{n-1} K_{n-1} K_{n-2} K_{n-2}$ (concatenation of words).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Proposition 1 (`integers-2024-A51-prop-1`). -/
public theorem_wanted kimberlingBlock_eq_append {n : ℕ} (hn : 2 ≤ n) :
    kimberlingBlock n = kimberlingBlock (n - 1) ++ kimberlingBlock (n - 1) ++
      kimberlingBlock (n - 2) ++ kimberlingBlock (n - 2)

/-- **Irvine's conjecture for Gutkovskiy's sequence.** Let $g_0, g_1, \dots$ be Gutkovskiy's
sequence and let $k_1 k_2 k_3 \cdots$ be Kimberling's word, with its letters read as the numbers
$0$ and $1$. Then $g_n = k_1 + \dots + k_n$ for every $n \ge 0$ (the empty sum when $n = 0$).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 1 (`integers-2024-A51-thm-1`). -/
public theorem_wanted gutkovskiy_eq_sum_kimberlingWord (n : ℕ) :
    gutkovskiy n = ∑ i ∈ Finset.range n, (kimberlingWord i).toNat

/-- **Closed form for Gutkovskiy's sequence.** Let $g_0, g_1, \dots$ be Gutkovskiy's sequence,
let $|K_i|$ be the length of the Kimberling block $K_i$, and let $\alpha = (\sqrt{3} - 1)/2$ and
$\beta = \sqrt{3}/3$. Let $n$ be a natural number and let $a_0, a_1, \dots, a_{m-1}$ be digits in
$\{0, 1, 2\}$ such that no two consecutive digits $a_i, a_{i+1}$ are both $2$ and
$n = \sum_{i < m} a_i |K_i|$. If $m \ge 1$ and $a_0 = 1$, then
$g_n = 2\lfloor \alpha n \rfloor + 1$; if $m \ge 1$ and $a_0 \in \{0, 2\}$, then
$g_n = 2\lfloor \alpha n + \beta \rfloor$.

Written most significant digit first, $a_{m-1} \cdots a_1 a_0$ is a $K$-representation of $n$
ending in the digit $a_0$; leading zeros are allowed.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 2 (`integers-2024-A51-thm-2`). -/
public theorem_wanted gutkovskiy_eq_two_mul_floor {n : ℕ} {a : List ℕ} (ha : ∀ d ∈ a, d ≤ 2)
    (h22 : ¬ [2, 2] <:+: a)
    (hn : (a.mapIdx fun i d ↦ d * (kimberlingBlock i).length).sum = n) :
    (a.head? = some 1 → (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ)⌋ + 1) ∧
      (a.head? = some 0 ∨ a.head? = some 2 →
        (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ) + √3 / 3⌋)

/-- **Positions of ones at the positions of zeros in Kimberling's word.** Let
$k = k_1 k_2 k_3 \cdots$ be Kimberling's word, and for $n \ge 1$ let $A_n$ and $B_n$ be the
positions (counted from $1$) of the $n$-th $1$ and of the $n$-th $0$ in $k$. Then for every
$n \ge 1$, either $A_{B_n} = A_n + B_n - 1$ or $A_{B_n} = A_n + B_n$.

This answers a problem of Fokkink, Ortega and Rust.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 3 (`integers-2024-A51-thm-3`). -/
public theorem_wanted kimberlingOnePosition_kimberlingZeroPosition {n : ℕ} (hn : 1 ≤ n) :
    kimberlingOnePosition (kimberlingZeroPosition n) + 1 =
        kimberlingOnePosition n + kimberlingZeroPosition n ∨
      kimberlingOnePosition (kimberlingZeroPosition n) =
        kimberlingOnePosition n + kimberlingZeroPosition n

/-- **Gutkovskiy's sequence modulo 2 is generated by a morphism.** Let $g_0, g_1, g_2, \ldots$ be
Gutkovskiy's sequence, and let $u$ be the map on the alphabet $\mathbb{N}$ with $u(0) = 01$ and
$u(b) = 0010$ for every letter $b \ne 0$. Then the infinite word $(g_n \bmod 2)_{n \ge 0}$ is the
limit of the iterates of $u$ at the letter $0$. On the letters $0$ and $1$ that occur, $u$ is the
morphism $0 \mapsto 01$, $1 \mapsto 0010$, and the word is OEIS A284772.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 4 (`integers-2024-A51-thm-4`). -/
public theorem_wanted isOmegaLimit_gutkovskiy_mod_two :
    IsOmegaLimit (fun b : ℕ ↦ if b = 0 then [0, 1] else [0, 0, 1, 0]) 0
      fun n ↦ gutkovskiy n % 2

/-- **Gutkovskiy's sequence from its parities.** Let $g_0, g_1, \dots$ be Gutkovskiy's sequence,
let $g'_n = g_n \bmod 2$ and let $h_n = \sum_{0 \le i < n} g'_i$. Then $g_n = 2h_n + g'_n$ for
every $n \ge 0$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 5 (`integers-2024-A51-thm-5`). -/
public theorem_wanted gutkovskiy_eq_two_mul_sum_mod_two_add (n : ℕ) :
    gutkovskiy n = 2 * ∑ i ∈ Finset.range n, gutkovskiy i % 2 + gutkovskiy n % 2

/-- **Lengths with two right-special factors in Kimberling's word.** Let $k$ be Kimberling's word
and write $K_m$ for the length of the $m$-th Kimberling block. A word $u$ is a right-special factor
of $k$ if both $u0$ and $u1$ are factors of $k$. For every $n \ge 0$, $k$ has exactly two
right-special factors of length $n$ if and only if there is an $i \ge 0$ such that
$x_i \le n < x_i + K_{2i}$, where $x_i = K_1 + K_3 + \cdots + K_{2i+1}$, or
$y_i \le n < y_i + K_{2i+1}$, where $y_i = K_0 + K_2 + \cdots + K_{2i+2}$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 6 (`integers-2024-A51-thm-6`). -/
public theorem_wanted rightSpecialFactors_kimberlingWord_ncard_eq_two_iff (n : ℕ) :
    (rightSpecialFactors kimberlingWord n).ncard = 2 ↔ ∃ i : ℕ,
      (∑ j ∈ Finset.range (i + 1), (kimberlingBlock (2 * j + 1)).length ≤ n ∧
        n < ∑ j ∈ Finset.range (i + 1), (kimberlingBlock (2 * j + 1)).length +
          (kimberlingBlock (2 * i)).length) ∨
      (∑ j ∈ Finset.range (i + 2), (kimberlingBlock (2 * j)).length ≤ n ∧
        n < ∑ j ∈ Finset.range (i + 2), (kimberlingBlock (2 * j)).length +
          (kimberlingBlock (2 * i + 1)).length)

/-- **Factor complexity of Kimberling's word.** Let $\rho(n)$ be the factor complexity of
Kimberling's word $k$, the number of distinct factors of $k$ of length $n$. Then, as $n \to \infty$
over the natural numbers, $\limsup \rho(n)/n = (30 + \sqrt{3})/23$ and
$\liminf \rho(n)/n = (3 + \sqrt{3})/4$.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Corollary 1 (`integers-2024-A51-cor-1`). -/
public theorem_wanted limsup_liminf_wordFactorComplexity_kimberlingWord :
    limsup (fun n : ℕ ↦ (wordFactorComplexity kimberlingWord n : ℝ) / n) atTop =
        (30 + √3) / 23 ∧
      liminf (fun n : ℕ ↦ (wordFactorComplexity kimberlingWord n : ℝ) / n) atTop =
        (3 + √3) / 4

/-- **Critical exponent of Kimberling's word.** Let $k = k_1 k_2 k_3 \cdots$ be Kimberling's
word. The supremum of the ratios $m/p$, over all integers $m \ge 1$ and $p \ge 1$ for which some
factor $k_{i+1} k_{i+2} \cdots k_{i+m}$ of $k$ ($i \ge 0$) has period $p$, that is,
$k_{i+1+j} = k_{i+1+j+p}$ for every $j \ge 0$ with $j + p < m$, is $(2\sqrt{3} + 12)/3$.

Allowing every period, not only the shortest one, does not change the supremum.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 7 (`integers-2024-A51-thm-7`). -/
public theorem_wanted sSup_exponent_kimberlingWord :
    sSup {e : ℝ | ∃ i m p : ℕ, 0 < m ∧ 0 < p ∧
      (∀ j, j + p < m → kimberlingWord (i + j) = kimberlingWord (i + j + p)) ∧
        e = m / p} = (2 * √3 + 12) / 3

end

end MetaMathlibExt
