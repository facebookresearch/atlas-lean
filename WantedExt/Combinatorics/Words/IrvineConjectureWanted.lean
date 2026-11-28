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
public import MathlibExt.Combinatorics.InfiniteWord.GutkovskiyFloor
public import MathlibExt.Combinatorics.InfiniteWord.GutkovskiyModTwo
public import MathlibExt.Combinatorics.InfiniteWord.IrvineConjecture
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
