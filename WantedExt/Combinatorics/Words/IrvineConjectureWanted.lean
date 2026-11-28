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
