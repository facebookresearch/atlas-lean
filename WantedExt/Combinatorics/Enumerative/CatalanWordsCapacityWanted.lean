/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.TrinomialCoefficient

namespace MetaMathlibExt

@[expose] public section

/-- **A recursion for binomial sums of odd-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with the convention $F_{-1} = 1$. For all integers $n \ge 1$ and $2 \le i \le n + 1$,
$$\sum_{m=0}^{n-i+1} \binom{n-m-1}{i-2} F_{2m-1} =
\binom{n-1}{i-2} + \sum_{j=i}^{n} \sum_{m=0}^{n-j} \binom{n-m-2}{j-2} F_{2m-1}$$
(Mansour and Shattuck's Lemma 5, identity (21)). All differences in the binomial coefficients and
in the summation bounds are nonnegative.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem_wanted sum_choose_mul_fib_odd_eq_choose_add_sum (n i : ℕ) (hn : 1 ≤ n)
    (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    ∑ m ∈ Finset.range (n + 2 - i),
        (n - m - 1).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      (n - 1).choose (i - 2) +
        ∑ j ∈ Finset.Icc i n, ∑ m ∈ Finset.range (n - j + 1),
          (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))

/-- **A double-sum identity for even-indexed Fibonacci numbers.** Let $F_k$ be the Fibonacci
numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{k+2} = F_{k+1} + F_k$, and set $F_{-1} = 1$. For every
natural number $n \ge 1$,
$$F_{2n} = \sum_{j=1}^{n} \sum_{m=0}^{n-j} \binom{n-m-1}{j-1} F_{2m-1}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem_wanted fib_two_mul_eq_sum_sum_choose_mul_fib_odd (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.range (n - j + 1),
        (n - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1))


open Polynomial LaurentPolynomial

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

/-- **Area of a word.** The area of a word $w = w_1 \cdots w_n$ of natural numbers is the sum
$w_1 + \cdots + w_n$ of its letters, the area of its bargraph.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of the area statistic. -/
public def wordArea {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, w i

/-- **Capacity of the word $122341123212323$.** The word
$w = 1\,2\,2\,3\,4\,1\,1\,2\,3\,2\,1\,2\,3\,2\,3$ of length $15$ has capacity $10$ (Mansour and
Shattuck's Figure 1).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, Figure 1. -/
public theorem wordCapacity_figure_one :
    wordCapacity ![1, 2, 2, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3] = 10 := by
  decide

/-- **Catalan words.** For a natural number $n$, the set $\mathcal{A}_n$ of Catalan words of length
$n$ consists of the words $w = w_1 w_2 \cdots w_n$ of positive integers with $w_1 = 1$ and
$w_{i+1} \le w_i + 1$ for $1 \le i < n$; for $n = 0$ it contains only the empty word.

Every letter of a Catalan word of length $n$ is at most $n$, so $\mathcal{A}_n$ is finite.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of Catalan words. -/
public def catalanWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧ ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1

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

/-- **Words ending in a given letter.** Given a finite set $S$ of words $w = w_1 \cdots w_n$
of length $n$ with letters in $\mathbb{N}$ and a natural number $k$, this is the set of words
in $S$ whose last letter $w_n$ is $k$. When $n = 0$ this set is empty.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒜_{n,i}`. -/
public def wordsEndingIn {n : ℕ} (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.filter fun w => ∃ i : Fin n, i.val + 1 = n ∧ w i = k

/-- **Words with all letters at most a bound.** Given a finite set $S$ of words of length $n$
with letters in $\mathbb{N}$ and a natural number $k$, this is the set of words in $S$ all of
whose letters are at most $k$. Applied to the words of $S$ whose last letter is $k$, it gives
those whose largest letter is $k$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `ℬ_{n,i}`. -/
public def wordsBoundedBy {n : ℕ} (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.filter fun w => ∀ i : Fin n, w i ≤ k

/-- **Capacity distribution.** For a finite set $S$ of words of length $n$ with letters in the
natural numbers, the capacity distribution of $S$ is the polynomial
$\sum_{w \in S} q^{\operatorname{cap}(w)}$ in $\mathbb{Z}[q]$, where $\operatorname{cap}(w)$ is the
capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def capacityDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordCapacity w

/-- **Area distribution.** For a finite set $S$ of words of length $n$ with letters in the
natural numbers, the area distribution of $S$ is the polynomial
$\sum_{w \in S} q^{\operatorname{area}(w)}$ in $\mathbb{Z}[q]$, where the area of a word is the
sum of its letters.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def areaDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordArea w

/-- **Capacity distribution of Catalan words with a given last letter.** For natural numbers $n$
and $i$, $a(n, i; q) \in \mathbb{Z}[q]$ is the capacity distribution of the Catalan words of
length $n$ whose last letter is $i$: the sum of $q^{\mathrm{cap}(w)}$ over all such words $w$,
where $\mathrm{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def catalanCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (catalanWords n) i)

/-- **Capacity distribution of Catalan words ending in their largest letter.** For natural
numbers $n$ and $i$, $b(n, i; q) \in \mathbb{Z}[q]$ is the sum of $q^{\mathrm{cap}(w)}$, where
$\mathrm{cap}(w)$ is the capacity of $w$, over the Catalan words $w$ of length $n$ whose last
letter is $i$ and all of whose letters are at most $i$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `b(n, i; q)`. -/
public noncomputable def catalanMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (catalanWords n) i) i)

/-- **Capacity distribution of smooth words by last letter.** For $n, i \ge 0$, $r(n, i; q)$ is the
polynomial $\sum_w q^{\operatorname{cap}(w)} \in \mathbb{Z}[q]$, where $w$ runs over the smooth
words of length $n$ whose last letter is $i$ and $\operatorname{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `r(n, i; q)`. -/
public noncomputable def smoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (smoothWords n) i)

/-- **Capacity distribution of smooth words ending in their largest letter.** For $n, i \ge 0$,
$s(n, i; q)$ is the polynomial $\sum_w q^{\operatorname{cap}(w)} \in \mathbb{Z}[q]$, where $w$ runs
over the smooth words of length $n$ whose last letter is $i$ and all of whose letters are at most
$i$, and $\operatorname{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `s(n, i; q)`. -/
public noncomputable def smoothMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (smoothWords n) i) i)

/-- **Capacity distribution of restricted smooth words with a given last letter.** For natural
numbers $n$ and $i$, $r^*(n, i; q)$ is the polynomial $\sum_w q^{\mathrm{cap}(w)}$ in
$\mathbb{Z}[q]$, where $w$ ranges over the restricted smooth words of length $n$ (smooth words
with no two adjacent letters equal to $1$) whose last letter is $i$, and $\mathrm{cap}(w)$ is the
capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `r*(n, i; q)`. -/
public noncomputable def restrictedSmoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (restrictedSmoothWords n) i)

/-- **Capacity distribution of restricted smooth words ending in their largest letter.** For
natural numbers $n$ and $i$, $s^*(n, i; q)$ is the polynomial $\sum_w q^{\mathrm{cap}(w)}$ in
$\mathbb{Z}[q]$, where $w$ ranges over the restricted smooth words of length $n$ (smooth words
with no two adjacent letters equal to $1$) whose last letter is $i$ and all of whose letters are
at most $i$, and $\mathrm{cap}(w)$ is the capacity of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `s*(n, i; q)`. -/
public noncomputable def restrictedSmoothMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (restrictedSmoothWords n) i) i)

/-- **Words with unit-bounded rises ending in their maximum.** For natural numbers $m$ and $j$,
$\mathcal{C}_{m,j}$ is the set of words $w = w_1 \cdots w_m$ of length $m$ with letters in
$\{1, \dots, j\}$ such that $w_{k+1} \le w_k + 1$ for $1 \le k < m$ and whose last letter $w_m$
is $j$. It is empty when $m = 0$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒞_{m,j}`. -/
public def catalanGrowthWords (m j : ℕ) : Finset (Fin m → ℕ) :=
  wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    ∀ i k : Fin m, k.val = i.val + 1 → w k ≤ w i + 1) j

/-- **Area distribution of words with unit-bounded rises, by first letter.** For natural numbers
$m$, $j$ and $\ell$, let $\mathcal{C}_{m,j}$ be the set of words of length $m$ with letters in
$\{1, \dots, j\}$, each letter at most one more than the letter before it, and last letter $j$.
Then $c(m, j, \ell; q) \in \mathbb{Z}[q]$ is the area distribution of the words in
$\mathcal{C}_{m,j}$ whose first letter is $\ell$: the sum of $q^{\mathrm{area}(w)}$ over these
words $w$, where $\mathrm{area}(w)$ is the sum of the letters of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def catalanGrowthAreaDist (m j ℓ : ℕ) : ℤ[X] :=
  areaDist ((catalanGrowthWords m j).filter fun w => ∀ i : Fin m, i.val = 0 → w i = ℓ)

/-- **Area distribution of smooth words from $j$ to $j$.** For natural numbers $m$ and $j$, let
$\mathcal{T}_{m,j}$ be the set of words $w = w_1 \cdots w_m$ with letters in $\{1, \dots, j\}$
such that $w_1 = w_m = j$ and $|w_{i+1} - w_i| \le 1$ for $1 \le i < m$; in particular
$\mathcal{T}_{0,j}$ is empty. The area distribution of $\mathcal{T}_{m,j}$ is the polynomial
$t(m, j; q) = \sum_{w \in \mathcal{T}_{m,j}} q^{w_1 + \cdots + w_m}$ in $\mathbb{Z}[q]$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `𝒯_{m,j}` and
`t(m, j; q)`. -/
public noncomputable def smoothPlateauAreaDist (m j : ℕ) : ℤ[X] :=
  areaDist (wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    (∀ i : Fin m, i.val = 0 → w i = j) ∧
      ∀ i k : Fin m, k.val = i.val + 1 → w k ≤ w i + 1 ∧ w i ≤ w k + 1) j)

/-- **Capacity distribution at $q = 1$.** For every finite set $S$ of words of length $n$ with
letters in the natural numbers, the capacity distribution of $S$ evaluated at $q = 1$ equals the
number of words in $S$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public theorem capacityDist_eval_one {n : ℕ} (S : Finset (Fin n → ℕ)) :
    (capacityDist S).eval 1 = S.card := by
  simp [capacityDist, eval_finsetSum]

/-- **Area distribution at $q = 1$.** For every finite set $S$ of words of length $n$ with
letters in the natural numbers, the area distribution of $S$ evaluated at $q = 1$ equals the
number of words in $S$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public theorem areaDist_eval_one {n : ℕ} (S : Finset (Fin n → ℕ)) :
    (areaDist S).eval 1 = S.card := by
  simp [areaDist, eval_finsetSum]

/-- **Catalan and smooth words of length four.** There are $14$ Catalan words of length $4$,
$13$ smooth words of length $4$, and $7$ restricted smooth words of length $4$. Here $14$ is the
Catalan number $C_4$, $13 = C_4 - 1$, and $7$ is the central trinomial coefficient $G_3$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, examples. -/
public theorem card_catalanWords_four_smoothWords_four :
    (catalanWords 4).card = 14 ∧ (smoothWords 4).card = 13 ∧
      (restrictedSmoothWords 4).card = 7 := by
  decide

/-- **Recurrence for the area distribution by first letter.** For natural numbers $m$, $j$ and
$\ell$, let $c(m, j, \ell; q) \in \mathbb{Z}[q]$ be the area distribution of the words of length
$m$ with letters in $\{1, \dots, j\}$, each letter at most one more than the letter before it,
that begin with $\ell$ and end with $j$. For all natural numbers $m \ge 2$ and $j$, $\ell$ with
$1 \le \ell \le j$,
$$c(m, j, \ell; q) = q^{\ell} \sum_{i=1}^{\ell+1} c(m-1, j, i; q),$$
and $c(1, j, \ell; q)$ equals $q^{\ell}$ if $j = \ell$ and $0$ otherwise.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 1 (`integers-2025-A5-lem-1`). -/
public theorem_wanted catalanGrowthAreaDist_succ (m j ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 1 ≤ ℓ)
    (hℓj : ℓ ≤ j) :
    catalanGrowthAreaDist m j ℓ =
        X ^ ℓ * ∑ i ∈ Finset.Icc 1 (ℓ + 1), catalanGrowthAreaDist (m - 1) j i ∧
      catalanGrowthAreaDist 1 j ℓ = X ^ ℓ * if j = ℓ then 1 else 0

/-- **Denominator polynomials for the area of words with unit-bounded rises.** The polynomials
$d_j(x; q)$, viewed as formal power series in $x$ over $\mathbb{Z}[q]$, are defined by $d_0 = 1$,
$d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and
$d_j = (1 - xq^j)\, d_{j-1} - x^2 q^{2j-1} d_{j-3}$ for $j \ge 3$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3, recurrence (4). -/
public noncomputable def catalanGrowthDen : ℕ → PowerSeries ℤ[X]
  | 0 => 1
  | 1 => 1 - PowerSeries.C X * PowerSeries.X
  | 2 => 1 - PowerSeries.C X * PowerSeries.X - PowerSeries.C (X ^ 2) * PowerSeries.X
  | j + 3 => (1 - PowerSeries.C (X ^ (j + 3)) * PowerSeries.X) * catalanGrowthDen (j + 2) -
      PowerSeries.C (X ^ (2 * j + 5)) * PowerSeries.X ^ 2 * catalanGrowthDen j

/-- **The area denominators have constant term one.** For every $j \ge 0$, the power series
$d_j(x; q)$ in $x$ over $\mathbb{Z}[q]$ defined by $d_0 = 1$, $d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$
and $d_j = (1 - xq^j) d_{j-1} - x^2 q^{2j-1} d_{j-3}$ for $j \ge 3$ has constant term $1$.

Consequently every $d_j(x; q)$ is invertible as a power series in $x$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3, recurrence (4). -/
public theorem constantCoeff_catalanGrowthDen :
    ∀ j, PowerSeries.constantCoeff (catalanGrowthDen j) = 1
  | 0 => by simp [catalanGrowthDen]
  | 1 => by simp [catalanGrowthDen]
  | 2 => by simp [catalanGrowthDen]
  | j + 3 => by
    simp [catalanGrowthDen, constantCoeff_catalanGrowthDen (j + 2)]

/-- **Area generating function of words with unit-bounded rises, by first letter.** For natural
numbers $i$ and $j$ with $1 \le i \le j$ and for $n \ge 0$, let $c(n, j, i; q) \in \mathbb{Z}[q]$
be the area distribution of the words of length $n$ with letters in $\{1, \dots, j\}$, each letter
at most one more than the letter before it, that begin with $i$ and end with $j$: the sum of
$q^{\mathrm{area}(w)}$ over these words $w$, where $\mathrm{area}(w)$ is the sum of the letters
of $w$. Let $d_0, d_1, \dots$ be the power series in $x$ over $\mathbb{Z}[q]$ defined by
$d_0 = 1$, $d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and
$d_k = (1 - xq^k)\, d_{k-1} - x^2 q^{2k-1} d_{k-3}$ for $k \ge 3$; each $d_k$ has constant term
$1$, so it is invertible. Then, as formal power series in $x$ over $\mathbb{Z}[q]$,
$$\sum_{n \ge 0} c(n, j, i; q)\, x^n =
x^{j-i+1} q^{\binom{j+1}{2} - \binom{i}{2}}\, \frac{d_{i-1}(x; q)}{d_j(x; q)}.$$

The term for $n = 0$ is zero, since there are no words of length $0$ that end with $j$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3 (`integers-2025-A5-lem-3`). -/
public theorem_wanted catalanGrowthAreaDist_genFun (j i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    PowerSeries.mk (fun n => catalanGrowthAreaDist n j i) =
      PowerSeries.C (X ^ ((j + 1).choose 2 - i.choose 2)) * PowerSeries.X ^ (j - i + 1) *
        catalanGrowthDen (i - 1) * PowerSeries.invOfUnit (catalanGrowthDen j) 1

/-- **Area generating function of words with unit-bounded rises ending in their maximum.** For
natural numbers $n$ and $j$, let $\mathcal{C}_{n,j}$ be the set of words $w = w_1 \cdots w_n$ with
letters in $\{1, \dots, j\}$, each letter at most one more than the letter before it, and last
letter $j$, and let $c(n, j; q) \in \mathbb{Z}[q]$ be the sum of $q^{w_1 + \cdots + w_n}$ over
$w \in \mathcal{C}_{n,j}$. Let the formal power series $d_k(x; q)$ in $x$ over $\mathbb{Z}[q]$ be
defined by $d_0 = 1$, $d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and
$d_k = (1 - xq^k)\, d_{k-1} - x^2 q^{2k-1} d_{k-3}$ for $k \ge 3$. For every natural number
$j \ge 1$, in formal power series in $x$ over $\mathbb{Z}[q]$,
$$\sum_{n \ge 0} c(n, j; q)\, x^n =
\frac{1}{d_j(x; q)} \sum_{i=1}^{j} x^{j-i+1} q^{\binom{j+1}{2} - \binom{i}{2}} d_{i-1}(x; q).$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3 (`integers-2025-A5-lem-3`). -/
public theorem_wanted catalanGrowthWords_areaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun n => areaDist (catalanGrowthWords n j)) =
      PowerSeries.invOfUnit (catalanGrowthDen j) 1 *
        ∑ i ∈ Finset.Icc 1 j,
          PowerSeries.C (X ^ ((j + 1).choose 2 - i.choose 2)) * PowerSeries.X ^ (j - i + 1) *
            catalanGrowthDen (i - 1)

/-- **Dilating and inverting a power series.** For a natural number $j$ and a power series
$f(x; q) = \sum_{n \ge 0} f_n(q) x^n$ in $x$ over $\mathbb{Z}[q]$, the power series
$f(q^j x; 1/q)$ in $x$ over the Laurent polynomial ring $\mathbb{Z}[q, q^{-1}]$ is
$\sum_{n \ge 0} q^{jn} f_n(q^{-1}) x^n$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4. -/
public noncomputable def dilateInvertSeries (j : ℕ) (f : PowerSeries ℤ[X]) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n => T ((j * n : ℕ) : ℤ) * invert (toLaurent (PowerSeries.coeff n f))

/-- **Dilating and inverting a power series preserves constant term one.** For every natural
number $j$ and every power series $f(x; q)$ in $x$ over $\mathbb{Z}[q]$ with constant term $1$,
the power series $f(q^j x; 1/q)$ in $x$ over $\mathbb{Z}[q, q^{-1}]$ also has constant term $1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4. -/
public theorem constantCoeff_dilateInvertSeries (j : ℕ) (f : PowerSeries ℤ[X])
    (h : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (dilateInvertSeries j f) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, dilateInvertSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp

/-- **Generating function for the capacity of Catalan words ending in their largest letter.** For
natural numbers $n$ and $i$, let $b(n, i; q)$ be the capacity distribution of the Catalan words of
length $n$ that end in $i$ and have all letters at most $i$, viewed in $\mathbb{Z}[q, q^{-1}]$.
Let the formal power series $d_k(x; q)$ in $x$ over $\mathbb{Z}[q]$ be defined by $d_0 = 1$,
$d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and $d_k = (1 - xq^k)\, d_{k-1} - x^2 q^{2k-1} d_{k-3}$ for
$k \ge 3$. For a natural number $j$ and a power series $f(x; q)$ over $\mathbb{Z}[q]$ write
$f(q^j x; 1/q)$ for the series over $\mathbb{Z}[q, q^{-1}]$ whose coefficient of $x^n$ is
$q^{jn}$ times the coefficient of $x^n$ in $f$ with $q$ replaced by $q^{-1}$. For every natural
number $i \ge 1$, in formal power series in $x$ over $\mathbb{Z}[q, q^{-1}]$,
$$\sum_{n \ge 0} b(n, i; q)\, x^n = x^i \prod_{j=1}^{i} \Bigl(1 - x -
\frac{x}{d_{j-1}(q^j x; 1/q)} \sum_{m=1}^{j-1} x^{j-m} q^{j(j-m) + \binom{m}{2} - \binom{j}{2}}
d_{m-1}(q^j x; 1/q)\Bigr)^{-1}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4 (`integers-2025-A5-lem-4`). -/
public theorem_wanted catalanMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (catalanMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.Icc 1 i,
        PowerSeries.invOfUnit (1 - PowerSeries.X -
          PowerSeries.X *
            PowerSeries.invOfUnit (dilateInvertSeries j (catalanGrowthDen (j - 1))) 1 *
            ∑ m ∈ Finset.Icc 1 (j - 1),
              PowerSeries.C (T (((j * (j - m) + m.choose 2 : ℕ) : ℤ) - (j.choose 2 : ℕ))) *
                PowerSeries.X ^ (j - m) * dilateInvertSeries j (catalanGrowthDen (m - 1))) 1

/-- **Recurrence for the capacity distribution on Catalan words.** Write $a(n, i)$ for the
capacity distribution of the Catalan words of length $n$ ending in $i$, $b(n, i)$ for that of
those Catalan words of length $n$ ending in $i$ whose largest letter is $i$, and $c(m, j)$ for the
area distribution of the set $\mathcal{C}_{m,j}$ of words of length $m$ over $\{1, \dots, j\}$
ending in $j$ in which each letter is at most one more than the letter before it. For
$1 < i < n$, in the Laurent polynomial ring $\mathbb{Z}[q, q^{-1}]$,
$$
a(n,i) = b(n-1,i-1) + \sum_{j=i}^{n-1} a(n-1,j) +
\sum_{m=1}^{n-i-1} \sum_{j=i}^{n-m-1} q^{mi} \, a(n-m-1,j) \, c(m,i-1;1/q),
$$
where $c(m, i-1; 1/q)$ is the image of $c(m, i-1)$ under $q \mapsto q^{-1}$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (catalanCapacityDist n i) =
      toLaurent (catalanMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ j ∈ Finset.Icc i (n - 1), toLaurent (catalanCapacityDist (n - 1) j) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1), ∑ j ∈ Finset.Icc i (n - m - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (catalanCapacityDist (n - m - 1) j) *
            invert (toLaurent (areaDist (catalanGrowthWords m (i - 1))))

/-- **Recurrence for the capacity of Catalan words ending in their largest letter.** For natural
numbers $n$ and $i$, let $b(n, i; q)$ be the capacity distribution of the Catalan words of length
$n$ that end in $i$ and have all letters at most $i$. For natural numbers $m$ and $k$, let
$c(m, k; q) \in \mathbb{Z}[q]$ be the area distribution of the words of length $m$ with letters
in $\{1, \dots, k\}$, each letter at most one more than the letter before it, and last letter
$k$, and let $c(m, k; 1/q)$ be its image under $q \mapsto q^{-1}$. For all natural numbers $n$
and $i$ with $1 < i < n$, in $\mathbb{Z}[q, q^{-1}]$,
$$b(n, i; q) = b(n-1, i; q) + b(n-1, i-1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, b(n-m-1, i; q)\, c(m, i-1; 1/q).$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanMaxEndCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (catalanMaxEndCapacityDist n i) =
      toLaurent (catalanMaxEndCapacityDist (n - 1) i) +
        toLaurent (catalanMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (catalanMaxEndCapacityDist (n - m - 1) i) *
            invert (toLaurent (areaDist (catalanGrowthWords m (i - 1))))

/-- **Boundary values of the capacity distributions on Catalan words.** Write $a(n, i)$ for the
capacity distribution of the Catalan words of length $n$ ending in $i$, $b(n, i)$ for that of
those Catalan words of length $n$ ending in $i$ whose largest letter is $i$, and $a(n)$ for the
capacity distribution of all Catalan words of length $n$. For every $n \ge 1$,
$a(n, n) = b(n, 1) = b(n, n) = 1$, and if $n \ge 2$ then $a(n, 1) = a(n - 1)$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanCapacityDist_boundary (n : ℕ) (hn : 1 ≤ n) :
    (2 ≤ n → catalanCapacityDist n 1 = capacityDist (catalanWords (n - 1))) ∧
      catalanCapacityDist n n = 1 ∧ catalanMaxEndCapacityDist n 1 = 1 ∧
        catalanMaxEndCapacityDist n n = 1

/-- **Generating function of Catalan words by last letter.** Let $C(x) = \sum_{n \ge 0} C_n x^n$
be the generating function of the Catalan numbers $C_n$. For every $i \ge 1$, let $a_{n,i}$ be the
number of Catalan words of length $n$ whose last letter is $i$. Then, as formal power series with
integer coefficients, $\sum_{n \ge 0} a_{n,i} x^n = x^i C(x)^i$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 3 (`integers-2025-A5-cor-3`). -/
public theorem_wanted catalanWordsEndingIn_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => ((wordsEndingIn (catalanWords n) i).card : ℤ)) =
      PowerSeries.X ^ i * PowerSeries.mk (fun n => (catalan n : ℤ)) ^ i

/-- **Maximum capacity of Catalan words.** For every natural number $m$, the degree of the capacity
distribution $\sum_{w \in \mathcal{A}_n} q^{\operatorname{cap}(w)}$ of the set $\mathcal{A}_n$ of
Catalan words of length $n$, that is, the largest capacity of a Catalan word of length $n$, is
$3\binom{m}{2}$ for $n = 3m$, $m(3m-1)/2$ for $n = 3m + 1$ and $m(3m+1)/2$ for $n = 3m + 2$. The
case $m = 0$ is included.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 2 (`integers-2025-A5-thm-2`). -/
public theorem_wanted catalanWords_capacity_natDegree (m : ℕ) :
    (capacityDist (catalanWords (3 * m))).natDegree = 3 * m.choose 2 ∧
      (capacityDist (catalanWords (3 * m + 1))).natDegree = m * (3 * m - 1) / 2 ∧
        (capacityDist (catalanWords (3 * m + 2))).natDegree = m * (3 * m + 1) / 2

/-- **Number of Catalan words of maximum capacity.** For every $n \ge 4$, let $\mathcal{A}_n$ be
the set of Catalan words of length $n$. The leading coefficient of the capacity distribution
$\sum_{w \in \mathcal{A}_n} q^{\operatorname{cap}(w)}$ is $2$ if $3$ divides $n$ and $1$
otherwise; equivalently, exactly two Catalan words of length $n$ have the largest capacity when
$3 \mid n$, and exactly one does otherwise.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 4 (`integers-2025-A5-cor-4`). -/
public theorem_wanted catalanWords_capacity_leadingCoeff (n : ℕ) (hn : 4 ≤ n) :
    (capacityDist (catalanWords n)).leadingCoeff = if 3 ∣ n then 2 else 1

/-- **Subleading coefficient of the capacity distribution of Catalan words.** For every $n \ge 4$,
let $\mathcal{A}_n$ be the set of Catalan words of length $n$, let $\alpha$ be the degree of its
capacity distribution $\sum_{w \in \mathcal{A}_n} q^{\operatorname{cap}(w)}$, and let $d_n$ be the
coefficient of $q^{\alpha - 1}$ in it. Then $d_4 = 13$, $d_5 = 7$, $d_6 = 8$, and for $n \ge 7$,
$d_n = 2m$ if $n = 3m$, $d_n = m + 1$ if $n = 3m + 1$ and $d_n = m + 2$ if $n = 3m + 2$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 4 (`integers-2025-A5-cor-4`). -/
public theorem_wanted catalanWords_capacity_subleading_coeff (n : ℕ) (hn : 4 ≤ n) :
    (capacityDist (catalanWords n)).coeff ((capacityDist (catalanWords n)).natDegree - 1) =
      if n = 4 then 13 else if n = 5 then 7 else if n = 6 then 8
      else if n % 3 = 0 then 2 * (n / 3 : ℕ) else if n % 3 = 1 then (n / 3 : ℕ) + 1
      else (n / 3 : ℕ) + 2

/-- **Zero-capacity Catalan words with a given last letter.** For $2 \le i \le n$, let
$a(n, i; q)$ be the capacity distribution of the Catalan words of length $n$ ending in $i$, so that
$a(n, i; 0)$ is the number of those words with capacity $0$. Then
$$
a(n, i; 0) = \sum_{m=0}^{n-i} \binom{n-m-2}{i-2} F_{2m-1},
$$
where $F_k$ is the $k$-th Fibonacci number ($F_1 = F_2 = 1$) and $F_{-1} = 1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`). -/
public theorem_wanted catalanCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (catalanCapacityDist n i).eval 0 =
      ∑ m ∈ Finset.range (n - i + 1),
        (((n - m - 2).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) : ℕ) : ℤ)

/-- **Catalan words of capacity zero.** Let $F_k$ be the Fibonacci numbers, with $F_0 = 0$ and
$F_1 = 1$. For $n \ge 1$, let $a(n, 1; q)$ be the capacity distribution on Catalan words of length
$n$ ending in $1$, and let $a(n; q) = \sum_{w \in \mathcal{A}_n} q^{\operatorname{cap}(w)}$ be the
capacity distribution on the set $\mathcal{A}_n$ of all Catalan words of length $n$. Then
$a(n, 1; 0)$, the number of Catalan words of length $n$ ending in $1$ with capacity $0$, is $1$ if
$n = 1$ and $F_{2n-3}$ if $n \ge 2$, and $a(n; 0)$, the number of Catalan words of length $n$ with
capacity $0$, is $F_{2n-1}$.

The value $1$ for $n = 1$ is $F_{2n-3}$ under the convention $F_{-1} = 1$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`). -/
public theorem_wanted catalanWords_zero_capacity_count (n : ℕ) (hn : 1 ≤ n) :
    (catalanCapacityDist n 1).eval 0 = ((if n = 1 then 1 else Nat.fib (2 * n - 3) : ℕ) : ℤ) ∧
      (capacityDist (catalanWords n)).eval 0 = (Nat.fib (2 * n - 1) : ℤ)

/-- **Recurrence for the area distribution of smooth words from $j$ to $j$.** Let $t(m, j; q)$ be
the area distribution of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$
and whose consecutive letters differ by at most $1$. For all $m \ge 2$ and $j \ge 2$,
$$t(m, j; q) = q^j\, t(m-1, j; q) + q^j \sum_{\ell=1}^{m-2} t(\ell, j-1; q)\, t(m-\ell-1, j; q),$$
and for every $k \ge 1$, $t(k, 1; q) = t(1, k; q) = q^k$ (Mansour and Shattuck's Lemma 6).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 6 (`integers-2025-A5-lem-6`). -/
public theorem_wanted smoothPlateauAreaDist_recurrence (m j : ℕ) (hm : 2 ≤ m) (hj : 2 ≤ j) :
    smoothPlateauAreaDist m j =
        X ^ j * smoothPlateauAreaDist (m - 1) j +
          X ^ j * ∑ ℓ ∈ Finset.Icc 1 (m - 2),
            smoothPlateauAreaDist ℓ (j - 1) * smoothPlateauAreaDist (m - ℓ - 1) j ∧
      ∀ k : ℕ, 1 ≤ k → smoothPlateauAreaDist k 1 = X ^ k ∧ smoothPlateauAreaDist 1 k = X ^ k

/-- **Area polynomial of restricted smooth words between two top letters.** For natural numbers
$m$ and $j$, let $\mathcal{T}^*_{m,j}$ be the set of words $w = w_1 \cdots w_m$ over
$\{1, \dots, j\}$ with $w_1 = w_m = j$, $w_{k+1} \le w_k + 1$ and $w_k \le w_{k+1} + 1$ for
$1 \le k < m$, and no two adjacent letters both equal to $1$ (so $\mathcal{T}^*_{0,j}$ is empty).
Then $t^*(m, j; q)$ is the polynomial $\sum_{w \in \mathcal{T}^*_{m,j}} q^{w_1 + \cdots + w_m}$ in
$\mathbb{Z}[q]$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `t*(m, j; q)`. -/
public noncomputable def restrictedSmoothPlateauAreaDist (m j : ℕ) : ℤ[X] :=
  areaDist (wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    (∀ i : Fin m, i.val = 0 → w i = j) ∧
      ∀ i k : Fin m, k.val = i.val + 1 →
        w k ≤ w i + 1 ∧ w i ≤ w k + 1 ∧ ¬(w i = 1 ∧ w k = 1)) j)

/-- **Continued-fraction denominators.** Given a power series $B$ in $x$ over $\mathbb{Z}[q]$,
define power series $K_k$ in $x$ over $\mathbb{Z}[q]$ by $K_0 = 1$, $K_1 = B$ and, for $k \ge 2$,
$K_k = 1 - q^k x - q^{2k-1} x^2 K_{k-1}^{-1}$. Here $K_{k-1}^{-1}$ is the formal inverse of
$K_{k-1}$ computed with constant term $1$. It is the true inverse whenever $K_{k-1}$ has constant
term $1$, which always holds for $k \ge 3$, and for $k = 2$ when $B$ has constant term $1$.
Lemma 8 takes $B = 1 - qx$ and Lemma 10 takes $B = 1$; the value $K_0$ is unused.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemmas 8 and 10. -/
public noncomputable def capacityContinuedFractionDen (base : PowerSeries ℤ[X]) :
    ℕ → PowerSeries ℤ[X]
  | 0 => 1
  | 1 => base
  | k + 2 => 1 - PowerSeries.C (X ^ (k + 2)) * PowerSeries.X -
      PowerSeries.C (X ^ (2 * k + 3)) * PowerSeries.X ^ 2 *
        PowerSeries.invOfUnit (capacityContinuedFractionDen base (k + 1)) 1

/-- **Continued-fraction denominators have constant term one.** Let $B$ be a power series in $x$
over $\mathbb{Z}[q]$ with constant term $1$, and define power series $K_k$ in $x$ over
$\mathbb{Z}[q]$ by $K_0 = 1$, $K_1 = B$ and $K_k = 1 - q^k x - q^{2k-1} x^2 / K_{k-1}$ for
$k \ge 2$. Then $K_k$ has constant term $1$ for every $k \ge 0$.

Consequently every $K_k$ is invertible as a power series in $x$, and the inverses of $K_{k-1}$
used to define $K_k$ are genuine inverses.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemmas 8 and 10. -/
public theorem constantCoeff_capacityContinuedFractionDen (base : PowerSeries ℤ[X])
    (h : PowerSeries.constantCoeff base = 1) :
    ∀ k, PowerSeries.constantCoeff (capacityContinuedFractionDen base k) = 1
  | 0 => by simp [capacityContinuedFractionDen]
  | 1 => by simpa [capacityContinuedFractionDen] using h
  | k + 2 => by simp [capacityContinuedFractionDen]

/-- **Continued fraction for smooth words from $j$ to $j$ by area.** Let $t(m, j; q)$ be the area
distribution of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$ and whose
consecutive letters differ by at most $1$. Define power series $K_k$ in $x$ over $\mathbb{Z}[q]$ by
$K_1 = 1 - qx$ and $K_k = 1 - q^k x - q^{2k-1} x^2 / K_{k-1}$ for $k \ge 2$; each $K_k$ has constant
term $1$. Then for every $j \ge 1$, in $\mathbb{Z}[q][[x]]$,
$$\sum_{m \ge 0} t(m, j; q)\, x^m = \frac{q^j x}{K_j}.$$
This is Mansour and Shattuck's Lemma 8: $q^j x / K_j$ is the finite continued fraction
$q^j x / (1 - q^j x - q^{2j-1} x^2 / (1 - q^{j-1} x - \cdots / (1 - q^2 x - q^3 x^2 / (1 - qx))))$,
and for $j = 1$ it is $qx / (1 - qx)$. The term $m = 0$ vanishes.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 8 (`integers-2025-A5-lem-8`). -/
public theorem_wanted smoothPlateauAreaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun m => smoothPlateauAreaDist m j) =
      PowerSeries.C (X ^ j) * PowerSeries.X *
        PowerSeries.invOfUnit
          (capacityContinuedFractionDen (1 - PowerSeries.C X * PowerSeries.X) j) 1

/-- **Continued fraction for the area series of restricted smooth words.** For $j \ge 1$, let
$t^*(m, j; q) = \sum_w q^{w_1 + \cdots + w_m}$, the sum over the words $w = w_1 \cdots w_m$ over
$\{1, \dots, j\}$ with $w_1 = w_m = j$ (there are none for $m = 0$), consecutive letters
differing by at most $1$ and no two adjacent letters equal to $1$, and let
$T^*_j(x; q) = \sum_{m \ge 0} t^*(m, j; q)\, x^m$. Define power series $K_k$ in $x$ over
$\mathbb{Z}[q]$ by $K_1 = 1$ and $K_k = 1 - q^k x - q^{2k-1} x^2 / K_{k-1}$ for $k \ge 2$ (each
$K_k$ has constant term $1$, so the divisions are defined). Then
$$T^*_j(x; q) = \frac{q^j x}{K_j}.$$
For example, $T^*_1 = qx$ and $T^*_2 = q^2 x / (1 - q^2 x - q^3 x^2)$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 10 (`integers-2025-A5-lem-10`). -/
public theorem_wanted restrictedSmoothPlateauAreaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun m => restrictedSmoothPlateauAreaDist m j) =
      PowerSeries.C (X ^ j) * PowerSeries.X *
        PowerSeries.invOfUnit (capacityContinuedFractionDen 1 j) 1

/-- **Recurrence for the capacity distribution of smooth words by last letter.** Let $r(n, i; q)$
be the capacity distribution of the smooth words of length $n$ ending in $i$, let $s(n, i; q)$ be
that of those smooth words of length $n$ ending in $i$ whose largest letter is $i$, and let
$t(m, j; q)$ be the area distribution (the area of a word is the sum of its letters) of the words
of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$ and whose adjacent letters
differ by at most $1$. For $1 < i < n$, in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent
polynomials,
$$
r(n, i; q) = r(n - 1, i; q) + r(n - 1, i + 1; q) + s(n - 1, i - 1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, r(n - m - 1, i; q)\, t(m, i - 1; 1/q).
$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (smoothCapacityDist n i) =
      toLaurent (smoothCapacityDist (n - 1) i) + toLaurent (smoothCapacityDist (n - 1) (i + 1)) +
        toLaurent (smoothMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (smoothCapacityDist (n - m - 1) i) *
            invert (toLaurent (smoothPlateauAreaDist m (i - 1)))

/-- **Recurrence for the capacity distribution of smooth words ending in their largest letter.**
Let $s(n, i; q)$ be the capacity distribution of the smooth words of length $n$ that end in $i$ and
have largest letter $i$, and let $t(m, j; q)$ be the area distribution (the area of a word is the
sum of its letters) of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$
and whose adjacent letters differ by at most $1$. For $1 < i < n$, in the ring
$\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials,
$$
s(n, i; q) = s(n - 1, i; q) + s(n - 1, i - 1; q) +
\sum_{m=1}^{n-i-1} q^{mi}\, s(n - m - 1, i; q)\, t(m, i - 1; 1/q).
$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothMaxEndCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (smoothMaxEndCapacityDist n i) =
      toLaurent (smoothMaxEndCapacityDist (n - 1) i) +
        toLaurent (smoothMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (smoothMaxEndCapacityDist (n - m - 1) i) *
            invert (toLaurent (smoothPlateauAreaDist m (i - 1)))

/-- **Boundary values of the capacity distributions of smooth words.** For letters $i$, let
$r(n, i; q)$ be the capacity distribution of the smooth words of length $n$ ending in $i$, and
$s(n, i; q)$ that of those smooth words of length $n$ ending in $i$ whose largest letter is $i$.
For $n \ge 1$, $r(n, n; q) = s(n, n; q) = s(n, 1; q) = 1$, and if $n \ge 2$ then
$r(n, 1; q) = r(n - 1, 1; q) + r(n - 1, 2; q)$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothCapacityDist_boundary (n : ℕ) (hn : 1 ≤ n) :
    smoothCapacityDist n n = 1 ∧ smoothMaxEndCapacityDist n n = 1 ∧
      smoothMaxEndCapacityDist n 1 = 1 ∧
        (2 ≤ n → smoothCapacityDist n 1 =
          smoothCapacityDist (n - 1) 1 + smoothCapacityDist (n - 1) 2)

/-- **Generating function of smooth words ending in their largest letter.** For $i \ge 1$, let
$s(n, i; q)$ be the capacity distribution of the smooth words of length $n$ that end in $i$ and
have largest letter $i$, and let $t(m, j; q)$ be the area distribution (the area of a word is the
sum of its letters) of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$
and whose adjacent letters differ by at most $1$. In the ring of formal power series in $x$ over
the Laurent polynomials $\mathbb{Z}[q, q^{-1}]$,
$$
\sum_{n \ge 0} s(n, i; q)\, x^n = x^i \prod_{j=0}^{i-1}
\Bigl(1 - x - x \sum_{m \ge 0} q^{(j+1)m}\, t(m, j; 1/q)\, x^m\Bigr)^{-1}.
$$

The factor for $j = 0$ is $(1 - x)^{-1}$, since $t(m, 0; q) = 0$ for every $m$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 9 (`integers-2025-A5-lem-9`). -/
public theorem_wanted smoothMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (smoothMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.range i,
        PowerSeries.invOfUnit (1 - PowerSeries.X - PowerSeries.X * PowerSeries.mk fun m =>
          T (((j + 1) * m : ℕ) : ℤ) * invert (toLaurent (smoothPlateauAreaDist m j))) 1

/-- **Generating function for restricted smooth words ending in their largest letter.** For
$i \ge 1$, let $s^*(n, i; q)$ be the capacity distribution of the restricted smooth words of
length $n$ that end in $i$ and all of whose letters are at most $i$. For $j \ge 1$, let
$t^*(m, j; q) = \sum_w q^{w_1 + \cdots + w_m}$, the sum over the words $w = w_1 \cdots w_m$ over
$\{1, \dots, j\}$ with $w_1 = w_m = j$ (there are none for $m = 0$), consecutive letters
differing by at most $1$ and no two adjacent letters equal to $1$, and let
$T^*_j(q^{j+1} x; 1/q) = \sum_{m \ge 0} q^{(j+1)m}\, t^*(m, j; 1/q)\, x^m$. Then, in the ring of
formal power series in $x$ over $\mathbb{Z}[q, q^{-1}]$,
$$
\sum_{n \ge 0} s^*(n, i; q)\, x^n =
x^i \prod_{j=1}^{i-1} \frac{1}{1 - x - x\, T^*_j(q^{j+1} x; 1/q)},
$$
where each denominator has constant term $1$ and so is invertible.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 11 (`integers-2025-A5-lem-11`). -/
public theorem_wanted restrictedSmoothMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (restrictedSmoothMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.Icc 1 (i - 1),
        PowerSeries.invOfUnit (1 - PowerSeries.X - PowerSeries.X * PowerSeries.mk fun m =>
          T (((j + 1) * m : ℕ) : ℤ) * invert (toLaurent (restrictedSmoothPlateauAreaDist m j))) 1

/-- **Maximum capacity of smooth words.** A smooth word is a word of positive integers with first
letter $1$ whose consecutive letters differ by at most $1$. Let
$r(n; q) = \sum_w q^{\mathrm{cap}(w)}$, summed over the smooth words $w$ of length $n$, where
$\mathrm{cap}(w)$ is the capacity of $w$. For all $m \ge 1$ and $0 \le p \le 3$, the degree of
$r(4m + p; q)$ in $q$ is $m(2m + p - 1)$. Since $r(n; q)$ is a nonzero polynomial with
nonnegative coefficients, this degree is the maximum capacity of a smooth word of length
$4m + p$ (Mansour and Shattuck's Theorem 5).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 5 (`integers-2025-A5-thm-5`). -/
public theorem_wanted smoothWords_capacity_natDegree (m p : ℕ) (hm : 1 ≤ m) (hp : p ≤ 3) :
    (capacityDist (smoothWords (4 * m + p))).natDegree = m * (2 * m + p - 1)

/-- **Zero-capacity smooth words with a given last letter.** For $2 \le i \le n$, the number of
smooth words of length $n$ ending in $i$ with capacity $0$, that is, the value at $q = 0$ of their
capacity distribution $r(n, i; q)$, equals $\sum_{j=i-2}^{n-2} \binom{n-2}{j}$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 6 (`integers-2025-A5-thm-6`). -/
public theorem_wanted smoothCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (smoothCapacityDist n i).eval 0 = ∑ j ∈ Finset.Icc (i - 2) (n - 2), ((n - 2).choose j : ℤ)

/-- **Number of smooth words of capacity zero.** Let $r(n, i; q)$ be the capacity distribution of
the smooth words of length $n$ ending in $i$ and $r(n; q)$ that of all smooth words of length $n$,
so that $r(n, i; 0)$ and $r(n; 0)$ count the smooth words of capacity $0$. Then $r(1, 1; 0) = 1$
and $r(n, 1; 0) = 2^{n-2}$ for every $n \ge 2$; moreover $r(1; 0) = 1$, $r(2; 0) = 2$ and
$r(n; 0) = (n + 2) \cdot 2^{n-3}$ for every $n \ge 3$ (Mansour and Shattuck's Theorem 6, totals).

The paper states the formula for $r(n; 0)$ for $n \ge 2$; at $n = 2$ it reads $4 \cdot 2^{-1} = 2$,
so that case is stated separately.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 6 (`integers-2025-A5-thm-6`). -/
public theorem_wanted smoothWords_zero_capacity_count (n : ℕ) (hn : 2 ≤ n) :
    (smoothCapacityDist n 1).eval 0 = 2 ^ (n - 2) ∧ (smoothCapacityDist 1 1).eval 0 = 1 ∧
      (3 ≤ n → (capacityDist (smoothWords n)).eval 0 = (n + 2) * 2 ^ (n - 3)) ∧
        (capacityDist (smoothWords 2)).eval 0 = 2 ∧ (capacityDist (smoothWords 1)).eval 0 = 1

/-- **Maximum capacity of restricted smooth words.** Let $m \ge 0$ and $0 \le p \le 7$ with
$n = 8m + p \ge 1$. The degree of the capacity distribution of the restricted smooth words of
length $n$, that is, the largest capacity of a restricted smooth word of length $n$, equals
$8m^2 + (2p - 3)m + e_p$, where $e_p = 0$ for $p \le 3$, $e_4 = 1$ and $e_p = 2^{p-5}$ for
$5 \le p \le 7$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 9 (`integers-2025-A5-thm-9`). -/
public theorem_wanted restrictedSmoothWords_capacity_natDegree (m p : ℕ) (hp : p ≤ 7)
    (hn : 1 ≤ 8 * m + p) :
    ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) =
      8 * (m : ℤ) ^ 2 + (2 * (p : ℤ) - 3) * m +
        if p ≤ 3 then 0 else if p = 4 then 1 else 2 ^ (p - 5)

/-- **Number of restricted smooth words of maximum capacity.** Let $n = 8m + p \ge 1$ with
natural numbers $m$ and $p \le 7$, and let $c_n$ be the leading coefficient of the capacity
distribution $\sum_{w} q^{\mathrm{cap}(w)}$ over the restricted smooth words $w$ of length $n$
(smooth words with no two adjacent letters equal to $1$), that is, the number of restricted
smooth words of length $n$ with maximum capacity. If $m = 0$, then $c_1, \dots, c_7$ are
$1, 1, 3, 1, 5, 2, 1$. If $m \ge 1$, then $c_n = m + 1$ for $p \in \{0, 3\}$, $c_n = m + 3$ for
$p = 5$, $c_n = m + 2$ for $p = 6$ and $c_n = 1$ for $p \in \{1, 2, 4, 7\}$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 9 (`integers-2025-A5-thm-9`). -/
public theorem_wanted restrictedSmoothWords_capacity_leadingCoeff (m p : ℕ) (hp : p ≤ 7)
    (hn : 1 ≤ 8 * m + p) :
    (capacityDist (restrictedSmoothWords (8 * m + p))).leadingCoeff =
      if m = 0 then ([0, 1, 1, 3, 1, 5, 2, 1].getD p 0 : ℤ)
      else if p = 0 ∨ p = 3 then (m : ℤ) + 1 else if p = 5 then (m : ℤ) + 3
      else if p = 6 then (m : ℤ) + 2 else 1

/-- **Zero-capacity restricted smooth words with a given last letter.** For natural numbers $n$
and $i$ with $3 \le i \le n$, let $r^*(n, i; q)$ be the capacity distribution of the restricted
smooth words of length $n$ ending in $i$. Its value at $q = 0$, which is the number of such words
of capacity $0$, is
$$r^*(n, i; 0) = \sum_{j=i-3}^{n-3} \binom{n-3}{j}.$$

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 10 (`integers-2025-A5-thm-10`). -/
public theorem_wanted restrictedSmoothCapacityDist_eval_zero (n i : ℕ) (hi : 3 ≤ i)
    (hin : i ≤ n) :
    (restrictedSmoothCapacityDist n i).eval 0 =
      ∑ j ∈ Finset.Icc (i - 3) (n - 3), ((n - 3).choose j : ℤ)

/-- **Zero-capacity restricted smooth words.** For $n \ge 1$ and a letter $i$, let $r^{\ast}(n, i)$
be the number of restricted smooth words of length $n$ ending in $i$ that have capacity $0$, and
let $r^{\ast}(n)$ be the number of restricted smooth words of length $n$ with capacity $0$; these
are the values at $q = 0$ of the corresponding capacity distributions. Then $r^{\ast}(n, 1) = 1$
for $n \in \{1, 3\}$, $r^{\ast}(2, 1) = 0$ and $r^{\ast}(n, 1) = 2^{n-4}$ for $n \ge 4$;
$r^{\ast}(2, 2) = 1$ and $r^{\ast}(n, 2) = 2^{n-3}$ for $n \ge 3$; and $r^{\ast}(n) = 1$ for
$n \le 2$, $r^{\ast}(3) = 3$ and $r^{\ast}(n) = (n + 2)\, 2^{n-4}$ for $n \ge 4$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 10 (`integers-2025-A5-thm-10`). -/
public theorem_wanted restrictedSmoothWords_zero_capacity_count (n : ℕ) (hn : 1 ≤ n) :
    (restrictedSmoothCapacityDist n 1).eval 0 =
        (if n = 1 ∨ n = 3 then 1 else if n = 2 then 0 else 2 ^ (n - 4)) ∧
      (2 ≤ n → (restrictedSmoothCapacityDist n 2).eval 0 = if n = 2 then 1 else 2 ^ (n - 3)) ∧
        (capacityDist (restrictedSmoothWords n)).eval 0 =
          if n ≤ 2 then 1 else if n = 3 then 3 else (n + 2) * 2 ^ (n - 4)

/-- **Restricted smooth words are counted by grand Motzkin numbers.** For every $n \ge 1$, the
number of restricted smooth words of length $n$ is the grand Motzkin number $G_{n-1}$, that is,
the central trinomial coefficient: the coefficient of $X^{n-1}$ in $(1 + X + X^2)^{n-1}$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 11 (`integers-2025-A5-thm-11`). -/
public theorem_wanted card_restrictedSmoothWords (n : ℕ) (hn : 1 ≤ n) :
    (restrictedSmoothWords n).card = trinomialCoefficient (n - 1) (n - 1)

end

end MetaMathlibExt
