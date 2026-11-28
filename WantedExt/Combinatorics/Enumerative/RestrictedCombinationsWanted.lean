/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian
public import MathlibExt.Combinatorics.Enumerative.FenceTiling
public import MathlibExt.Combinatorics.Enumerative.RestrictedCombinations
public import MathlibExt.Combinatorics.Enumerative.RestrictedCombinationsWellBased
public import MathlibExt.Combinatorics.Enumerative.RestrictedPermutationsMultiples
public import MathlibExt.Combinatorics.Enumerative.SubwordShiftSet
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP

/-!
# Combinations without specified separations

Statements from Michael A. Allen, *Connections Between Combinations Without Specified
Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of
Integer Sequences 28 (2025), Article 25.3.7 (arXiv:2409.00624v4).

`restrictedCombinationCount Q n k` is the paper's `S^Q_{n,k}`: the number of `k`-subsets of
`{1, …, n}` in which no two elements differ by an element of `Q`; `restrictedCombinationTotal Q n`
is `S^Q_n`. Permutations of `ℕ_n = {1, …, n}` are modelled as permutations of `Fin n`
(0-based positions; only differences `π(i) - i` and excedances matter, so the shift is
harmless). Most bijection statements are recorded as equalities of cardinalities, which is
equivalent for finite sets. Lemma 12 (`fenceTiling_strongPerm_bijection`) states the explicit
correspondence instead: a compatibility relation between tilings and permutations that is
functional in both directions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Restricted combinations with no forbidden differences.** For all natural numbers $n$ and
$k$, the number $S^{\emptyset}_{n,k}$ of $k$-subsets of $\{1, \dots, n\}$ in which no two
elements differ by an element of the empty set is the binomial coefficient $\binom{n}{k}$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedCombinationCount_empty (n k : ℕ) :
    restrictedCombinationCount ∅ n k = n.choose k := by
  unfold restrictedCombinationCount restrictedCombinations
  rw [Finset.filter_true_of_mem (fun s _ => by simp), Finset.card_powersetCard, Nat.card_Icc,
    Nat.add_sub_cancel]

/-- **Subsets of $\{1, 2, 3, 4\}$ with no two consecutive elements.** There are exactly $8$
subsets of $\{1, 2, 3, 4\}$ in which no two elements differ by $1$.

This is the case $n = 4$ of the identity $S^{\{1\}}_n = F_{n+2}$, where $S^{\{1\}}_n$ is the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ and $F_m$ is the
$m$-th Fibonacci number ($F_1 = F_2 = 1$): $F_6 = 8$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1 (`S^{1}_n = F_{n+2}`). -/
public theorem restrictedCombinationTotal_singleton_one_four :
    restrictedCombinationTotal {1} 4 = 8 := by
  decide

/-- **Forbidden differences 1 and q and windowed adjacent-swap permutations.** For all natural
numbers $q$, $n$ and $k$, the number of $k$-subsets of $\{1, \dots, n\}$ in which no two
distinct elements differ by $1$ or by $q$ equals the number of permutations $\pi$ of
$\{0, 1, \dots, n\}$ such that $|\pi(i) - i| \le 1$ for every $i$; for every $i_0 \ge 0$ with
$i_0 + q \le n + 1$, all $i, j$ with $i_0 \le i, j < i_0 + q$ satisfy
$\pi(i) \le \pi(j) + q$ (every window of $q$ consecutive values has maximum minus minimum
at most $q$); and $\pi$ has exactly $k$ excedances (points $i$ with $\pi(i) > i$).

The paper takes $q \ge 2$; for $q \le 1$ the statement reduces to the case $Q = \{1\}$. The
condition $|\pi(i) - i| \le 1$ cannot be dropped: for $q = n = 2$ all $6$ permutations of
$\{0, 1, 2\}$ satisfy the window condition, while only $3$ subsets of $\{1, 2\}$ have no two
elements differing by $1$ or $2$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 8. -/
public theorem_wanted restrictedCombinationCount_one_q_eq_card_windowedAdjacentSwapPerms
    (q n k : ℕ) :
    restrictedCombinationCount {1, q} n k =
      Nat.card {π : Equiv.Perm (Fin (n + 1)) //
        (∀ i : Fin (n + 1), (π i : ℕ) ≤ i + 1 ∧ (i : ℕ) ≤ π i + 1) ∧
        (∀ i₀ < n + 2 - q, ∀ i j : Fin (n + 1), i₀ ≤ (i : ℕ) → (i : ℕ) < i₀ + q →
          i₀ ≤ (j : ℕ) → (j : ℕ) < i₀ + q → (π i : ℕ) ≤ π j + q) ∧
        excedanceCount (n + 1) π = k}

/-- **Generating function for subsets avoiding differences 1 and 6.** Let $S^{\{1,6\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $6$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,6\}}_n x^n\Bigr)
(1 - x - x^4 - x^5 + 2x^6 - 4x^7 + 2x^8 - 2x^{10} + 2x^{11} - 4x^{12} + 3x^{13} - x^{14} +
2x^{16} - x^{17} + x^{18}) =
1 + x + x^2 + 2x^3 + 2x^4 + 2x^5 + 5x^6 + 3x^8 + 2x^9 - x^{10} + x^{11} - 4x^{12} - x^{13} -
2x^{14} - 2x^{15} - x^{17}.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,6\}}_n x^n$ as a quotient of a polynomial
of degree $17$ by a polynomial of degree $18$, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 11. -/
public theorem_wanted restrictedCombinationTotal_one_six_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 6} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 -
          4 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 10 +
          2 * PowerSeries.X ^ 11 - 4 * PowerSeries.X ^ 12 + 3 * PowerSeries.X ^ 13 -
          PowerSeries.X ^ 14 + 2 * PowerSeries.X ^ 16 - PowerSeries.X ^ 17 +
          PowerSeries.X ^ 18) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        2 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 + 3 * PowerSeries.X ^ 8 +
        2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10 + PowerSeries.X ^ 11 -
        4 * PowerSeries.X ^ 12 - PowerSeries.X ^ 13 - 2 * PowerSeries.X ^ 14 -
        2 * PowerSeries.X ^ 15 - PowerSeries.X ^ 17

/-- **Forbidden differences m, 2m, …, jm and strongly restricted permutations.** For natural
numbers $m \ge 1$, $j \ge 1$, $n$ and $k$, the number of $k$-subsets of $\{1, \dots, n\}$ in
which no two elements differ by an element of $\{m, 2m, \dots, jm\}$ equals the number of
permutations $\pi$ of $\{0, 1, \dots, n + jm - 1\}$ such that $\pi(i) - i \in \{-m, 0, jm\}$ for
every $i$ and $\pi$ has exactly $k$ excedances (points $i$ with $\pi(i) > i$).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 13. -/
public theorem_wanted restrictedCombinationCount_multiples_eq_card_strongPerms
    (m j n k : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) :
    restrictedCombinationCount ((Finset.Icc 1 j).image fun u => u * m) n k =
      Nat.card {π : Equiv.Perm (Fin (n + j * m)) //
        (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
        excedanceCount (n + j * m) π = k}

/-- **The $(1,t)$-bonacci polynomials.** Fix a natural number $s$ and put $t = s + 1$. The
$(1,t)$-bonacci polynomials $f^{(t)}_n(x)$, $n \ge 0$, are the polynomials with natural-number
coefficients defined by $f^{(t)}_0(x) = 1$ and, for every $n \ge 0$,
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x) + x \, f^{(t)}_{n-s}(x)$ if $s \le n$ and
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x)$ if $n < s$.

Equivalently, $f^{(t)}_n(x) = f^{(t)}_{n-1}(x) + x \, f^{(t)}_{n-t}(x) + \delta_{n,0}$ with
$f^{(t)}_n(x) = 0$ for $n < 0$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public noncomputable def oneTBonacciPolynomial (s : ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 =>
    oneTBonacciPolynomial s n +
      Polynomial.X * (if s ≤ n then oneTBonacciPolynomial s (n - s) else 0)
termination_by n => n
decreasing_by all_goals omega

/-- **Initial value of the $(1,t)$-bonacci polynomials.** For every natural number $s$, the
$(1,s+1)$-bonacci polynomial of index $0$ is $f^{(s+1)}_0(x) = 1$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_zero (s : ℕ) : oneTBonacciPolynomial s 0 = 1 := by
  rw [oneTBonacciPolynomial]

/-- **Recurrence for the $(1,t)$-bonacci polynomials.** For all natural numbers $s$ and $n$ with
$s \le n$, the $(1,s+1)$-bonacci polynomials $f^{(s+1)}_m(x)$, $m \ge 0$, satisfy
$f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x) + x \, f^{(s+1)}_{n-s}(x)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_le (s n : ℕ) (h : s ≤ n) :
    oneTBonacciPolynomial s (n + 1) =
      oneTBonacciPolynomial s n + Polynomial.X * oneTBonacciPolynomial s (n - s) := by
  rw [oneTBonacciPolynomial]
  simp [h]

/-- **The $(1,t)$-bonacci polynomials below the recurrence range.** For all natural numbers $s$
and $n$ with $n < s$, the $(1,s+1)$-bonacci polynomials $f^{(s+1)}_m(x)$, $m \ge 0$, satisfy
$f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_lt (s n : ℕ) (h : n < s) :
    oneTBonacciPolynomial s (n + 1) = oneTBonacciPolynomial s n := by
  rw [oneTBonacciPolynomial]
  simp [show ¬ s ≤ n by omega]

/-- **Excedances of strongly restricted permutations with displacements $-m$, $0$, $jm$.** Let
$m, j, i, r, k$ be natural numbers with $j \ge 1$ and $r < m$, and let $f_n(x)$ be the
$(1, j+1)$-bonacci polynomials with natural-number coefficients: $f_0(x) = 1$, and
$f_{n+1}(x) = f_n(x) + x f_{n-j}(x)$ if $n \ge j$, $f_{n+1}(x) = f_n(x)$ if $n < j$. Then the
number of permutations $\pi$ of $\{0, 1, \dots, im + r - 1\}$ with $\pi(a) - a \in \{-m, 0, jm\}$
for every $a$ and with exactly $k$ excedances (points $a$ with $\pi(a) > a$) equals the
coefficient of $x^k$ in $f_i(x)^{m-r} f_{i+1}(x)^r$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem_wanted card_strongPerms_multiples_excedance_eq_coeff
    (m j i r k : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        (∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
        excedanceCount (i * m + r) π = k} =
      ((oneTBonacciPolynomial j i) ^ (m - r) * (oneTBonacciPolynomial j (i + 1)) ^ r).coeff k

/-- **Combinations avoiding an interval of differences with one value removed.** Let $p$, $q$
and $n$ be natural numbers with $p < q < 2p$, let $Q = \{1, \dots, q\} \setminus \{p\}$, and let
$S^Q_n$ be the number of subsets of $\{1, \dots, n\}$ in which no two elements differ by an
element of $Q$. Then $S^Q_n$ is the number of compositions of $n + q$ in which every part is
either $1$ or of the form $q + 1 + jp$ for some integer $j \ge 0$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 19. -/
public theorem_wanted restrictedCombinationTotal_Icc_erase_eq_card_compositions
    (p q n : ℕ) (hpq : p < q) (hqp : q < 2 * p) :
    restrictedCombinationTotal ((Finset.Icc 1 q).erase p) n =
      Nat.card {c : Composition (n + q) //
        ∀ b ∈ c.blocks, b = 1 ∨ (q + 1 ≤ b ∧ p ∣ b - (q + 1))}

/-- **Two dominoes on a 4-board.** For $Q = \{1\}$ the $Q$-comb is a domino, and the number
$B^{\{1\}}_{4,2}$ of restricted-overlap tilings of a $4$-board with squares and two $Q$-combs is
$1$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedOverlapTilingCount_singleton_one_four_two :
    restrictedOverlapTilingCount {1} 4 2 = 1 := by
  decide

/-- **Two interlocking $\{2\}$-combs on a 4-board.** For $Q = \{2\}$, there is exactly one
restricted-overlap tiling of a $4$-board with squares and two $Q$-combs.

Here the $Q$-comb has length $3$, with teeth in cells $0$ and $2$ and a gap in cell $1$; in
the unique tiling the two combs start in cells $0$ and $1$ and interlock.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedOverlapTilingCount_singleton_two_four_two :
    restrictedOverlapTilingCount {2} 4 2 = 1 := by
  decide

/-- **Metatiles with at most two combs.** Let $Q$ be a finite set of natural numbers and $q$ its
largest element ($q = 0$ for $Q = \emptyset$). The set $Q$ has metatiles with at most two combs
if for all natural numbers $N$ and $k$ and every restricted-overlap tiling of an $N$-board with
squares and $k$ $Q$-combs, with set $P$ of comb start cells, any three combs $a < b < c$ in $P$
are separated by a boundary: there is a natural number $j$ with $a < j \le c$ such that no comb
$s \in P$ satisfies $s < j \le s + q$.

A metatile is a gapless grouping of tiles that cannot be split into smaller gapless groupings.
The boundary before cell $j$ separates two metatiles exactly when no tile straddles it, that is,
when no comb $s \in P$ has $s < j \le s + q$ (squares never straddle a boundary). So the
condition says that every metatile of every such tiling contains at most two combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1 (metatiles) and Lemma 15. -/
public def MetatilesHaveAtMostTwoCombs (Q : Finset ℕ) : Prop :=
  ∀ N k, ∀ P ∈ restrictedOverlapTilings Q N k, ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a < b → b < c →
    ∃ j, a < j ∧ j ≤ c ∧ ∀ s ∈ P, ¬ (s < j ∧ j ≤ s + Q.sup id)

/-- **For $Q = \emptyset$, metatiles have at most two combs.** For $Q = \emptyset$, every metatile
of every restricted-overlap tiling with squares and $Q$-combs contains at most two combs.

Here the $Q$-comb is a single cell, so no tile straddles a cell boundary and every metatile is a
single tile.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem metatilesHaveAtMostTwoCombs_empty : MetatilesHaveAtMostTwoCombs ∅ := by
  intro N k P _ a _ b _ c _ hab hbc
  exact ⟨c, by omega, le_rfl, fun s _ h => by simp at h; omega⟩

/-- **For $Q = \{3\}$, a metatile can contain three combs.** For $Q = \{3\}$ it is not true that
every metatile of every restricted-overlap tiling with squares and $Q$-combs contains at most
two combs.

Here the $Q$-comb is a $(1,2,1)$-comb, and combs starting at cells $0, 1, 2$ of a $6$-board form
a single metatile with three combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem not_metatilesHaveAtMostTwoCombs_three : ¬ MetatilesHaveAtMostTwoCombs {3} := by
  intro h
  obtain ⟨j, hj0, hj2, hj⟩ := h 6 3 {0, 1, 2} (by decide) 0 (by simp) 1 (by simp) 2 (by simp)
    (by omega) (by omega)
  exact hj 0 (by simp) ⟨hj0, by simp; omega⟩

/-- **Restricted combinations counted by compositions.** Let $Q$ be a finite set of natural
numbers whose largest element $q$ is positive, and let $S^Q_n$ be the number of subsets of
$\{1, \dots, n\}$ in which no two elements differ by an element of $Q$. Then the following are
equivalent: (i) there is a finite set $A$ of natural numbers such that, for every $n \ge 0$,
$S^Q_n$ is the number of compositions of $n + q$ with all parts in $A$; (ii) every metatile of
every restricted-overlap tiling with squares and $Q$-combs contains at most two combs.
Moreover, if (ii) holds, then for every $n \ge 0$, $S^Q_n$ is the number of compositions of
$n + q$ in which every part is $1$, $q + 1$, or $q + 1 + p$ for some
$p \in \{1, \dots, q\} \setminus Q$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Lemma 15. -/
public theorem_wanted restrictedCombinationTotal_eq_card_compositions_iff_metatiles
    (Q : Finset ℕ) (hq : 0 < Q.sup id) :
    ((∃ A : Finset ℕ, ∀ n, restrictedCombinationTotal Q n =
        Nat.card {c : Composition (n + Q.sup id) // ∀ b ∈ c.blocks, b ∈ A}) ↔
      MetatilesHaveAtMostTwoCombs Q) ∧
    (MetatilesHaveAtMostTwoCombs Q → ∀ n, restrictedCombinationTotal Q n =
      Nat.card {c : Composition (n + Q.sup id) // ∀ b ∈ c.blocks,
        b = 1 ∨ b = Q.sup id + 1 ∨ ∃ p ∈ Finset.Icc 1 (Q.sup id) \ Q, b = Q.sup id + 1 + p})

end

end MetaMathlibExt
