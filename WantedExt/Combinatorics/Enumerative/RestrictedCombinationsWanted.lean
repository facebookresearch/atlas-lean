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

/-- **Restricted combinations.** For a finite set $Q$ of natural numbers and $n, k \ge 0$, the
restricted combinations are the $k$-element subsets $s$ of $\{1, \dots, n\}$ such that
$b - a \notin Q$ for all $a, b \in s$ with $a < b$. Since only distinct elements are compared,
whether $0 \in Q$ makes no difference.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinations (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powersetCard k).filter fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q

/-- **Number of restricted combinations.** For a finite set $Q$ of natural numbers and natural
numbers $n$ and $k$, $S^Q_{n,k}$ is the number of $k$-subsets of $\{1, \dots, n\}$ in which no
two distinct elements differ by an element of $Q$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedCombinations Q n k).card

/-- **Number of subsets avoiding a set of differences.** For a finite set $Q$ of natural numbers
and $n \ge 0$, $S^Q_n$ is the number of subsets of $\{1, \dots, n\}$ in which no two distinct
elements differ by an element of $Q$. That is, $S^Q_n = \sum_{k=0}^{n} S^Q_{n,k}$, where
$S^Q_{n,k}$ is the number of such subsets with $k$ elements.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationTotal (Q : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), restrictedCombinationCount Q n k

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

/-- **Generating function for subsets avoiding differences 1 and 4.** Let $S^{\{1,4\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $4$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,4\}}_n x^n\Bigr)(1 - x - x^3 + x^4 - 2x^5 + x^6 - x^7) =
1 + x + x^2 + x^3 + 2x^4 + x^6.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,4\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 9. -/
public theorem_wanted restrictedCombinationTotal_one_four_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 4} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 +
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        PowerSeries.X ^ 6

/-- **Generating function for subsets avoiding differences 1 and 5.** Let $S^{\{1,5\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $5$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,5\}}_n x^n\Bigr)
(1 - x^2 - x^3 - x^4 + x^5 - x^6 - x^7 - x^8 - x^{10}) =
1 + 2x + 2x^2 + 2x^3 + 2x^4 + 4x^5 + 3x^6 + 2x^7 + x^8 + x^9.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,5\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 10. -/
public theorem_wanted restrictedCombinationTotal_one_five_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 5} n : ℤ)) *
        (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 -
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7 - PowerSeries.X ^ 8 - PowerSeries.X ^ 10) =
      1 + 2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6 +
        2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 + PowerSeries.X ^ 9

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

/-- **Counting strongly restricted permutations with displacements $-m$, $0$, $jm$.** Let
$m, j, i, r$ be natural numbers with $j \ge 1$ and $r < m$, and let $F_j$ be the Fibonacci
$j$-numbers: $F_j(0) = 0$, $F_j(n) = 1$ for $1 \le n \le j$, and
$F_j(n) = F_j(n-1) + F_j(n-j-1)$ for $n > j$. Then the number of permutations $\pi$ of
$\{0, 1, \dots, im + r - 1\}$ such that $\pi(x) - x \in \{-m, 0, jm\}$ for every $x$ equals
$F_j(i+1)^{m-r} \, F_j(i+2)^r$.

In the paper's notation this is
$P^{\{-m,0,jm\}}_{im+r} = (f^{(j+1)}_i)^{m-r} (f^{(j+1)}_{i+1})^r$, where the
$(1,t)$-bonacci numbers $f^{(t)}_n$ satisfy $f^{(j+1)}_n = F_j(n+1)$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem_wanted card_strongPerms_multiples_eq_fibonacciP
    (m j i r : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)} =
      fibonacciP j (i + 1) ^ (m - r) * fibonacciP j (i + 2) ^ r

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

/-- **Well-based sets.** A finite set $Q$ of natural numbers is well based (Kitaev;
Valyuzhenich) if for every $x \in Q$ and every natural number $a$ with $0 < a < x$, at least one
of $a$ and $x - a$ lies in $Q$.

The empty set is well based, as in the paper's equivalent formulation. For a nonempty set $Q$
of positive integers the condition forces $1 \in Q$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public def IsWellBased (Q : Finset ℕ) : Prop :=
  ∀ x ∈ Q, ∀ a, 0 < a → a < x → a ∈ Q ∨ x - a ∈ Q

/-- **The set $\{1, \dots, q\}$ is well based.** For every natural number $q$, the set
$\{1, 2, \dots, q\}$ is well based.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem isWellBased_Icc (q : ℕ) : IsWellBased (Finset.Icc 1 q) := by
  intro x hx a ha hax
  left
  simp only [Finset.mem_Icc] at hx ⊢
  omega

/-- **The set $\{1, 3, 4\}$ is not well based.** The set $\{1, 3, 4\}$ is not well based: in
$4 = 2 + 2$ neither part lies in the set.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem not_isWellBased_one_three_four : ¬ IsWellBased {1, 3, 4} := by
  intro h
  have := h 4 (by simp) 2 (by norm_num) (by norm_num)
  simp at this

/-- **Shift set of a binary subword.** For natural numbers $\omega$ and $l$, the shift set of
$\omega$ with length $l$ is the set of $j \in \{1, \dots, l - 1\}$ with
$\lfloor \omega / 2^j \rfloor \ne \omega \bmod 2^{l-j}$. When $\omega < 2^l$ is read as a binary
word of length $l$, this says that the leftmost $l - j$ bits of $\omega$ differ from its rightmost
$l - j$ bits.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 21. -/
public def subwordShiftSet (ω l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (l - 1)).filter fun j => ω / 2 ^ j ≠ ω % 2 ^ (l - j)

/-- **Shift set of the subword 1010.** The shift set of the binary subword $1010$ of length $4$
(the number $10$) is $\{1, 3\}$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1 (OEIS list after Theorem 21). -/
public theorem subwordShiftSet_1010 : subwordShiftSet 0b1010 4 = {1, 3} := by
  decide

/-- **Subword shift sets are well based.** Let $l$ be a natural number and $\omega$ a binary word
of length $l$, read as a natural number $\omega < 2^l$. Then the set $Q$ of those
$j \in \{1, \dots, l-1\}$ for which the leftmost $l - j$ bits of $\omega$ differ from its
rightmost $l - j$ bits, that is $\lfloor \omega / 2^j \rfloor \ne \omega \bmod 2^{l-j}$, is well
based.

This is the well-based part of Theorem 22 of the paper. Its further claim, that no integer
linear combination of the elements $p_i$ of $\{1, \dots, q\} \setminus Q$ lies in $Q$ (with $q$
the largest element of $Q$), is omitted: for $\omega = 010100101$ and $l = 9$ one gets
$Q = \{1, 2, 3, 4, 6, 8\}$, $q = 8$, $p_1 = 5$, $p_2 = 7$, and $p_2 - p_1 = 2 \in Q$. The side
condition $q = l - 1$ of Theorem 21 is not needed.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 22. -/
public theorem_wanted isWellBased_subwordShiftSet (ω l : ℕ) (hω : ω < 2 ^ l) :
    IsWellBased (subwordShiftSet ω l)

/-- **Bivariate generating function for well-based forbidden differences.** Let $Q$ be a finite
set of positive integers that is well based, and write $S^Q_{n,k}$ for the number of $k$-subsets
of $\{1, \dots, n\}$ in which no two elements differ by an element of $Q$. In the ring
$\mathbb{Z}[y][[x]]$ of formal power series in $x$ with coefficients in $\mathbb{Z}[y]$, let
$g(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} \, y^k x^n$ and
$c = 1 + \sum_{q \in Q} x^q y$. Then $g(x, y) \, \bigl((1 - x) \, c - x y\bigr) = c$; since
$(1 - x) c - x y$ has constant term $1$, this says $g = c / ((1 - x) c - x y)$.

The empty set counts as well based, so the case $Q = \emptyset$, where $g = 1/(1 - x - xy)$,
is included.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 24. -/
public theorem_wanted restrictedCombination_bivariate_genFun_of_isWellBased
    (Q : Finset ℕ) (hQ0 : 0 ∉ Q) (hQ : IsWellBased Q) :
    PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) *
        ((1 - PowerSeries.X) *
            (1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X) -
          PowerSeries.X * PowerSeries.C Polynomial.X) =
      1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X

/-- **Restricted-overlap tilings.** Let $Q$ be a finite set of natural numbers and let $q$ be its
largest element ($q = 0$ if $Q$ is empty). The $Q$-comb is a piece of length $q + 1$ whose cell
$0$ and cells $j \in Q$ are teeth and whose other cells are gaps. A restricted-overlap tiling of an
$n$-board (cells $0, \dots, n - 1$) with squares and $k$ $Q$-combs is recorded by the set $P$ of
the start cells of its combs, with squares filling the cells that no tooth covers. The
restricted-overlap tilings are the $k$-element sets $P$ of natural numbers $s$ with $s + q < n$
(each comb fits on the board) such that $s \ne s' + j$ for all $s, s' \in P$ and all nonzero
$j \in Q$ (no comb's leftmost cell is covered by a non-leftmost tooth of another comb).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilings (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  (((Finset.range n).filter fun s => s + Q.sup id < n).powersetCard k).filter
    fun P => ∀ s ∈ P, ∀ s' ∈ P, ∀ j ∈ Q, j ≠ 0 → s ≠ s' + j

/-- **Number of restricted-overlap tilings.** For a finite set $Q$ of natural numbers and natural
numbers $n$ and $k$, $B^Q_{n,k}$ is the number of restricted-overlap tilings of an $n$-board with
squares and $k$ $Q$-combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilingCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedOverlapTilings Q n k).card

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

/-- **Restricted combinations and restricted-overlap tilings.** Let $Q$ be a finite set of
natural numbers and let $q$ be its largest element ($q = 0$ if $Q$ is empty). Write
$S^Q_{n,k}$ for the number of $k$-subsets of $\{1, \dots, n\}$ in which no two distinct
elements differ by an element of $Q$, $S^Q_n = \sum_{k=0}^{n} S^Q_{n,k}$, and $B^Q_{m,k}$ for
the number of restricted-overlap tilings of an $m$-board with squares and $k$ $Q$-combs. Then
for all natural numbers $n$ and $k$, $S^Q_{n,k} = B^Q_{n+q,k}$ and
$S^Q_n = \sum_{j=0}^{n+q} B^Q_{n+q,j}$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 1. -/
public theorem_wanted restrictedCombinationCount_eq_restrictedOverlapTilingCount
    (Q : Finset ℕ) (n k : ℕ) :
    restrictedCombinationCount Q n k = restrictedOverlapTilingCount Q (n + Q.sup id) k ∧
      restrictedCombinationTotal Q n = ∑ j ∈ Finset.range (n + Q.sup id + 1),
        restrictedOverlapTilingCount Q (n + Q.sup id) j

/-- **Generating functions of restricted combinations and restricted-overlap tilings.** Let $Q$
be a finite set of natural numbers and let $q$ be its largest element ($q = 0$ if $Q$ is empty).
Write $S^Q_{n,k}$ for the number of $k$-subsets of $\{1, \dots, n\}$ in which no two elements
differ by an element of $Q$, and $B^Q_{n,k}$ for the number of restricted-overlap tilings of an
$n$-board with squares and $k$ $Q$-combs. In the ring $\mathbb{Z}[y][[x]]$ of power series in
$x$ with coefficients in $\mathbb{Z}[y]$, let
$g^Q(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} x^n y^k$ and
$G(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} B^Q_{n,k} x^n y^k$. Then
$$x^q g^Q(x, y) = G(x, y) - \sum_{n=0}^{q-1} x^n.$$

This is the paper's formula $g^Q = \bigl(G - (1 - x^q)/(1 - x)\bigr)/x^q$ with the denominators
cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 7. -/
public theorem_wanted restrictedCombination_genFun_eq_tiling_genFun (Q : Finset ℕ) :
    PowerSeries.X ^ Q.sup id * PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) =
      PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedOverlapTilingCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) -
        ∑ n ∈ Finset.range (Q.sup id), PowerSeries.X ^ n

/-- **Fence tilings and strongly restricted permutations.** Let $D$ be a finite set of integers
and $n$ a natural number. Number the cells of an $n$-board $0, 1, \dots, n-1$ and give cell $i$
a left slot $2i$ and a right slot $2i + 1$. A fence $(s, g)$, with $s$ and $g$ natural numbers,
has teeth in slots $s$ and $s + 1 + 2g$. A tiling is a finite set of fences such that every
fence $(s, g)$ in it satisfies $s + 1 + 2g < 2n$ and either $s$ is even and $g \in D$, or $s$ is
odd and $-g - 1 \in D$, and such that every slot $x < 2n$ is a tooth of exactly one of its
fences. A tiling $t$ and a permutation $\pi$ of $\{0, 1, \dots, n-1\}$ are compatible if for
every cell $i$ and every fence $(s, g) \in t$: if $s = 2i$ then $\pi(i) = i + g$, and if
$s + 1 + 2g = 2i$ then $\pi(i) = i - g - 1$. Then for every tiling $t$ there is exactly one
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ that is compatible with $t$, and for every
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ there is exactly one tiling compatible
with $\pi$.

The lemma is due to Edwards and Allen (2015); the fences are $(\tfrac12, g)$-fences.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Lemma 12. -/
public theorem_wanted fenceTiling_strongPerm_bijection (D : Finset ℤ) (n : ℕ) :
    let IsTiling := fun t : Finset (ℕ × ℕ) =>
      (∀ f ∈ t, f.1 + 1 + 2 * f.2 < 2 * n ∧
        ((f.1 % 2 = 0 ∧ (f.2 : ℤ) ∈ D) ∨ (f.1 % 2 = 1 ∧ -(f.2 : ℤ) - 1 ∈ D))) ∧
      ∀ x < 2 * n, ∃! f, f ∈ t ∧ (x = f.1 ∨ x = f.1 + 1 + 2 * f.2)
    let Compatible := fun (t : Finset (ℕ × ℕ)) (π : Equiv.Perm (Fin n)) =>
      ∀ i : Fin n, ∀ f ∈ t,
        (f.1 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) + f.2) ∧
        (f.1 + 1 + 2 * f.2 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) - f.2 - 1)
    (∀ t, IsTiling t → ∃! π : Equiv.Perm (Fin n),
        (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) ∧ Compatible t π) ∧
      ∀ π : Equiv.Perm (Fin n), (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) →
        ∃! t, IsTiling t ∧ Compatible t π

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
