/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation
public import WantedExt.Combinatorics.Enumerative.LuckyCarsWanted

/-!
# Lucky and displacement statistics of Stirling permutations

Statements from L. Colmenarejo, A. Dawkins, J. Elder, P. E. Harris, K. J. Harry,
S. Kara, D. Smith, and B. E. Tenner, *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7
(arXiv:2403.03280).

A Stirling permutation of order `n` is MathlibExt's
`MetaMathlibExt.IsStirlingPermutation n w` for a word `w : Fin (2 * n) → ℕ`
(`w(1) ⋯ w(2n)` is `w 0, …, w (2n-1)`). It is read as a parking function of
length `2n`: car `i + 1` prefers spot `w i`. Parking is the existing greedy
outcome `MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.parkSpots`
(zero-based), applied to the zero-based preferences `stirlingPref w`. Car and
spot numbers in the statements below are the paper's one-based numbers: the car
at index `i : Fin (2 * n)` is car `i + 1`, and `stirlingParkSpot w i` is its
one-based spot `p(i + 1)`.
-/

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted (parkSpots)

namespace MetaMathlibExt

@[expose] public section

/-- **Zero-based preferences of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural
numbers, read as the preferences of $2n$ cars for spots numbered $0, \dots, 2n - 1$. Car
$i \in \{1, \dots, 2n\}$ prefers the spot $(w_i - 1) \bmod 2n$, where $w_i - 1$ is truncated at
$0$. When every $w_i$ lies in $\{1, \dots, 2n\}$, for example when $w$ is a Stirling permutation
of order $n$, this is the spot $w_i - 1$, which is spot $w_i$ in the one-based numbering.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Section 1 (Stirling permutations read as parking functions of length `2n`). -/
public def stirlingPref {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(w i - 1) % (2 * n), Nat.mod_lt _ i.pos⟩

/-- **Parking spot of a car.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car $i$
prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when every
$w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in order, and
car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an earlier car, or in
$p(i) = q_i$ if there is no such spot. The parking spot of car $i \in \{1, \dots, 2n\}$ is $p(i)$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingParkSpot {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  (parkSpots (stirlingPref w) i).val + 1

/-- **The lucky set of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car
$i$ prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when
every $w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in
order, and car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an
earlier car, or in $p(i) = q_i$ if there is no such spot. The lucky set $\mathrm{Lucky}(w)$
is the set of cars $i \in \{1, \dots, 2n\}$ with $p(i) = w_i$; when every $w_i$ lies in
$\{1, \dots, 2n\}$, these are the cars that park in their preferred spot.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 1.2. -/
public def stirlingLuckySet {n : ℕ} (w : Fin (2 * n) → ℕ) : Finset ℕ :=
  (Finset.univ.filter fun i => stirlingParkSpot w i = w i).image fun i => i.val + 1

/-- **Displacement of a car.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car
$i$ prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when
every $w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in
order, and car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an
earlier car, or in $p(i) = q_i$ if there is no such spot. The displacement of car $i$ is
$d(i) = p(i) - w_i$, where the subtraction is truncated at $0$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1; the tuple `i ↦ d(i + 1)` is the displacement composition
`dis(w)` (Definition 5.4). -/
public def stirlingDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  stirlingParkSpot w i - w i

/-- **Total displacement of a word.** Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers,
and for $i \in \{1, \dots, 2n\}$ let $d(i)$ be the displacement of car $i$ in $w$. The total
displacement of $w$ is $d(w) = \sum_{i=1}^{2n} d(i)$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingTotalDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) : ℕ :=
  ∑ i, stirlingDisplacement w i

/-- **Admissible lucky sets.** Let $n$ be a natural number. A finite set $S$ of natural numbers
is an $n$-admissible lucky set if $S = \mathrm{Lucky}(w)$ for some Stirling permutation $w$ of
order $n$, where $\mathrm{Lucky}(w)$ is the set of lucky cars of $w$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 3.1. -/
public def IsAdmissibleLuckySet (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ w : Fin (2 * n) → ℕ, IsStirlingPermutation n w ∧ stirlingLuckySet w = S

/-- **Lucky sets of 1122 and 1221.** Read as parking functions of length $4$, the Stirling
permutation $1122$ has car $1$ as its only lucky car, and $1221$ has exactly cars $1$ and $2$
lucky: $\mathrm{Lucky}(1122) = \{1\}$ and $\mathrm{Lucky}(1221) = \{1, 2\}$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definitions 1.2 and 3.1. -/
public theorem stirlingLuckySet_small :
    stirlingLuckySet (n := 2) ![1, 1, 2, 2] = {1} ∧
      stirlingLuckySet (n := 2) ![1, 2, 2, 1] = {1, 2} := by
  decide

/-- **Displacement compositions of 1122 and 11244233.** The displacement composition of a word
$w = w_1 \cdots w_{2n}$ is $\mathrm{dis}(w) = (d(1), \dots, d(2n))$, where $d(i)$ is the
displacement of car $i$. For the Stirling permutations $1122$ of order $2$ and $11244233$ of
order $4$, $\mathrm{dis}(1122) = (0, 1, 1, 2)$ and
$\mathrm{dis}(11244233) = (0, 1, 1, 0, 1, 4, 4, 5)$ (the paper's Example 5.5).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.4 and Example 5.5. -/
public theorem stirlingDisplacement_small :
    (fun i => stirlingDisplacement (n := 2) ![1, 1, 2, 2] i) = ![0, 1, 1, 2] ∧
      (fun i => stirlingDisplacement (n := 4) ![1, 1, 2, 4, 4, 2, 3, 3] i) =
        ![0, 1, 1, 0, 1, 4, 4, 5] := by
  decide

/-- **Basic properties of lucky cars.** Let $n \ge 1$ and let $w$ be a Stirling permutation of
order $n$, read as a parking function of length $2n$. Then (a) car $1$ is lucky; (b) the first
car $i$ with $w_i = 1$ is lucky; (c) the number of lucky cars of $w$ is at least $1$ and at
most $n$.

The hypothesis $n \ge 1$ is added: the only Stirling permutation of order $0$ is the empty
word, which has no cars.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 2.1 (`jis-2024-24.6.7-lem-5`). -/
public theorem_wanted stirlingLuckySet_basic (n : ℕ) (hn : 1 ≤ n) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    1 ∈ stirlingLuckySet w ∧
      (∀ i : Fin (2 * n), w i = 1 → (∀ j < i, w j ≠ 1) → i.val + 1 ∈ stirlingLuckySet w) ∧
      1 ≤ (stirlingLuckySet w).card ∧ (stirlingLuckySet w).card ≤ n

/-- **Characterization of extremely unlucky Stirling permutations.** Let $n \ge 1$ and let $w$
be a Stirling permutation of order $n$, read as a parking function of length $2n$. Then car $1$
is the only lucky car of $w$ if and only if for every $x \in \{2, \dots, n\}$ and every
position $i \le x$, we have $w_i < x$.

The hypothesis $n \ge 1$ is added: the empty word, the only Stirling permutation of order $0$,
has no lucky cars, while the right-hand side holds vacuously.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 2.5 (`jis-2024-24.6.7-cor-11`). -/
public theorem_wanted stirlingLuckySet_eq_singleton_iff (n : ℕ) (hn : 1 ≤ n)
    (w : Fin (2 * n) → ℕ) (hw : IsStirlingPermutation n w) :
    stirlingLuckySet w = {1} ↔
      ∀ x ∈ Finset.Icc 2 n, ∀ i : Fin (2 * n), i.val + 1 ≤ x → w i < x

/-- **Counting extremely unlucky Stirling permutations.** For every integer $n \ge 1$, the number
of Stirling permutations $w$ of order $n$ that are extremely unlucky, that is, whose only lucky
car is car $1$ ($\mathrm{Lucky}(w) = \{1\}$), is $(n - 1)!$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 2.7 (`jis-2024-24.6.7-thm-13`). -/
public theorem_wanted card_extremely_unlucky_stirling (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ stirlingLuckySet w = {1}} =
      (n - 1).factorial

/-- **Characterization of extremely lucky Stirling permutations.** Let $w$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$. Then $w$ has exactly $n$
lucky cars if and only if the second occurrences of the letters of $w$ appear in decreasing
order: for all positions $a < b$ such that $w_a$ also occurs before position $a$ and $w_b$ also
occurs before position $b$, we have $w_b < w_a$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 2.11 (`jis-2024-24.6.7-prop-17`). -/
public theorem_wanted stirlingLuckySet_card_eq_iff (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    (stirlingLuckySet w).card = n ↔
      ∀ a b : Fin (2 * n), (∃ c < a, w c = w a) → (∃ c < b, w c = w b) → a < b → w b < w a

/-- **Extremely lucky Stirling permutations and Dyck words.** For every natural number $n$, there
is a bijection between the Stirling permutations $w$ of order $n$ that are extremely lucky, that
is, whose set $\mathrm{Lucky}(w)$ of lucky cars has exactly $n$ elements, and the Dyck words of
semilength $n$ (valid parenthesizations of $n$ pairs of parentheses).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 2.12 (`jis-2024-24.6.7-thm-18`). -/
public theorem_wanted extremely_lucky_stirling_equiv_dyckWord (n : ℕ) :
    Nonempty ({w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ (stirlingLuckySet w).card = n} ≃
      {p : DyckWord // p.semilength = n})

/-- **Extremely lucky Stirling permutations are counted by the Catalan numbers.** For every
positive integer $n$, the number of Stirling permutations $w$ of order $n$ that are extremely
lucky, that is, whose set $\mathrm{Lucky}(w)$ of lucky cars has exactly $n$ elements, is the
Catalan number $C_n$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 2.14 (`jis-2024-24.6.7-cor-20`). -/
public theorem_wanted card_extremely_lucky_stirling (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ (stirlingLuckySet w).card = n} =
      catalan n

/-- **Extending admissible lucky sets.** Let $n \ge 1$. If $S$ is an $n$-admissible lucky set,
then both $S$ and $S \cup \{2n + 1\}$ are $(n + 1)$-admissible lucky sets.

The hypothesis $n \ge 1$ is added: the empty set is $0$-admissible but not $1$-admissible.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 3.3 (`jis-2024-24.6.7-thm-23`). -/
public theorem_wanted IsAdmissibleLuckySet.succ (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : IsAdmissibleLuckySet n S) :
    IsAdmissibleLuckySet (n + 1) S ∧ IsAdmissibleLuckySet (n + 1) (insert (2 * n + 1) S)

/-- **Necessary conditions for admissible lucky sets.** Let $n \ge 1$. If $S$ is an
$n$-admissible lucky set, then $1 \in S$ and $2n \notin S$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 3.4 (`jis-2024-24.6.7-cor-24`). -/
public theorem_wanted IsAdmissibleLuckySet.one_mem_and_two_mul_not_mem (n : ℕ) (hn : 1 ≤ n)
    (S : Finset ℕ) (hS : IsAdmissibleLuckySet n S) : 1 ∈ S ∧ 2 * n ∉ S

/-- **Parking before the second lucky car.** Let $w = w_1 \cdots w_{2n}$ be a Stirling permutation
of order $n$, read as a parking function of length $2n$, and let $x$ be a lucky car of $w$ such
that exactly one lucky car of $w$ is smaller than $x$, so that $x$ is the second-smallest element
of the lucky set $\mathrm{Lucky}(w)$. Then every car $c$ with $2 \le c \le x - 1$ parks in spot
$w_1 + c - 1$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.5 (`jis-2024-24.6.7-lem-25`). -/
public theorem_wanted stirlingParkSpot_before_second_lucky (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (i : Fin (2 * n))
    (hi : 2 ≤ i.val + 1) (hix : i.val + 1 ≤ x - 1) :
    stirlingParkSpot w i = w ⟨0, i.pos⟩ + i.val

/-- **Left-to-right minima of a Stirling permutation sit at odd positions.** Let
$w = w_1 \cdots w_{2n}$ be a Stirling permutation of order $n$ and let $j \in \{1, \dots, 2n\}$.
If $w_j < w_i$ for every $i < j$, then $j$ is odd.

In the paper, $j$ is the first car preferring spot $w_j$; the hypothesis $w_j < w_i$ for all
$i < j$ already implies this, and $w_j \in \{1, \dots, n\}$ holds for every Stirling permutation.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.7 (`jis-2024-24.6.7-lem-27`). -/
public theorem_wanted stirling_odd_of_lt_all_before (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (j : Fin (2 * n)) (hj : ∀ i < j, w j < w i) :
    Odd (j.val + 1)

/-- **A second lucky car beyond $n$ is odd.** Let $w = w_1 \cdots w_{2n}$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$, and let $x$ be a lucky car
of $w$ such that exactly one lucky car of $w$ is smaller than $x$, so that $x$ is the
second-smallest element of the lucky set $\mathrm{Lucky}(w)$. If $x > n$, then $x$ is odd.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 3.8 (`jis-2024-24.6.7-prop-28`). -/
public theorem_wanted stirling_second_lucky_odd (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (hxn : n < x) : Odd x

/-- **Preference of the second lucky car.** Let $w = w_1 \cdots w_{2n}$ be a Stirling permutation
of order $n$, read as a parking function of length $2n$, and let $x$ be a lucky car of $w$ such
that exactly one lucky car of $w$ is smaller than $x$, so that $x$ is the second-smallest element
of the lucky set $\mathrm{Lucky}(w)$. If $w_1 = 1$, then $x \le w_x \le n$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.9 (`jis-2024-24.6.7-lem-29`). -/
public theorem_wanted stirling_second_lucky_pref (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (i : Fin (2 * n))
    (hi : i.val + 1 = x) (hw1 : w ⟨0, i.pos⟩ = 1) : x ≤ w i ∧ w i ≤ n

/-- **The first preference bounds the lucky cars.** Let $w$ be a Stirling permutation of
order $n$, read as a parking function of length $2n$, with at least $3$ lucky cars, and let $x$
be the second-smallest lucky car of $w$. If $x \ge n$, then the number of lucky cars of $w$ is
at most $w_1$, and every lucky car parks in one of the spots $1, \dots, w_1$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.10 (`jis-2024-24.6.7-lem-30`). -/
public theorem_wanted stirling_first_pref_ge_lucky (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (h3 : 3 ≤ (stirlingLuckySet w).card) (x : ℕ)
    (hx : x ∈ stirlingLuckySet w) (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1)
    (hxn : n ≤ x) (i₀ : Fin (2 * n)) (hi₀ : i₀.val = 0) :
    (stirlingLuckySet w).card ≤ w i₀ ∧
      ∀ i : Fin (2 * n), i.val + 1 ∈ stirlingLuckySet w → stirlingParkSpot w i ≤ w i₀

/-- **When the penultimate car is lucky.** Let $n \ge 1$ and let $w = w_1 \cdots w_{2n}$ be a
Stirling permutation of order $n$, read as a parking function of length $2n$. Then car $2n - 1$
is lucky, that is, belongs to the lucky set $\mathrm{Lucky}(w)$, if and only if $w_{2n-1} = 1$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 3.11 (`jis-2024-24.6.7-thm-31`). -/
public theorem_wanted stirling_penultimate_lucky_iff (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (i : Fin (2 * n)) (hi : i.val + 1 = 2 * n - 1) :
    2 * n - 1 ∈ stirlingLuckySet w ↔ w i = 1

/-- **Admissible lucky sets with two elements.** Let $n$, $h$ and $i$ be natural numbers with
$h < i \le 2n$. The set $\{h, i\}$ is an $n$-admissible lucky set if and only if $h = 1$ and
either $i > n$ and $i$ is odd, or $i \le n$.

The bound $i \le 2n$ is the paper's standing assumption that lucky sets lie in
$\{1, \dots, 2n\}$; without it $\{1, 2n + 1\}$ would satisfy the right-hand side.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 4.1 (`jis-2024-24.6.7-thm-32`). -/
public theorem_wanted isAdmissibleLuckySet_pair_iff (n h i : ℕ) (hhi : h < i) (hi : i ≤ 2 * n) :
    IsAdmissibleLuckySet n {h, i} ↔ h = 1 ∧ (n < i ∧ Odd i ∨ i ≤ n)

/-- **Counting admissible lucky sets with two elements.** For every integer $n \ge 1$, the number
of $n$-admissible lucky sets with exactly two elements is $n - 1 + \lceil (n - 1)/2 \rceil$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 4.2 (`jis-2024-24.6.7-cor-33`). -/
public theorem_wanted ncard_admissibleLuckySet_card_two (n : ℕ) (hn : 1 ≤ n) :
    {S : Finset ℕ | IsAdmissibleLuckySet n S ∧ S.card = 2}.ncard =
      n - 1 + ⌈((n - 1 : ℕ) : ℚ) / 2⌉₊

/-- **Stirling permutations whose second lucky car is $n$.** Let $w = w_1 \cdots w_{2n}$ be a
Stirling permutation of order $n$, read as a parking function of length $2n$, such that car $n$
is lucky and exactly one lucky car of $w$ is smaller than $n$, so that $n$ is the second-smallest
element of the lucky set $\mathrm{Lucky}(w)$. (a) If $n$ is even, then $w_1 = 1$, $w_n = n$ and
$\mathrm{Lucky}(w)$ has exactly $2$ elements. (b) If $n$ is odd and $w_1 = 1$, then $w_n = n$ and
$\mathrm{Lucky}(w)$ has exactly $2$ elements.

The paper states this for an admissible lucky set $S$ and a Stirling permutation $w$ with
$\mathrm{Lucky}(w) = S$; here it holds for every such $w$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 4.3 (`jis-2024-24.6.7-lem-34`). -/
public theorem_wanted stirling_second_lucky_eq_n (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hn : n ∈ stirlingLuckySet w)
    (hn2 : ((stirlingLuckySet w).filter (· < n)).card = 1) (i₀ iN : Fin (2 * n))
    (hi₀ : i₀.val = 0) (hiN : iN.val + 1 = n) :
    (Even n → w i₀ = 1 ∧ w iN = n ∧ (stirlingLuckySet w).card = 2) ∧
      (Odd n → w i₀ = 1 → w iN = n ∧ (stirlingLuckySet w).card = 2)

/-- **When $\{1, n - 1, 2n - 2\}$ is an admissible lucky set.** For every integer $n \ge 4$, the
set $\{1, n - 1, 2n - 2\}$ is an $n$-admissible lucky set if and only if $n$ is even.

As printed the claim covers all $n$, but it fails at $n = 3$: $w = 133221$ is a Stirling
permutation of order $3$ with $\mathrm{Lucky}(w) = \{1, 2, 4\} = \{1, n - 1, 2n - 2\}$ (its cars
park in spots $1, 3, 4, 2, 5, 6$). The paper's proof assumes $n > 3$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 4.4 (`jis-2024-24.6.7-prop-35`). -/
public theorem_wanted isAdmissibleLuckySet_one_pred_two_mul_sub_two_iff (n : ℕ) (hn : 4 ≤ n) :
    IsAdmissibleLuckySet n {1, n - 1, 2 * n - 2} ↔ Even n

/-- **Total displacement of a Stirling permutation is invariant under rearrangement.** Let
$w = w_1 \cdots w_{2n}$ be a Stirling permutation of order $n$ and let $\sigma$ be a permutation
of $\{1, \dots, 2n\}$. Read words of length $2n$ as parking functions, and let $d(v)$ denote the
total displacement of a word $v$, the sum of the displacements of its cars. Then the rearranged
word $w \circ \sigma = w_{\sigma(1)} \cdots w_{\sigma(2n)}$ satisfies $d(w \circ \sigma) = d(w)$.

The rearranged word $w \circ \sigma$ need not be a Stirling permutation.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 5.2 (`jis-2024-24.6.7-lem-37`), quoting Elder, Harris, Kretschmann, and
Martínez Mori, Lemma 3.1. -/
public theorem_wanted stirlingTotalDisplacement_comp_perm (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (σ : Equiv.Perm (Fin (2 * n))) :
    stirlingTotalDisplacement (w ∘ σ) = stirlingTotalDisplacement w

/-- **Total displacement of a Stirling permutation.** Let $w = w_1 \cdots w_{2n}$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$. Then the total displacement
of $w$, the sum $d(1) + \dots + d(2n)$ of the displacements of its cars, is $n^2$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.3 (`jis-2024-24.6.7-cor-38`). -/
public theorem_wanted stirlingTotalDisplacement_eq (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) : stirlingTotalDisplacement w = n ^ 2

/-- **Number of cars with zero displacement.** Let $n \ge 1$ and let $w$ be a Stirling
permutation of order $n$, read as a parking function of length $2n$. The number of cars
$i \in \{1, \dots, 2n\}$ with displacement $d(i) = 0$ is at least $1$ and at most $n$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.6 (`jis-2024-24.6.7-cor-41`). -/
public theorem_wanted stirling_card_zero_displacement (n : ℕ) (hn : 1 ≤ n) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    1 ≤ (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ∧
      (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ≤ n

/-- **Unlucky cars of an extremely lucky Stirling permutation.** Let $w = w_1 \cdots w_{2n}$ be a
Stirling permutation of order $n$ that is extremely lucky, that is, its set $\mathrm{Lucky}(w)$
of lucky cars has exactly $n$ elements, and let $1 \le i \le n$. If car $j$ is unlucky and
exactly $i - 1$ of the cars $1, \dots, j - 1$ are unlucky, then car $j$ prefers spot
$w_j = n - i + 1$ and has displacement $d(j) = 2i - 1$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 5.7 (`jis-2024-24.6.7-lem-42`). -/
public theorem_wanted extremely_lucky_unlucky_car (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hl : (stirlingLuckySet w).card = n) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (j : Fin (2 * n)) (hj : j.val + 1 ∉ stirlingLuckySet w)
    (hcount : (Finset.univ.filter fun k : Fin (2 * n) =>
      k < j ∧ k.val + 1 ∉ stirlingLuckySet w).card = i - 1) :
    w j = n - i + 1 ∧ stirlingDisplacement w j = 2 * i - 1

/-- **Extremely lucky Stirling permutations are determined by their displacements.** Let $w$ and
$w'$ be Stirling permutations of order $n$, and suppose that $w$ is extremely lucky, that is, its
set $\mathrm{Lucky}(w)$ of lucky cars has exactly $n$ elements. If every car has the same
displacement in $w'$ as in $w$ (that is, $\mathrm{dis}(w') = \mathrm{dis}(w)$), then $w' = w$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 5.8 (`jis-2024-24.6.7-thm-43`). -/
public theorem_wanted extremely_lucky_eq_of_displacement_eq (n : ℕ) (w w' : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hw' : IsStirlingPermutation n w')
    (hl : (stirlingLuckySet w).card = n)
    (hd : ∀ i, stirlingDisplacement w' i = stirlingDisplacement w i) : w' = w

/-- **Stirling permutations with $n$ nonzero displacements.** For every natural number $n$, the
number of Stirling permutations $w$ of order $n$ in which exactly $n$ cars have nonzero
displacement (equivalently, whose displacement composition $\mathrm{dis}(w)$ has exactly $n$
nonzero parts) is the Catalan number $C_n$.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.9 (`jis-2024-24.6.7-cor-45`). -/
public theorem_wanted card_stirling_displacement_nonzero_parts (n : ℕ) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧
      (Finset.univ.filter fun i => stirlingDisplacement w i ≠ 0).card = n} = catalan n

end

end MetaMathlibExt
