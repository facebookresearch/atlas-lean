/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd-indexed Fibonacci numbers via pattern-avoiding permutations

Statements from Juan B. Gil, Felix H. Xu, and William
Y. Zhu, "Odd-Indexed Fibonacci Numbers via
Pattern-Avoiding Permutations", *INTEGERS* 25 (2025),
Article A79 (<https://math.colgate.edu/~integers/vol25.html>).

Pattern containment is classical: `HasPattern σ π` says
some subsequence of `σ` is order-isomorphic to `π`
(patterns are given as `0`-based value functions, so
`pat321 = ![2, 1, 0]`, etc.). Stated here are the counts
`|Sₙ(321, 4123)| = |Sₙ(321, 3412)| = |Sₙ(231, 3124)| =
F_{2n-1}` (Propositions 1, 7, 10), the position-of-`1`
refinements for the first and third classes
(Propositions 2, 11, counts only: the bivariate
generating-function clauses reach the extraction in
garbled form and are not stated), and the first clause of
Proposition 8 (positions `1` and `2` of the entry `1` in
the `(321, 3412)` class). All were verified by brute force
for `n ≤ 7`.

Not stated (see the source audit table): the `(321, 2143)`
family (Propositions 4, 5, 6), whose classical-pattern
counts `1, 2, 5, 13, 33, 80, 185` disagree with the
extracted `F_{2n-1}` claim, so the pattern `2143` as
extracted cannot be the classical pattern intended;
Proposition 8's clause for positions `≥ 3`, whose
extracted form `|Sₙ^{k→1}| = |S_{n-1}|` is numerically
false (the values are `F_{2n-2k+1}`); and the bijection
statements (Corollary 1, Propositions 3, 6, 9, 12), which
need the paper's classes of noncrossing/nonnesting
partitions, Dyck paths, block fountains, and directed
column-convex polyominoes.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- **Classical pattern containment in a permutation.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n-1\}$ and let $\pi$ be a map from $\{0, 1, \dots, k-1\}$ to itself. Then
$\sigma$ contains the pattern $\pi$ if there are positions $e_0 < e_1 < \dots < e_{k-1}$ in
$\{0, 1, \dots, n-1\}$ such that for all $i, j < k$, $\sigma(e_i) < \sigma(e_j)$ holds exactly
when $\pi(i) < \pi(j)$. -/
def HasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) : Prop :=
  ∃ e : Fin k → Fin n, (∀ i j : Fin k, i < j → e i < e j) ∧
    ∀ i j : Fin k, σ (e i) < σ (e j) ↔ π i < π j


/-- **The pattern $321$.** The pattern $321$ written with values $0, 1, 2$: the map from
$\{0, 1, 2\}$ to itself sending $0 \mapsto 2$, $1 \mapsto 1$ and $2 \mapsto 0$. -/
def pat321 : Fin 3 → Fin 3 := ![2, 1, 0]

/-- **The pattern $231$.** The pattern $231$ written with values $0, 1, 2$: the map from
$\{0, 1, 2\}$ to itself sending $0 \mapsto 1$, $1 \mapsto 2$ and $2 \mapsto 0$. -/
def pat231 : Fin 3 → Fin 3 := ![1, 2, 0]

/-- **The permutation pattern $4123$.** The pattern $4123$ with its values shifted down by
one: the map $\{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ sending $0, 1, 2, 3$ to $3, 0, 1, 2$
respectively. -/
def pat4123 : Fin 4 → Fin 4 := ![3, 0, 1, 2]

/-- **The permutation pattern $3412$.** The pattern $3412$ with its values shifted down by
one: the map $\{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ sending $0, 1, 2, 3$ to $2, 3, 0, 1$
respectively. -/
def pat3412 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- **The pattern $3124$.** The pattern $3124$ written with values $0, 1, 2, 3$: the map from
$\{0, 1, 2, 3\}$ to itself sending $0 \mapsto 2$, $1 \mapsto 0$, $2 \mapsto 1$ and $3 \mapsto 3$. -/
def pat3124 : Fin 4 → Fin 4 := ![2, 0, 1, 3]

/-- **$(321, 4123)$-avoiding permutations are counted by odd-indexed Fibonacci numbers.** For
every $n \ge 1$, the number of permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$321$ and $4123$, that is, contain neither of them, is the Fibonacci number $F_{2n-1}$, where
$F_0 = 0$ and $F_1 = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 1. -/
theorem_wanted card_avoid_321_4123 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} =
      Nat.fib (2 * n - 1)

/-- **$(321, 3412)$-avoiding permutations are counted by odd-indexed Fibonacci numbers.** For
every $n \ge 1$, the number of permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$321$ and $3412$, that is, contain neither of them, is the Fibonacci number $F_{2n-1}$, where
$F_0 = 0$ and $F_1 = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 7. -/
theorem_wanted card_avoid_321_3412 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412} =
      Nat.fib (2 * n - 1)

/-- **$(231, 3124)$-avoiding permutations are counted by odd-indexed Fibonacci numbers.** For
every $n \ge 1$, the number of permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$231$ and $3124$, that is, contain neither of them, is the Fibonacci number $F_{2n-1}$, where
$F_0 = 0$ and $F_1 = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 10. -/
theorem_wanted card_avoid_231_3124 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
      Nat.fib (2 * n - 1)

/-- **Position of the smallest entry in $(321, 4123)$-avoiding permutations.** For a natural
number $m$, write $S_m(321, 4123)$ for the set of permutations of $\{0, 1, \dots, m-1\}$ that
avoid both patterns $321$ and $4123$, that is, contain neither of them. Let $n \ge 1$ and let
$j$ be a position with $j + 1 < n$. Then the number of permutations $\sigma \in S_n(321, 4123)$
with $\sigma(j) = 0$ equals $(j + 1) \cdot |S_{n-j-1}(321, 4123)|$.

In the source, positions and values start at $1$: with $k = j + 1$, the number of such
permutations with $\sigma(k) = 1$ is $k \cdot |S_{n-k}(321, 4123)|$ for $1 \le k < n$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 2. -/
theorem_wanted card_avoid_321_4123_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123}

/-- **Position of the smallest entry in $(231, 3124)$-avoiding permutations.** For a natural
number $m$, write $S_m(231, 3124)$ for the set of permutations of $\{0, 1, \dots, m-1\}$ that
avoid both patterns $231$ and $3124$, that is, contain neither of them. Let $n \ge 1$ and let
$j$ be a position with $j + 1 < n$. Then the number of permutations $\sigma \in S_n(231, 3124)$
with $\sigma(j) = 0$ equals $(j + 1) \cdot |S_{n-j-1}(231, 3124)|$.

In the source, positions and values start at $1$: with $k = j + 1$, the number of such
permutations with $\sigma(k) = 1$ is $k \cdot |S_{n-k}(231, 3124)|$ for $1 \le k < n$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 11. -/
theorem_wanted card_avoid_231_3124_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124}

/-- **Smallest entry in the first two positions of $(321, 3412)$-avoiding permutations.** Let
$n \ge 2$. Among the permutations $\sigma$ of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$321$ and $3412$, that is, contain neither of them, the number with $\sigma(0) = 0$ and the
number with $\sigma(1) = 0$ are both equal to the Fibonacci number $F_{2n-3}$, where $F_0 = 0$
and $F_1 = 1$.

In the source's indexing from $1$, these are the permutations with $\sigma(1) = 1$ and with
$\sigma(2) = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 8. -/
theorem_wanted card_avoid_321_3412_pos_zero_le (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨0, by omega⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3) ∧
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨1, hn⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3)

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
