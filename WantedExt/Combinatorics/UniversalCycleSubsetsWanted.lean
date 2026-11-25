/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.UniversalCycleSubsetsWanted

/-!
# Universal cycle conjecture for k-subsets

Source [AMR-030-0078]: Chung/Diaconis/Graham as cited in Cooper,
Combinatorial Problems I Like (2020 snapshot), Words and Codes,
source-order bullet 78.
Source URL: https://people.math.sc.edu/cooper/combprob.html

Clause list from the source:
* for each `k`;
* every sufficiently large `n`, i.e. `∃ N, ∀ n ≥ N, …`;
* with `k` dividing `((n - 1).choose (k - 1))`;
* there is a universal cycle for the `k`-subsets of an `n`-set, i.e. a cyclic
  sequence of length `n.choose k` over the `n`-set whose blocks of `k`
  consecutive cyclic entries yield each `k`-subset exactly once.
-/

/-- **Universal cycle for $k$-subsets.** For natural numbers $n$ and $k$, let $N = \binom{n}{k}$.
A sequence $c_0, \dots, c_{N-1}$ of elements of $\{0, \dots, n-1\}$, read cyclically, is a
universal cycle for the $k$-subsets of $\{0, \dots, n-1\}$ when, for every starting position
$i < N$, the $k$ consecutive entries $c_i, c_{i+1}, \dots, c_{i+k-1}$ (indices taken modulo $N$)
are pairwise distinct, and every $k$-element subset of $\{0, \dots, n-1\}$ is the set of these
entries for exactly one starting position $i$.

Source: Chung/Diaconis/Graham as cited in Cooper, Combinatorial Problems I Like,
Words and Codes bullet 78 [AMR-030-0078]. -/
def IsUniversalCycle (n k : ℕ) (c : Fin (Nat.choose n k) → Fin n) : Prop :=
  ∀ hpos : 0 < Nat.choose n k,
    (∀ i : Fin (Nat.choose n k),
      ((Finset.univ : Finset (Fin k)).image (fun j : Fin k =>
        c ⟨(i.val + j.val) % Nat.choose n k,
          Nat.mod_lt (i.val + j.val) hpos⟩)).card = k)
    ∧ ∀ S : Finset (Fin n), S.card = k →
        ∃! i : Fin (Nat.choose n k),
          (Finset.univ : Finset (Fin k)).image (fun j : Fin k =>
            c ⟨(i.val + j.val) % Nat.choose n k,
              Nat.mod_lt (i.val + j.val) hpos⟩) = S

/-- **Chung–Diaconis–Graham universal cycle conjecture.** The statement that for every natural
number $k$ there is a natural number $N$ such that every $n \ge N$ for which $k$ divides
$\binom{n-1}{k-1}$ admits a universal cycle for the $k$-subsets of $\{0, \dots, n-1\}$. Here
$n - 1$ and $k - 1$ are truncated at $0$, so for $k = 0$ the divisibility condition reads
$0 \mid 1$ and never holds.

Source: Chung/Diaconis/Graham as cited in Cooper, Combinatorial Problems I Like,
Words and Codes bullet 78 [AMR-030-0078]. -/
def conjecture : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    k ∣ Nat.choose (n - 1) (k - 1) →
    ∃ c : Fin (Nat.choose n k) → Fin n, IsUniversalCycle n k c

/-- **Existence of universal cycles for $k$-subsets.** For every natural number $k$ there is a
natural number $N$ such that for every $n \ge N$ for which $k$ divides $\binom{n-1}{k-1}$, there
is a universal cycle for the $k$-subsets of $\{0, \dots, n-1\}$. Here $n - 1$ and $k - 1$ are
truncated at $0$, so for $k = 0$ the divisibility condition reads $0 \mid 1$ and never holds.

This is the Chung–Diaconis–Graham conjecture. Glock, Joos, Kühn and Osthus (Theorem 1.1)
proved it for every $k \ge 2$ in the language of tight Euler tours of the complete
$k$-uniform hypergraph; the case $k = 1$ is elementary.

Source: Stefan Glock, Felix Joos, Daniela Kühn, Deryk Osthus, Euler tours in
hypergraphs, Combinatorica 40 (2020), 679-690; arXiv:1808.07720,
https://arxiv.org/abs/1808.07720. Moved from
`OpenConjectures/Combinatorics/UniversalCycleSubsets`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.UniversalCycleSubsetsWanted
