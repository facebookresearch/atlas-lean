/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flattened Stirling permutations

Statements from Adam Buck, Jennifer Elder, Azia A. Figueroa, Pamela E. Harris,
Kimberly J. Harry, and Anthony Simpson, "Flattened Stirling Permutations",
*INTEGERS* 24 (2024), Article A104 (arXiv:2306.13034).

Stirling permutations of order `n` are MathlibExt's `IsStirlingPermutation n`
on words `Fin (2 * n) → ℕ`. A *run* of a word is a maximal contiguous weakly
increasing subword, so position `i` starts a run iff `i = 0` or the previous
letter is larger (`wordRunStart`). A word is *flattened* when the leading
letters of its runs are weakly increasing (`IsFlattenedWord`). For a
permutation the runs are increasing and the same predicates apply.

Type `B` set partitions of `[-n, n]` are Mathlib `Finpartition`s of
`Finset.Icc (-n) n` closed under negation with exactly one self-negative block
(`IsTypeBSetPartition`). The Dowling number `D_n` is MathlibExt's
`qrDowlingNumber` of the Whitney numbers `QRWhitney.whitneySecond 2 1 1`
(Whitney numbers of the second kind of the Dowling lattice over a group of
order `2`: `W(n+1, k+1) = W(n, k) + (2(k+1) + 1) W(n, k+1)`).
-/

/-
Proved in `MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBRuns`, which this module
imports: the number of runs of the word of a type `B` set partition
(`MetaMathlibExt.wordRunCount_typeBFlattenedWord`).

Proved in `MathlibExt.Combinatorics.Enumerative.DowlingExponentialGeneratingFunction`, which this
module imports: the exponential generating function of the Dowling numbers
(`MetaMathlibExt.hasSum_dowling_egf`).
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.DowlingExponentialGeneratingFunction
public import MathlibExt.Combinatorics.Enumerative.FlattenedPermutationRunRecurrence
public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTwoRuns
public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBRuns
public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBWord
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.NumberTheory.QRDowlingPolynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Flattened Stirling permutations and type $B$ set partitions.** For every natural number
$n \ge 1$, the set of flattened Stirling permutations of order $n + 1$ is in bijection with the
set of type $B$ set partitions of $[-n, n] = \{-n, \dots, n\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 2. -/
public theorem_wanted nonempty_flattenedStirling_equiv_typeBSetPartition (n : ℕ)
    (hn : 1 ≤ n) :
    Nonempty ({w : Fin (2 * (n + 1)) → ℕ //
        IsStirlingPermutation (n + 1) w ∧ IsFlattenedWord w} ≃
      {P : Finpartition (Finset.Icc (-(n : ℤ)) n) // IsTypeBSetPartition P})

/-- **Flattened Stirling permutations are counted by Dowling numbers.** For every $n \ge 1$, the
number $|\mathrm{flat}(Q_{n+1})|$ of flattened Stirling permutations of order $n + 1$ equals the
Dowling number $D_n = \sum_{k=0}^{n} W_{2,1,1}(n, k)$, where $W_{2,1,1}(n, k)$ are the
$(q, r)$-Whitney numbers of the second kind with $m = 2$, $r = 1$ and $q = 1$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 1. -/
public theorem_wanted flattenedStirlingCount_succ_eq_dowling (n : ℕ) (hn : 1 ≤ n) :
    (flattenedStirlingCount (n + 1) : ℂ) = qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n

/-- **Maximum number of runs of a flattened Stirling permutation.** For every natural number
$n \ge 1$, some flattened Stirling permutation of order $n$ has exactly
$\lceil 2n/3 \rceil$ runs, and no flattened Stirling permutation of order $n$ has more.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 5. -/
public theorem_wanted isGreatest_flattenedStirling_runCount (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {r : ℕ | ∃ w : Fin (2 * n) → ℕ,
        IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = r}
      ⌈(2 * n : ℚ) / 3⌉₊

/-- **A binomial–Stirling formula for flattened Stirling permutations.** For every natural number
$n$, the number of flattened Stirling permutations of order $n + 1$ is
$$
|\mathrm{flat}(Q_{n+1})| = \sum_{i=0}^{n} \binom{n}{i} \sum_{k=0}^{n-i} 2^{n-i-k} S(n-i, k),
$$
where $S(a, k)$ are the Stirling numbers of the second kind, with $S(0, 0) = 1$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 4. -/
public theorem_wanted flattenedStirlingCount_succ_eq_sum (n : ℕ) :
    flattenedStirlingCount (n + 1) =
      ∑ i ∈ Finset.range (n + 1), n.choose i *
        ∑ k ∈ Finset.range (n - i + 1), 2 ^ (n - i - k) * Nat.stirlingSecond (n - i) k

/-- **A binomial–Stirling formula for the Dowling numbers.** Let $W_{2,1,1}(n, k)$ be the
$(q, r)$-Whitney numbers of the second kind with $m = 2$, $r = 1$ and $q = 1$, and let
$D_n = \sum_{k=0}^{n} W_{2,1,1}(n, k)$ be the associated Dowling numbers. For every $n \ge 1$,
$$
D_n = \sum_{i=0}^{n} \binom{n}{i} \sum_{k=0}^{n-i} 2^{n-i-k} S(n-i, k),
$$
where $S(a, k)$ are the Stirling numbers of the second kind, with $S(0, 0) = 1$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 3, formula. -/
public theorem_wanted dowling_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n =
      ((∑ i ∈ Finset.range (n + 1), n.choose i *
        ∑ k ∈ Finset.range (n - i + 1), 2 ^ (n - i - k) * Nat.stirlingSecond (n - i) k : ℕ) : ℂ)

/-- **The map $\varphi$ is a bijection from type $B$ set partitions onto flattened Stirling
permutations.** For a natural number $n$, let $\varphi$ be the map of Buck et al.
(Proposition 1) that sends a set partition $P$ of $\{-n, \dots, n\}$ to a word of length
$2(n + 1)$ over the natural numbers, built from the zero block of $P$ and its Adler-labelled
blocks with each element $i$ replaced by $|i| + 1$. Then $\varphi$ sends the set of type $B$
set partitions of $\{-n, \dots, n\}$ bijectively onto the set of flattened Stirling
permutations of order $n + 1$: $\varphi$ is injective on type $B$ set partitions, sends each
of them to a flattened Stirling permutation of order $n + 1$, and every flattened Stirling
permutation of order $n + 1$ is $\varphi(\pi)$ for some type $B$ set partition $\pi$ of
$\{-n, \dots, n\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 3. -/
public theorem_wanted bijOn_typeBFlattenedWord (n : ℕ) :
    Set.BijOn (typeBFlattenedWord (n := n))
      {P : Finpartition (Finset.Icc (-(n : ℤ)) n) | IsTypeBSetPartition P}
      {w : Fin (2 * (n + 1)) → ℕ | IsStirlingPermutation (n + 1) w ∧ IsFlattenedWord w}

end

end MetaMathlibExt
