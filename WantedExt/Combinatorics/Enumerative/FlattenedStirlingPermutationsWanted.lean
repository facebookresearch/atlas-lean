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
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.NumberTheory.QRDowlingPolynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Recursion for flattened partitions by number of runs.** Let $f_{n,k}$ be the number of
flattened partitions of length $n$ with exactly $k$ runs. For all $n \ge 1$ and $k \ge 2$,
$$
f_{n,k} = \sum_{m=1}^{n-2} \left( \binom{n-1}{m} - 1 \right) f_{m,k-1},
$$
where the sum is empty when $n \le 2$. Moreover $f_{n,1} = 1$ for every $n \ge 1$, and
$f_{n,k} = 0$ whenever $2 \le n \le k$.

This is the recursion of Nabawanda, Rakotondrajao, and Bamunoba as quoted in the paper.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 1 (quoting
Nabawanda et al., Theorem 1). -/
public theorem_wanted flattenedPermRunCount_recursion :
    (∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
      (flattenedPermRunCount n k : ℤ) =
        ∑ m ∈ Finset.Icc 1 (n - 2),
          (((n - 1).choose m : ℤ) - 1) * flattenedPermRunCount m (k - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → flattenedPermRunCount n 1 = 1) ∧
    (∀ n k : ℕ, 2 ≤ n → n ≤ k → flattenedPermRunCount n k = 0)

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

/-- **Recursion for flattened Stirling permutations with two runs.** Write
$|\mathrm{flat}_2(Q_n)|$ for the number of flattened Stirling permutations of order $n$ with
exactly two runs. Then $|\mathrm{flat}_2(Q_1)| = 0$, and for every natural number $n \ge 1$,
$|\mathrm{flat}_2(Q_{n+1})| = 2\,|\mathrm{flat}_2(Q_n)| + 2n - 1$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 2. -/
public theorem_wanted flattenedStirlingRunCount_two_recursion :
    flattenedStirlingRunCount 1 2 = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        flattenedStirlingRunCount (n + 1) 2 = 2 * flattenedStirlingRunCount n 2 + 2 * n - 1

/-- **Closed form for flattened Stirling permutations with two runs.** For every natural number
$n \ge 1$, the number $|\mathrm{flat}_2(Q_{n+1})|$ of flattened Stirling permutations of order
$n + 1$ with exactly two runs equals $3(2^n - 1) - 2n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 2. -/
public theorem_wanted flattenedStirlingRunCount_two_closed (n : ℕ) (hn : 1 ≤ n) :
    (flattenedStirlingRunCount (n + 1) 2 : ℤ) = 3 * (2 ^ n - 1) - 2 * n

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

/-- **Exponential generating function of the Dowling numbers.** For $n \ge 0$ let $D_n$ be the
$n$-th Dowling number of the group of order $2$, that is, the $(q, r)$-Dowling number
$D_n = \sum_{k=0}^{n} W_{2,1,1}(n, k)$ built from the $(q, r)$-Whitney numbers of the second
kind with $m = 2$, $r = 1$, $q = 1$. Then for every complex number $x$ the series
$\sum_{n \ge 0} D_n x^n / n!$ is summable with sum $\exp\bigl(x + (e^{2x} - 1)/2\bigr)$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 3, generating
function. -/
public theorem_wanted hasSum_dowling_egf (x : ℂ) :
    HasSum (fun n : ℕ => qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n * x ^ n / n.factorial)
      (Complex.exp (x + (Complex.exp (2 * x) - 1) / 2))

/-- **The word of a type $B$ set partition is a flattened Stirling permutation.** For every
natural number $n$ and every type $B$ set partition $P$ of $[-n, n] = \{-n, \dots, n\}$, the word
$\varphi(P) = w_1 w_2 \cdots w_{2(n+1)}$ of $P$ is a Stirling permutation of order $n + 1$ and is
flattened.

Source: arXiv:2306.13034, Proposition 3.6; the INTEGERS record is truncated after
"let `π_i = N_i P_i` be as in", and the statement is completed from the arXiv text.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1. -/
public theorem_wanted typeBFlattenedWord_mem_flattenedStirling {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    IsStirlingPermutation (n + 1) (typeBFlattenedWord P) ∧
      IsFlattenedWord (typeBFlattenedWord P)

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

/-- **Number of runs of the word of a type $B$ set partition.** Let $\pi$ be a type $B$ set
partition of $[-n, n]$ and let $\varphi(\pi)$ be the word of length $2(n + 1)$ that the map
$\varphi$ of Proposition 1 assigns to it. Write $P_0$ for the set of nonnegative elements of the
block of $\pi$ containing $0$. Let $\beta_1, \dots, \beta_m$ be the blocks kept by Adler's
labelling, exactly one from each pair $\{\beta, -\beta\}$ of distinct blocks, namely the block
containing the smallest magnitude of the pair as a positive element; write $N_i$ and $P_i$ for
the sets of negative and positive elements of $\beta_i$. Then the number of runs of
$\varphi(\pi)$ is
$$1 + |\{i \ge 1 : |N_i| \ge 1\}| + |\{i \ge 0 : |P_i| \ge 2\}|.$$

The paper states this for a flattened Stirling permutation $w$ of order $n + 1$ and the
partition $\varphi^{-1}(w)$; since $\varphi$ is a bijection from the type $B$ set partitions of
$[-n, n]$ onto these permutations (Theorem 3), this is the same as the statement for
$w = \varphi(\pi)$ over all $\pi$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 4. -/
public theorem_wanted wordRunCount_typeBFlattenedWord {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    wordRunCount (typeBFlattenedWord P) =
      1 + ((adlerBlockLabels P).filter fun p => ((P.part p).filter (· < 0)).Nonempty).card +
        ((insert 0 (adlerBlockLabels P)).filter fun p =>
          2 ≤ ((P.part p).filter (0 ≤ ·)).card).card

end

end MetaMathlibExt
