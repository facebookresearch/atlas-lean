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
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Partition.Finpartition
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation
public import MathlibExt.NumberTheory.QRDowlingPolynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Start of a run.** Position $i$ of a word $w = w_0 w_1 \cdots w_{m-1}$ of natural numbers
starts a run when $i = 0$ or the letter before it is larger, that is, $w_{i-1} > w_i$. Runs are
the maximal contiguous weakly increasing subwords, so these are exactly the positions where a run
begins.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunStart {m : ℕ} (w : Fin m → ℕ) (i : Fin m) : Prop :=
  i.val = 0 ∨ ∃ j : Fin m, j.val + 1 = i.val ∧ w i < w j

instance {m : ℕ} (w : Fin m → ℕ) : DecidablePred (wordRunStart w) := fun _ => by
  unfold wordRunStart; infer_instance

/-- **Number of runs of a word.** A run of a word $w = w_0 w_1 \cdots w_{m-1}$ of natural numbers is
a maximal contiguous weakly increasing subword. The number of runs of $w$ is the number of
positions $i < m$ that start a run, that is, with $i = 0$ or $w_{i-1} > w_i$; the empty word has
no runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunCount {m : ℕ} (w : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter (wordRunStart w)).card

/-- **Flattened words.** A word $w = w_1 w_2 \cdots w_m$ of natural numbers is flattened when
the leading letters of its runs, read left to right, are weakly increasing. Here a run is a
maximal contiguous weakly increasing subword, so position $i$ starts a run when $i = 1$ or
$w_{i-1} > w_i$; the condition is that $w_i \le w_j$ whenever $i < j$ and both positions
start runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened). -/
def IsFlattenedWord {m : ℕ} (w : Fin m → ℕ) : Prop :=
  ∀ i j : Fin m, i < j → wordRunStart w i → wordRunStart w j → w i ≤ w j

instance {m : ℕ} (w : Fin m → ℕ) : Decidable (IsFlattenedWord w) := by
  unfold IsFlattenedWord; infer_instance

/-- **Number of flattened Stirling permutations.** For a natural number $n$,
$|\mathrm{flat}(Q_n)|$ is the number of flattened Stirling permutations of order $n$: words
$w_1 w_2 \cdots w_{2n}$ of natural numbers that are Stirling permutations of order $n$ and whose
runs (maximal contiguous weakly increasing subwords) have weakly increasing leading letters,
read from left to right.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingCount (n : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ | IsStirlingPermutation n w ∧ IsFlattenedWord w}

/-- **Counting flattened Stirling permutations by runs.** For natural numbers $n$ and $k$,
$|\mathrm{flat}_k(Q_n)|$ is the number of flattened Stirling permutations of order $n$ with
exactly $k$ runs, where a run is a maximal contiguous weakly increasing subword.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingRunCount (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ |
    IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = k}

/-- **Flattened partitions counted by runs.** For natural numbers $n$ and $k$, $f_{n,k}$ is the
number of permutations $\sigma$ of $\{0, 1, \dots, n - 1\}$ such that the word
$\sigma(0) \sigma(1) \cdots \sigma(n - 1)$ is flattened (the leading letters of its runs, read
left to right, are weakly increasing) and has exactly $k$ runs, where a run is a maximal
contiguous weakly increasing subword. These are the flattened partitions of length $n$ of
Nabawanda, Rakotondrajao, and Bamunoba, with letters $0, \dots, n - 1$ in place of
$1, \dots, n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened
partitions, after Nabawanda, Rakotondrajao, and Bamunoba). -/
def flattenedPermRunCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    IsFlattenedWord (fun i => (σ i : ℕ)) ∧ wordRunCount (fun i => (σ i : ℕ)) = k).card

/-- **Type $B$ set partitions.** For a natural number $n$, a set partition $P$ of the integer
interval $[-n, n] = \{-n, \dots, n\}$ is of type $B$ if for every block $\beta$ of $P$ the set
$-\beta = \{-x : x \in \beta\}$ is again a block of $P$, and exactly one block $\beta$ of $P$
satisfies $-\beta = \beta$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1. -/
def IsTypeBSetPartition {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Prop :=
  (∀ b ∈ P.parts, b.image (fun x => -x) ∈ P.parts) ∧
    ∃! b, b ∈ P.parts ∧ b.image (fun x => -x) = b

/-- **A flattened word with four runs.** The word
$w = 1\,1\,2\,2\,9\,9\,3\,8\,8\,3\,4\,6\,6\,7\,7\,4\,5\,5$ of length $18$ is flattened (the
leading letters of its runs, read left to right, are weakly increasing), and it has exactly
$4$ runs, where a run is a maximal contiguous weakly increasing subword.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem isFlattenedWord_example :
    IsFlattenedWord ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] ∧
      wordRunCount ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] = 4 := by
  decide

/-- **A word that is not flattened.** The word $123321445566778899$ is not flattened.

This word is a Stirling permutation of order $9$; its runs $1233$, $2$, $1445566778899$ have
leading letters $1, 2, 1$, which do not weakly increase.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem not_isFlattenedWord_example :
    ¬ IsFlattenedWord ![1, 2, 3, 3, 2, 1, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] := by
  decide

/-- **The one-block partition is of type B.** For every natural number $n$, the partition of
the integer interval $[-n, n] = \{-n, \dots, n\}$ into a single block is a type $B$ set
partition: its only block is closed under negation, so it is the unique block equal to its own
negative (the zero-block).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1; characteristic
check of `IsTypeBSetPartition`. -/
theorem isTypeBSetPartition_indiscrete (n : ℕ) :
    IsTypeBSetPartition
      (Finpartition.indiscrete (a := Finset.Icc (-(n : ℤ)) n)
        (by rw [Finset.bot_eq_empty]; exact (Finset.nonempty_Icc.2 (by omega)).ne_empty)) := by
  refine ⟨?_, ⟨Finset.Icc (-(n : ℤ)) n, ⟨by simp, ?_⟩, ?_⟩⟩
  · intro b hb
    simp only [Finpartition.indiscrete_parts, Finset.mem_singleton] at hb ⊢
    subst hb
    ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · rintro b ⟨hb, -⟩
    simpa using hb

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

/-- **Exactly one flattened Stirling permutation has one run.** For every natural number
$n \ge 1$, exactly one flattened Stirling permutation of order $n$ has exactly one run.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 1. -/
public theorem_wanted flattenedStirlingRunCount_one (n : ℕ) (hn : 1 ≤ n) :
    flattenedStirlingRunCount n 1 = 1

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

/-- **The shift map.** For a finite set $S$ of integers, $h(S) = \{|i| + 1 : i \in S\}$, a
finite set of natural numbers.

In particular, for every natural number $n$, $h$ sends subsets of $[-n, n]$ to subsets of
$\{1, \dots, n + 1\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
def typeBShift (S : Finset ℤ) : Finset ℕ :=
  S.image fun i => i.natAbs + 1

/-- **Doubled word.** For a finite set $S = \{s_1 < s_2 < \dots < s_k\}$ of natural numbers, the
doubled word of $S$ is $f(S) = s_1 s_1 s_2 s_2 \cdots s_k s_k$, which lists the elements of $S$
in increasing order with each one written twice; $f(\emptyset)$ is the empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
def doubledWord (S : Finset ℕ) : List ℕ :=
  (S.sort (· ≤ ·)).flatMap fun s => [s, s]

/-- **Wrapped word of a finite set.** For a finite set $S = \{s_1 < s_2 < \dots < s_k\}$ of natural
numbers, the wrapped word $g(S)$ is $s_1 s_2 s_2 \cdots s_k s_k s_1$: the smallest element, then
each larger element written twice in increasing order, then the smallest element again. For
$S = \emptyset$, $g(S)$ is the empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
def wrappedWord (S : Finset ℕ) : List ℕ :=
  match S.sort (· ≤ ·) with
  | [] => []
  | s :: t => s :: t.flatMap (fun x => [x, x]) ++ [s]

/-- **An example of the shift map.** For the map $h(S) = \{|i| + 1 : i \in S\}$ on finite sets
of integers, $h(\{-2, 0, 1\}) = \{1, 2, 3\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
theorem typeBShift_example : typeBShift {-2, 0, 1} = {1, 2, 3} := by
  decide

/-- **The doubled word of a singleton.** For every natural number $s$, the doubled word of the
singleton $\{s\}$ is $f(\{s\}) = s\,s$, the word of length two whose letters are both $s$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem doubledWord_singleton (s : ℕ) : doubledWord {s} = [s, s] := by
  simp [doubledWord]

/-- **Length of the doubled word.** For every finite set $S$ of natural numbers with elements
$s_1 < \dots < s_k$, the doubled word $f(S) = s_1 s_1 s_2 s_2 \cdots s_k s_k$ has length $2|S|$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem length_doubledWord (S : Finset ℕ) : (doubledWord S).length = 2 * S.card := by
  simp [doubledWord, List.length_flatMap, mul_comm]

/-- **Wrapped word of the empty set.** The wrapped word $g(\emptyset)$ of the empty set is the
empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_empty : wrappedWord ∅ = [] := by
  simp [wrappedWord]

/-- **Wrapped word of a singleton.** For every natural number $s$, the wrapped word of the
singleton $\{s\}$ is $g(\{s\}) = s\,s$, the word of length two both of whose letters are $s$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_singleton (s : ℕ) : wrappedWord {s} = [s, s] := by
  simp [wrappedWord]

/-- **Length of the wrapped word.** For every finite set $S$ of natural numbers with elements
$s_1 < \dots < s_k$, the wrapped word $g(S) = s_1 s_2 s_2 \cdots s_k s_k s_1$ (the empty word when
$S = \emptyset$) has length $2|S|$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem length_wrappedWord (S : Finset ℕ) : (wrappedWord S).length = 2 * S.card := by
  rw [← Finset.length_sort (· ≤ ·) (s := S)]
  unfold wrappedWord
  split <;> simp_all [List.length_flatMap]
  omega

/-- **Adler block labels.** Let $n$ be a natural number and $P$ a set partition of the integer
interval $\{-n, \dots, n\}$; for $x$ in this interval write $P(x)$ for the block of $P$
containing $x$. The Adler block labels of $P$ are the integers $p$ with $1 \le p \le n$ such
that $p \le q$ for every positive $q \in P(p)$ and $p < -q$ for every negative $q \in P(p)$;
that is, $p$ is the least positive element of its block and is smaller than the absolute value
of every negative element of that block.

For a type $B$ set partition the block containing $0$ is never labelled, and from each pair of
blocks $\beta \ne -\beta$ exactly the block containing the element of least absolute value as a
positive element is labelled, by its least positive element; sorting the labels orders these
kept blocks as $\beta_1, \dots, \beta_m$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3 (arXiv:2306.13034). -/
def adlerBlockLabels {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Finset ℤ :=
  (Finset.Icc 1 (n : ℤ)).filter fun p =>
    ∀ q ∈ P.part p, (0 < q → p ≤ q) ∧ (q < 0 → p < -q)

/-- **Adler labels lie in $\{1, \dots, n\}$.** For every natural number $n$ and every set
partition $P$ of $\{-n, \dots, n\}$, every Adler block label $p$ of $P$ is an integer with
$1 \le p \le n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3. -/
theorem adlerBlockLabels_subset {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    adlerBlockLabels P ⊆ Finset.Icc 1 (n : ℤ) :=
  Finset.filter_subset _ _

/-- **The word of a set partition of $[-n, n]$, as a list.** Let $n$ be a natural number and let
$P$ be a set partition of $[-n, n] = \{-n, \dots, n\}$. For a finite set $S$ of integers let
$h(S) = \{|i| + 1 : i \in S\}$, and for a finite set $T$ of natural numbers with elements
$t_1 < \dots < t_k$ let $f(T) = t_1 t_1 t_2 t_2 \cdots t_k t_k$ and
$g(T) = t_1 t_2 t_2 \cdots t_k t_k t_1$ (both empty when $T = \emptyset$). Let $P_0$ be the set of
nonnegative elements of the block of $P$ containing $0$. Let $p_1 < \dots < p_m$ be the integers $p$
with $1 \le p \le n$ such that every positive element of the block of $P$ containing $p$ is at
least $p$ and every negative element $q$ of that block satisfies $p < -q$, and let $N_i$ and $P_i$
be the sets of negative and of positive elements of the block containing $p_i$. The list of $P$ is
the list of natural numbers
$$g(h(P_0))\, f(h(N_1))\, g(h(P_1)) \cdots f(h(N_m))\, g(h(P_m)).$$

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`), with
Definition 2. -/
def typeBFlattenedWordList {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    List ℕ :=
  wrappedWord (typeBShift ((P.part 0).filter (0 ≤ ·))) ++
    ((adlerBlockLabels P).sort (· ≤ ·)).flatMap fun p =>
      doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))

/-- **The word of a set partition of $[-n, n]$.** For a natural number $n$ and a set partition
$P$ of $[-n, n] = \{-n, \dots, n\}$, let $L(P)$ be the list of $P$: the list of natural numbers
built from the blocks of $P$ (via the shift map and the doubled and wrapped words). The word
$\varphi(P) = w_1 w_2 \cdots w_{2(n+1)}$ has $w_i$ equal to the $i$-th entry of $L(P)$ when $L(P)$
has at least $i$ entries, and $w_i = 0$ otherwise.

Restricted to type $B$ set partitions, this is the map $\varphi$ of Proposition 1.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`). -/
def typeBFlattenedWord {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    Fin (2 * (n + 1)) → ℕ :=
  fun i => (typeBFlattenedWordList P).getD i 0

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
