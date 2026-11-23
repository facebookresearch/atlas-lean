/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Fundamental sequences and the duality formula for Zeckendorf binary expansions

Statement-only targets from Sungkon Chang, *Distribution of Zeckendorf Expressions*,
INTEGERS 25 (2025), Article A25 (texts checked against arXiv:2308.12872v1, Lemmas 1.2 and 1.5).
Indices are shifted to start at `0`: the paper's `2^(k-1)` and Fibonacci terms `F_k`
(`F_1 = 1`, `F_2 = 2`) become `2 ^ k` and `Nat.fib (k + 2)`. A coefficient function with entries
at most `1` is a finite index set `s : Finset ℕ`.

Section 2 of the paper (generalized Zeckendorf expansions for positive integers) works with
general coefficient functions, taken here as `ℕ →₀ ℕ` with the same shift: the paper's
`ε_k` (`k ≥ 1`) is `ε (k - 1)`, its basis coefficient function `β^k` is `Finsupp.single (k - 1) 1`,
`res_m(ε)` (indices `≤ m`) is `ε.filter (· < m)` and `res^m(ε)` (indices `≥ m`) is
`ε.filter (m - 1 ≤ ·)`.

Sections 3.3-4 (the function `δ*` on `(0, 1)`, its continuity, differentiability and extrema) are
checked against the journal text (INTEGERS 25 (2025), Article A25, pp. 18-42); see the section
note before `IsPeriodicZeckendorfPair`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Powers of two are the only binary fundamental sequence.** Let
$H \colon \mathbb{N} \to \mathbb{N}$ be a strictly increasing sequence of positive integers. Then
every natural number (including $0$) equals $\sum_{k \in s} H_k$ for exactly one finite set
$s \subseteq \mathbb{N}$ if and only if $H_k = 2^k$ for all $k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem_wanted bijective_finset_sum_iff_eq_two_pow {H : ℕ → ℕ} (hpos : ∀ k, 0 < H k)
    (hmono : StrictMono H) :
    Function.Bijective (fun s : Finset ℕ => ∑ k ∈ s, H k) ↔ ∀ k, H k = 2 ^ k

/-- **The Fibonacci numbers are the only Zeckendorf fundamental sequence.** Let
$H \colon \mathbb{N} \to \mathbb{N}$ be a strictly increasing sequence of positive integers, and
call a finite set $s \subseteq \mathbb{N}$ nonadjacent if $k \in s$ implies $k + 1 \notin s$.
Then every natural number (including $0$) equals $\sum_{k \in s} H_k$ for exactly one nonadjacent
finite set $s$ if and only if $H_k = F_{k+2}$ for all $k$, where $F_0 = 0$, $F_1 = 1$ and
$F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem_wanted bijective_nonadjacent_finset_sum_iff_eq_fib {H : ℕ → ℕ}
    (hpos : ∀ k, 0 < H k) (hmono : StrictMono H) :
    Function.Bijective (fun s : {s : Finset ℕ // ∀ k ∈ s, k + 1 ∉ s} => ∑ k ∈ s.1, H k) ↔
      ∀ k, H k = Nat.fib (k + 2)

/-- **Duality formula for binary expansions without adjacent ones.** For $x \in \mathbb{N}$ let
$z(x)$ be the number of $n < x$ whose binary expansion has no two adjacent digits equal to $1$.
For a finite set $A \subseteq \mathbb{N}$, put $\bar A = A$ if there is no $j$ with
$j, j + 1 \in A$, and otherwise $\bar A = \{k \in A : k \ge j\}$, where $j$ is the largest index
with $j, j + 1 \in A$. Then $z\bigl(\sum_{k \in A} 2^k\bigr) = \sum_{k \in \bar A} F_{k+2}$,
where $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 2 (`integers-2025-A25-lem-2`). -/
public theorem_wanted card_zeckendorfBinary_lt_sum_two_pow (A : Finset ℕ) :
    let J := A.filter (fun j => j + 1 ∈ A)
    let Abar := if h : J.Nonempty then A.filter (fun k => J.max' h ≤ k) else A
    ((Finset.range (∑ k ∈ A, 2 ^ k)).filter (fun n => n &&& (n >>> 1) = 0)).card =
      ∑ k ∈ Abar, Nat.fib (k + 2)

/-- **Ascending lexicographic order.** For coefficient functions
$\mu, \nu \colon \mathbb{N} \to \mathbb{N}$ with finite support, $\mu <_a \nu$ means that there
is an index $k$ with $\mu_k < \nu_k$ and $\mu_j = \nu_j$ for all $j > k$: at the largest index
where they differ, $\mu$ is smaller.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def AscLexLT (μ ν : ℕ →₀ ℕ) : Prop :=
  ∃ k, μ k < ν k ∧ ∀ j, k < j → μ j = ν j

/-- **Example of the ascending lexicographic order.** Write $(a_0, a_1, a_2, a_3, a_4)$ for the
coefficient function with finite support whose entry at index $i \le 4$ is $a_i$ and whose other
entries are $0$. Then $(1, 2, 10, 3, 7) <_a (1, 3, 1, 4, 7)$ in the ascending lexicographic
order: the largest index where they differ is $3$, where $3 < 4$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2, example). -/
public theorem ascLexLT_example :
    AscLexLT (Finsupp.single 0 1 + Finsupp.single 1 2 + Finsupp.single 2 10 +
        Finsupp.single 3 3 + Finsupp.single 4 7)
      (Finsupp.single 0 1 + Finsupp.single 1 3 + Finsupp.single 2 1 + Finsupp.single 3 4 +
        Finsupp.single 4 7) := by
  refine ⟨3, by simp, fun j hj => ?_⟩
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- **Immediate predecessor.** Let $E$ be a collection of finitely supported coefficient functions
$\mathbb N \to \mathbb N$, and let $<_a$ be the ascending lexicographic order. A finitely supported
coefficient function $\mu$ is the immediate predecessor of $\nu$ in $E$ if $\mu \in E$,
$\mu <_a \nu$, and every $\xi \in E$ with $\xi <_a \nu$ satisfies $\xi = \mu$ or $\xi <_a \mu$.
That is, $\mu$ is the largest element of $E$ that is $<_a \nu$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediatePredecessor (E : Set (ℕ →₀ ℕ)) (ν μ : ℕ →₀ ℕ) : Prop :=
  μ ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT ξ ν → ξ = μ ∨ AscLexLT ξ μ

/-- **Immediate successor.** Let $E$ be a collection of finitely supported coefficient functions
$\mathbb N \to \mathbb N$, and let $<_a$ be the ascending lexicographic order. A finitely supported
coefficient function $\nu$ is the immediate successor of $\mu$ in $E$ if $\nu \in E$,
$\mu <_a \nu$, and every $\xi \in E$ with $\mu <_a \xi$ satisfies $\xi = \nu$ or $\nu <_a \xi$.
That is, $\nu$ is the smallest element of $E$ that is $>_a \mu$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediateSuccessor (E : Set (ℕ →₀ ℕ)) (μ ν : ℕ →₀ ℕ) : Prop :=
  ν ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT μ ξ → ξ = ν ∨ AscLexLT ν ξ

/-- **Zeckendorf collections.** Index coefficient functions from $1$, let $\beta^n$ be the basis
coefficient function with entry $1$ at index $n$, and for a coefficient function $\mu$ let
$\operatorname{res}_n(\mu)$ keep the entries of $\mu$ at indices $\le n$ and
$\operatorname{res}^n(\mu)$ keep those at indices $\ge n$, the other entries being $0$. A set $E$
of finitely supported coefficient functions $\mathbb N \to \mathbb N$ is a Zeckendorf collection
when it contains $0$ and $\beta^n$ for every $n \ge 1$, every $\mu \in E$ has only finitely many
elements of $E$ below it in the ascending lexicographic order $<_a$, and for every $\mu \in E$
and every immediate successor $\tilde\mu$ of $\mu$ in $E$ with $\tilde\mu \ne \beta^1 + \mu$
there is an index $n \ge 2$ such that $\operatorname{res}_{n-1}(\mu)$ is the immediate
predecessor of $\beta^n$ in $E$ and $\tilde\mu = \beta^n + \operatorname{res}^n(\mu)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsZeckendorfCollection (E : Set (ℕ →₀ ℕ)) : Prop :=
  0 ∈ E ∧ (∀ i, Finsupp.single i 1 ∈ E) ∧ (∀ μ ∈ E, {ν | ν ∈ E ∧ AscLexLT ν μ}.Finite) ∧
    ∀ μ ∈ E, ∀ ν, IsImmediateSuccessor E μ ν → ν ≠ Finsupp.single 0 1 + μ →
      ∃ m, 1 ≤ m ∧ IsImmediatePredecessor E (Finsupp.single m 1) (μ.filter (· < m)) ∧
        ν = Finsupp.single m 1 + μ.filter (m ≤ ·)

/-- **Zeckendorf collections contain zero.** Every Zeckendorf collection $E$ of finitely supported
coefficient functions $\mathbb N \to \mathbb N$ contains the zero coefficient function.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public theorem IsZeckendorfCollection.zero_mem {E : Set (ℕ →₀ ℕ)} (h : IsZeckendorfCollection E) :
    0 ∈ E :=
  h.1

/-- **The maximal $L$-block $\theta^{m+1}$.** Let $L = (e_1, \dots, e_N)$ be a list of natural
numbers and $m \in \mathbb N$, with indices of coefficient functions starting at $0$. The maximal
$L$-block $\theta^{m+1}$ is the finitely supported coefficient function whose entry at each index
$i < m$ is $e_j$, where $j - 1 = (m - 1 - i) \bmod N$, and whose entries at the indices $i \ge m$
are $0$ (every entry is $0$ when $L$ is empty).

In the paper's one-based indexing, $\theta^n = \mathrm{rev}_{n-1}(\beta^*)$, where $\beta^*$ is
the coefficient function with $\beta^*_k = e_j$ for $k \equiv j \pmod N$ and
$\mathrm{rev}_{n-1}(\beta^*)$ lists the first $n - 1$ entries of $\beta^*$ in reverse order,
followed by zeros.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public noncomputable def periodicTheta (L : List ℕ) (m : ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ Finset.range m, Finsupp.single i (L.getD ((m - 1 - i) % L.length) 0)

/-- **The maximal block $\theta^4$ in the Fibonacci case.** For $L = (1, 0)$, the maximal $L$-block
$\theta^4$ is $(1, 0, 1)$: its entries at indices $0$, $1$, $2$ are $1$, $0$, $1$, and all its
entries from index $3$ on are $0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public theorem periodicTheta_one_zero_three :
    periodicTheta [1, 0] 3 = Finsupp.single 0 1 + Finsupp.single 2 1 := by
  simp [periodicTheta, Finset.sum_range_succ]

/-- **L-blocks.** Let $L$ be a list of natural numbers, and for each $m$ let $\theta^{m+1}$ be the
maximal $L$-block, which vanishes from index $m$ on (indices are zero-based). A finitely supported
coefficient function $\zeta$ is an $L$-block with support interval $[s, m - 1]$ if $1 \le m$,
$s < m$, and either $s = 0$ and $\zeta = \theta^{m+1}$, or $\zeta_i = \theta^{m+1}_i$ for every
$i > s$, $\zeta_s < \theta^{m+1}_s$ and $\zeta_i = 0$ for every $i < s$.

In the paper's indexing this is a block at index $n - 1$ with $n = m + 1 \ge 2$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public def IsLBlock (L : List ℕ) (ζ : ℕ →₀ ℕ) (lo m : ℕ) : Prop :=
  1 ≤ m ∧ lo < m ∧
    ((lo = 0 ∧ ζ = periodicTheta L m) ∨
      (ζ.filter (lo < ·) = (periodicTheta L m).filter (lo < ·) ∧ ζ lo < periodicTheta L m lo ∧
        ζ.filter (· < lo) = 0))

/-- **Periodic Zeckendorf collection.** For a list $L$ of natural numbers, the periodic Zeckendorf
collection determined by $L$ is the set of finitely supported coefficient functions $\mu$ that
can be written as a sum $\mu = \zeta_1 + \dots + \zeta_r$ of finitely many $L$-blocks
$\zeta_1, \dots, \zeta_r$ (possibly none, which gives $\mu = 0$) whose support intervals are
pairwise disjoint.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 4 and the definition following it (arXiv:2308.12872v1, Section 2.2). -/
public def periodicZeckendorfCollection (L : List ℕ) : Set (ℕ →₀ ℕ) :=
  {μ | ∃ blocks : List ((ℕ →₀ ℕ) × ℕ × ℕ), (∀ b ∈ blocks, IsLBlock L b.1 b.2.1 b.2.2) ∧
    blocks.Pairwise (fun a b => a.2.2 ≤ b.2.1 ∨ b.2.2 ≤ a.2.1) ∧ μ = (blocks.map Prod.fst).sum}

/-- **Evaluation of a coefficient function at an integer sequence.** For a sequence $H$ of
natural numbers and a finitely supported coefficient function
$\varepsilon \colon \mathbb{N} \to \mathbb{N}$, the evaluation of $\varepsilon$ at $H$ is the
natural number $\mathrm{eval}_H(\varepsilon) = \sum_{k \ge 0} \varepsilon_k H_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 1 (arXiv:2308.12872v1, Section 1). -/
public def zeckendorfEval (H : ℕ → ℕ) (ε : ℕ →₀ ℕ) : ℕ :=
  ε.sum fun k a => a * H k

/-- **Zeckendorf collections are determined by their immediate predecessors.** Index
coefficient functions from $0$, and for $m \in \mathbb N$ let $\beta^{(m)}$ be the coefficient
function with entry $1$ at index $m$ and $0$ elsewhere. Suppose that for each $m \ge 1$ a finitely
supported coefficient function $\theta^{(m)}$ is given whose entry at index $m - 1$ is nonzero and
whose entries at all indices $j \ge m$ are $0$. Then there is a unique Zeckendorf collection $E$
such that, for every $m \ge 1$, $\theta^{(m)}$ is the immediate predecessor of $\beta^{(m)}$ in
$E$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 3 (`integers-2025-A25-thm-3`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted existsUnique_zeckendorfCollection (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → θ m (m - 1) ≠ 0 ∧ ∀ j, m ≤ j → θ m j = 0) :
    ∃! E : Set (ℕ →₀ ℕ), IsZeckendorfCollection E ∧
      ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)

/-- **Periodic collections are Zeckendorf collections.** Let $L = (e_1, \dots, e_N)$ be a list of
natural numbers with $N \ge 2$ and $e_1 \ne 0$, and let $E$ be the periodic Zeckendorf collection
determined by $L$ (the sums of finitely many $L$-blocks with pairwise disjoint support
intervals). Index coefficient functions from $1$ and let $\beta^n$ be the basis coefficient
function with entry $1$ at index $n$. Then $E$ is a Zeckendorf collection, and for every
$n \ge 2$ the immediate predecessor of $\beta^n$ in $E$ is the maximal $L$-block $\theta^n$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 4 (`integers-2025-A25-thm-4`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted isZeckendorfCollection_periodic (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    IsZeckendorfCollection (periodicZeckendorfCollection L) ∧
      ∀ m, 1 ≤ m → IsImmediatePredecessor (periodicZeckendorfCollection L)
        (Finsupp.single m 1) (periodicTheta L m)

/-- **Fundamental sequences of Zeckendorf collections.** Let $E$ be a Zeckendorf collection and
index coefficient functions and sequences from $0$. Suppose that, for each $m \ge 1$,
$\theta^{(m)}$ is the immediate predecessor in $E$ of the coefficient function with entry $1$ at
index $m$ and $0$ elsewhere. For a sequence $H$ write $\mathrm{eval}_H(\mu) = \sum_k \mu_k H_k$.
Then there is a unique strictly increasing sequence $H$ of positive integers such that
$\mathrm{eval}_H$ is a bijection from $E$ onto $\mathbb N$. Moreover, every such $H$ satisfies
$H_m = H_0 + \mathrm{eval}_H(\theta^{(m)})$ for all $m \ge 1$, and for all $\mu, \nu \in E$,
$\mu <_a \nu$ (that is, $\mu_k < \nu_k$ at the largest index $k$ where $\mu$ and $\nu$ differ)
if and only if $\mathrm{eval}_H(\mu) < \mathrm{eval}_H(\nu)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 5 (`integers-2025-A25-thm-5`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted existsUnique_zeckendorf_fundamentalSequence {E : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)) :
    (∃! H : ℕ → ℕ, StrictMono H ∧ (∀ k, 0 < H k) ∧ Set.BijOn (zeckendorfEval H) E Set.univ) ∧
      ∀ H : ℕ → ℕ, StrictMono H → (∀ k, 0 < H k) → Set.BijOn (zeckendorfEval H) E Set.univ →
        (∀ m, 1 ≤ m → H m = H 0 + zeckendorfEval H (θ m)) ∧
          ∀ μ ∈ E, ∀ ν ∈ E, (AscLexLT μ ν ↔ zeckendorfEval H μ < zeckendorfEval H ν)

/-- **Criterion for one Zeckendorf collection to contain another.** Let $E$ and $\tilde E$ be
Zeckendorf collections. For $n \ge 2$ let $\beta^n$ be the basis coefficient function with entry
$1$ at position $n$ (positions counted from $1$) and $0$ elsewhere, and let $\hat\beta^n$ be the
immediate predecessor of $\beta^n$ in $E$ (the largest element of $E$ that is $<_a \beta^n$ in the
ascending lexicographic order). Then $E \subseteq \tilde E$ if and only if
$\hat\beta^n \in \tilde E$ for all $n \ge 2$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 1 (`integers-2025-A25-prop-1`; arXiv:2308.12872v1, Section 2.2). -/
public theorem_wanted zeckendorfCollection_subset_iff {E E' : Set (ℕ →₀ ℕ)}
    (hE' : IsZeckendorfCollection E') (hE : IsZeckendorfCollection E) (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)) :
    E ⊆ E' ↔ ∀ m, 1 ≤ m → θ m ∈ E'

/-- **Counting function of a subcollection.** For a set $E$ of finitely supported coefficient
functions $\mu : \mathbb{N} \to \mathbb{N}$, a sequence $H : \mathbb{N} \to \mathbb{N}$ and a
real number $x$, $z(x)$ is the number of natural numbers $n < x$ of the form
$n = \sum_k \mu_k H_k$ for some $\mu \in E$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1 and Section 3 (arXiv:2308.12872v1, Sections 1 and 3.2). -/
public noncomputable def subcollectionCount (E : Set (ℕ →₀ ℕ)) (H : ℕ → ℕ) (x : ℝ) : ℕ :=
  {n : ℕ | (n : ℝ) < x ∧ ∃ μ ∈ E, zeckendorfEval H μ = n}.ncard

/-- **The counting function $z$ vanishes for $x \le 0$.** Let $E$ be a set of finitely supported
coefficient functions and $H$ a sequence of natural numbers, and for real $x$ let $z(x)$ be the
number of natural numbers $n < x$ of the form $n = \sum_k \mu_k H_k$ with $\mu \in E$. Then
$z(x) = 0$ for every real $x \le 0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3 (arXiv:2308.12872v1, Section 3.2). -/
public theorem subcollectionCount_of_nonpos (E : Set (ℕ →₀ ℕ)) (H : ℕ → ℕ) {x : ℝ}
    (hx : x ≤ 0) : subcollectionCount E H x = 0 := by
  have h : {n : ℕ | (n : ℝ) < x ∧ ∃ μ ∈ E, zeckendorfEval H μ = n} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hn
    exact absurd hn (not_lt.mpr (le_trans hx (Nat.cast_nonneg n)))
  simp [subcollectionCount, h]

/-- **Power-law bounds for the subcollection count.** Let $L$ and $\tilde L$ be lists of natural
numbers of length at least $2$ with nonzero first entries, and let $E$ and $\tilde E$ be the
periodic Zeckendorf collections they determine, with $E$ a proper subset of $\tilde E$. Let
$\tilde H$ be a strictly increasing sequence of positive integers such that
$\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto $\mathbb N$, and let
$z(x)$ be the number of natural numbers $n < x$ of the form $\sum_k \mu_k \tilde H_k$ with
$\mu \in E$. Then there are reals $\gamma$, $a$ and $b$ with $0 < \gamma < 1$, $a > 0$ and $b > 0$
such that $a < z(x) / x^\gamma < b$ for all sufficiently large real $x$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1 (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1, with the standing
assumption of Section 3 that `E` is a proper subcollection). -/
public theorem_wanted exists_rpow_bounds_subcollectionCount (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H' : ℕ → ℕ}
    (hmono : StrictMono H') (hpos : ∀ k, 0 < H' k)
    (hbij : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ γ a b : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < a ∧ 0 < b ∧ ∀ᶠ x in Filter.atTop,
      a < (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) / x ^ γ ∧
        (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) / x ^ γ < b

/-- **Limsup of the count of binary expansions without adjacent ones.** For real $x$ let $z(x)$
be the number of natural numbers $n < x$ (including $0$) whose binary expansion has no two
adjacent $1$s, let $\varphi$ be the golden ratio and let $\gamma = \log_2 \varphi$. Then
$\limsup_{x \to \infty} z(x) / x^{\gamma} = 3^{\gamma} (\varphi + 2) / 5$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1, Equation (1) (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted limsup_zeckendorfBinaryCount_div_rpow :
    Filter.limsup (fun x : ℝ =>
      ({n : ℕ | (n : ℝ) < x ∧ n &&& (n >>> 1) = 0}.ncard : ℝ) /
        x ^ Real.logb 2 Real.goldenRatio) Filter.atTop =
      3 ^ Real.logb 2 Real.goldenRatio * (Real.goldenRatio + 2) / 5

/-- **Liminf of the count of binary expansions without adjacent ones.** For real $x$ let $z(x)$
be the number of natural numbers $n < x$ (including $0$) whose binary expansion has no two
adjacent $1$s, let $\varphi$ be the golden ratio and let $\gamma = \log_2 \varphi$. Then
$\liminf_{x \to \infty} z(x) / x^{\gamma} = (3\varphi + 1) / 5$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1, Equation (1) (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted liminf_zeckendorfBinaryCount_div_rpow :
    Filter.liminf (fun x : ℝ =>
      ({n : ℕ | (n : ℝ) < x ∧ n &&& (n >>> 1) = 0}.ncard : ℝ) /
        x ^ Real.logb 2 Real.goldenRatio) Filter.atTop =
      (3 * Real.goldenRatio + 1) / 5

/-- **Asymptotic form of the subcollection count.** Let $L$ and $\tilde L$ be lists of natural
numbers of length at least $2$ with nonzero first entries, and let $E$ and $\tilde E$ be the
periodic Zeckendorf collections they determine, with $E$ a proper subset of $\tilde E$. Let
$\tilde H$ be a strictly increasing sequence of positive integers such that
$\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto $\mathbb N$, and let
$z(x)$ be the number of natural numbers $n < x$ of the form $\sum_k \mu_k \tilde H_k$ with
$\mu \in E$. Then there are reals $\gamma$ and $\tilde\varphi$ with $0 < \gamma < 1$ and
$\tilde\varphi > 1$, and a continuous function $\Phi : \mathbb R \to \mathbb R$, such that
$z(x) \sim x^\gamma \Phi(\{\log_{\tilde\varphi} x\})$ as $x \to \infty$, where $\{t\}$ is the
fractional part of $t$, and $\Phi$ is differentiable at almost every point of $(0, 1)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 2 (`integers-2025-A25-thm-2`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted exists_isEquivalent_subcollectionCount (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H' : ℕ → ℕ}
    (hmono : StrictMono H') (hpos : ∀ k, 0 < H' k)
    (hbij : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ γ φ' : ℝ, 0 < γ ∧ γ < 1 ∧ 1 < φ' ∧ ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun x : ℝ => (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ))
        (fun x : ℝ => x ^ γ * Φ (Int.fract (Real.logb φ' x))) ∧
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 → DifferentiableAt ℝ Φ t

/-- **Growth of fundamental sequences.** Let $L$ and $\tilde L$ be lists of natural numbers of
length at least $2$ with nonzero first entries, and let $E$ and $\tilde E$ be the periodic
Zeckendorf collections they determine, with $E$ a proper subset of $\tilde E$. Let $H$ and
$\tilde H$ be strictly increasing sequences of positive integers, indexed from $0$, such that
$\mu \mapsto \sum_k \mu_k H_k$ is a bijection from $E$ onto $\mathbb N$ and
$\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto $\mathbb N$. Then there
are reals $\alpha > 0$, $\tilde\alpha > 0$, $\varphi$, $\tilde\varphi$ and $r$ with
$1 < \varphi < \tilde\varphi$ and $0 < r < 1$ such that, as $n \to \infty$,
$H_n - \alpha \varphi^n = O(\varphi^{nr})$, $\tilde H_n - \tilde\alpha \tilde\varphi^n =
O(\tilde\varphi^{nr})$ and, with $\gamma = \log_{\tilde\varphi} \varphi$,
$H_n / \tilde H_n^{\gamma} \to \alpha / \tilde\alpha^{\gamma}$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 7 (`integers-2025-A25-thm-7`; arXiv:2308.12872v1, Section 3.1). -/
public theorem_wanted fundamentalSequence_div_rpow_tendsto (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H H' : ℕ → ℕ}
    (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) (periodicZeckendorfCollection L) Set.univ)
    (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ α α' φ φ' r : ℝ, 0 < α ∧ 0 < α' ∧ 1 < φ ∧ φ < φ' ∧ 0 < r ∧ r < 1 ∧
      (fun n : ℕ => (H n : ℝ) - α * φ ^ n) =O[Filter.atTop] (fun n : ℕ => φ ^ ((n : ℝ) * r)) ∧
      (fun n : ℕ => (H' n : ℝ) - α' * φ' ^ n) =O[Filter.atTop]
        (fun n : ℕ => φ' ^ ((n : ℝ) * r)) ∧
      Filter.Tendsto (fun n : ℕ => (H n : ℝ) / (H' n : ℝ) ^ Real.logb φ' φ) Filter.atTop
        (nhds (α / α' ^ Real.logb φ' φ))

/-- **Reduction lemma for counting a subcollection.** Let $E \subseteq \tilde E$ be Zeckendorf
collections, and let $\tilde H$ be a strictly increasing sequence of positive integers such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde H_k$ is a bijection from $\tilde E$ onto
$\mathbb{N}$. For a natural number $x$ let $R(x)$ be the set of natural numbers $n < x$ of the
form $n = \sum_k \varepsilon_k \tilde H_k$ with $\varepsilon \in E$. Let $\mu \in \tilde E$ be
nonzero, suppose that $\mu$ has an immediate predecessor $\check\mu$ in $E$ (the largest element
of $E$ that is $<_a \mu$ in the ascending lexicographic order), and suppose that $\check\mu$ has
an immediate successor $\bar\mu$ in $E$ (the smallest element of $E$ that is $>_a \check\mu$).
Then $R(\sum_k \mu_k \tilde H_k) = R(\sum_k \bar\mu_k \tilde H_k)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 7 (`integers-2025-A25-lem-7`; arXiv:2308.12872v1, Section 3.2, with the paper's
definition of `μ̌` and `μ̄` there). -/
public theorem_wanted subcollectionLT_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H' : ℕ → ℕ} (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ) {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E')
    (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc) (hb : IsImmediateSuccessor E μc μb) :
    {n : ℕ | n < zeckendorfEval H' μ ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n} =
      {n : ℕ | n < zeckendorfEval H' μb ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n}

/-- **Duality formula.** Let $E \subseteq \tilde E$ be Zeckendorf collections. Let $H$ and
$\tilde H$ be strictly increasing sequences of positive integers such that
$\mu \mapsto \sum_k \mu_k H_k$ is a bijection from $E$ onto $\mathbb N$ and
$\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto $\mathbb N$. For real
$x$, let $z(x)$ be the number of natural numbers $n < x$ of the form $n = \sum_k \nu_k \tilde H_k$
with $\nu \in E$. Let $\mu \in \tilde E$ be nonzero, let $\check\mu$ be the immediate predecessor
of $\mu$ in $E$ (the largest element of $E$ below $\mu$ in the ascending lexicographic order), and
let $\bar\mu$ be the immediate successor of $\check\mu$ in $E$. Then
$z\left(\sum_k \mu_k \tilde H_k\right) = \sum_k \bar\mu_k H_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 8 (`integers-2025-A25-thm-8`; arXiv:2308.12872v1, Section 3.2). -/
public theorem_wanted subcollectionCount_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H H' : ℕ → ℕ} (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) E Set.univ) (hmono' : StrictMono H')
    (hpos' : ∀ k, 0 < H' k) (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ)
    {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E') (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc)
    (hb : IsImmediateSuccessor E μc μb) :
    subcollectionCount E H' (zeckendorfEval H' μ) = zeckendorfEval H μb

/-- **Descending lexicographic order.** For coefficient functions
$\varepsilon, \varepsilon' \colon \mathbb{N} \to \mathbb{N}$, $\varepsilon <_d \varepsilon'$
means that there is an index $k$ with $\varepsilon_k < \varepsilon'_k$ and
$\varepsilon_j = \varepsilon'_j$ for all $j < k$: at the smallest index where they differ,
$\varepsilon$ is smaller.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def DescLexLT (ε ε' : ℕ → ℕ) : Prop :=
  ∃ k, ε k < ε' k ∧ ∀ j, j < k → ε j = ε' j

/-- **The maximal $L^*$-block.** Let $L = (e_1, \dots, e_N)$ be a list of natural numbers and $s$
an index, with indices starting at $0$. The maximal $L^*$-block starting at $s$ is the
coefficient function whose entry at index $i$ is $0$ for $i < s$, and $e_j$ for $i \ge s$, where
$j - 1 = (i - s) \bmod N$ (every entry is $0$ when $L$ is empty). It is the paper's
$\bar\beta^{s+1}$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def maxLStarBlock (L : List ℕ) (s i : ℕ) : ℕ :=
  if i < s then 0 else L.getD ((i - s) % L.length) 0

/-- **The maximal block $\bar\beta^2$ for $L = (2, 3, 0)$.** For $L = (2, 3, 0)$, the maximal
$L^*$-block starting at index $1$ (indices start at $0$; the paper's $\bar\beta^2$) has entries
$0, 2, 3, 0, 2$ at the indices $0, 1, 2, 3, 4$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3, example). -/
public theorem maxLStarBlock_example :
    (List.range 5).map (maxLStarBlock [2, 3, 0] 1) = [0, 2, 3, 0, 2] := by
  decide

/-- **Proper $L^*$-blocks.** Let $L$ be a list of natural numbers, index coefficient functions
from $1$, and let $\bar\beta^s$ be the maximal $L^*$-block starting at index $s$. For $s \ge 1$,
a function $\zeta : \mathbb N \to \mathbb N$ is a proper $L^*$-block with support interval
$[s, k]$ when $s \le k$, $\zeta_i = \bar\beta^s_i$ for all $i < k$, $\zeta_k < \bar\beta^s_k$,
and $\zeta_i = 0$ for all $i > k$. Since $\bar\beta^s$ vanishes below $s$, so does $\zeta$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsProperLStarBlock (L : List ℕ) (ζ : ℕ → ℕ) (s k : ℕ) : Prop :=
  s ≤ k ∧ (∀ i, i < k → ζ i = maxLStarBlock L s i) ∧ ζ k < maxLStarBlock L s k ∧
    ∀ i, k < i → ζ i = 0

/-- **Sums of disjoint proper $L^\ast$-blocks.** Let $L$ be a list of natural numbers, and for
each $s$ let $\bar\beta^{s+1}$ be the maximal $L^*$-block starting at (zero-based) index $s$. Let
$I$ be a finite or infinite set of pairs $(s, k)$ of natural numbers. A coefficient function
$\varepsilon : \mathbb N \to \mathbb N$ is the sum of the disjoint proper $L^*$-blocks with
support intervals $[s, k]$, $(s, k) \in I$, if $s \le k$ for every $(s, k) \in I$, the intervals
$[s, k]$ of distinct pairs in $I$ are pairwise disjoint, for every $(s, k) \in I$ we have
$\varepsilon_i = \bar\beta^{s+1}_i$ whenever $s \le i < k$ and
$\varepsilon_k < \bar\beta^{s+1}_k$, and $\varepsilon_i = 0$ for every index $i$ that lies in
none of the intervals.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsLStarBlockSum (L : List ℕ) (I : Set (ℕ × ℕ)) (ε : ℕ → ℕ) : Prop :=
  (∀ p ∈ I, p.1 ≤ p.2) ∧ I.PairwiseDisjoint (fun p => Set.Icc p.1 p.2) ∧
    (∀ p ∈ I, (∀ i, p.1 ≤ i → i < p.2 → ε i = maxLStarBlock L p.1 i) ∧
      ε p.2 < maxLStarBlock L p.1 p.2) ∧
    ∀ i, (∀ p ∈ I, i ∉ Set.Icc p.1 p.2) → ε i = 0

/-- **The periodic collection $E^*$.** For a list $L$ of natural numbers, $E^*$ is the set of
nonzero coefficient functions $\varepsilon : \mathbb{N} \to \mathbb{N}$ that are sums of finitely
or infinitely many disjoint proper $L^*$-blocks, that is, the $\varepsilon \ne 0$ that are
$L^*$-block sums over some set of support intervals. It is the collection $E^*$ for the interval
$(0, 1)$ determined by $L$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def lStarCollection (L : List ℕ) : Set (ℕ → ℕ) :=
  {ε | ε ≠ 0 ∧ ∃ I, IsLStarBlockSum L I ε}

/-- **The zero function is not in the periodic Zeckendorf collection for $(0, 1)$.** For every
list $L$ of natural numbers, the zero coefficient function $\mathbb{N} \to \mathbb{N}$ does not
belong to the periodic Zeckendorf collection $E^*$ for the interval $(0, 1)$ determined by $L$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public theorem zero_notMem_lStarCollection (L : List ℕ) : (0 : ℕ → ℕ) ∉ lStarCollection L :=
  fun h => h.1 rfl

/-- **Real Zeckendorf expansions.** Let $L = (e_1, \dots, e_N)$ be a list of natural numbers with
$N \ge 2$ and $e_1 \ne 0$, and let $E^*$ be its $L^*$-collection; indices of coefficient functions
and sequences start at $0$. There is a unique strictly decreasing sequence $(Q_m)_{m \ge 0}$ in
$(0, 1)$ such that $\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a bijection from $E^*$ onto
$(0, 1)$. Moreover, every such sequence $Q$ has the following properties: for
$\varepsilon, \delta \in E^*$, $\varepsilon <_d \delta$ (that is, $\varepsilon_k < \delta_k$ at
the smallest index $k$ where $\varepsilon$ and $\delta$ differ) if and only if
$\sum_k \varepsilon_k Q_k < \sum_k \delta_k Q_k$; for every $m$, $Q_m = \sum_k \bar\beta_k Q_k$,
where $\bar\beta$ is the maximal $L^*$-block starting at index $m + 1$; and if $\omega > 0$
satisfies $-1 + \sum_{k=1}^{N-1} e_k \omega^k + (1 + e_N) \omega^N = 0$, then
$Q_m = \omega^{m+1}$ for every $m$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6 (`integers-2025-A25-thm-6`; arXiv:2308.12872v1, Section 2.3, quoting Chang 2021). -/
public theorem_wanted existsUnique_lStar_fundamentalSequence (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    (∃! Q : ℕ → ℝ, StrictAnti Q ∧ (∀ n, 0 < Q n ∧ Q n < 1) ∧
      Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L) (Set.Ioo 0 1)) ∧
    ∀ Q : ℕ → ℝ, StrictAnti Q → (∀ n, 0 < Q n ∧ Q n < 1) →
      Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L) (Set.Ioo 0 1) →
      (∀ ε ∈ lStarCollection L, ∀ δ ∈ lStarCollection L,
        DescLexLT ε δ ↔ ∑' k, (ε k : ℝ) * Q k < ∑' k, (δ k : ℝ) * Q k) ∧
      (∀ m, Q m = ∑' k, (maxLStarBlock L (m + 1) k : ℝ) * Q k) ∧
      ∀ ω : ℝ, 0 < ω →
        -1 + ∑ k ∈ Finset.Ico 1 L.length, (L.getD (k - 1) 0 : ℝ) * ω ^ k +
          (1 + (L.getD (L.length - 1) 0 : ℝ)) * ω ^ L.length = 0 →
        ∀ m, Q m = ω ^ (m + 1)

/-- **The coefficient function $\inf(\varepsilon)$.** Let $L$ be a list of natural numbers and
$\varepsilon : \mathbb{N} \to \mathbb{N}$ a coefficient function, with indices starting at $0$.
If $\varepsilon$ has a last nonzero entry, at index $c$, then $\inf(\varepsilon)$ agrees with
$\varepsilon$ at the indices $i < c$, equals $\varepsilon_c - 1$ at $c$, and agrees with the
maximal $L^*$-block starting at index $c + 1$ at the indices $i > c$. Otherwise, that is, when
$\varepsilon$ has infinite support or is zero, $\inf(\varepsilon) = \varepsilon$.

In the paper's one-based indexing the last nonzero entry sits at index $c + 1$, and
$\inf(\varepsilon) = \operatorname{res}_{c+1}(\varepsilon) - \beta^{c+1} + \bar\beta^{c+2}$,
where $\operatorname{res}_{c+1}(\varepsilon)$ keeps the entries of $\varepsilon$ at the indices
at most $c + 1$, $\beta^{c+1}$ has a single entry $1$ at index $c + 1$ and zeros elsewhere, and
$\bar\beta^{c+2}$ is the maximal $L^*$-block starting at index $c + 2$ (all in paper indices).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public noncomputable def lStarInf (L : List ℕ) (ε : ℕ → ℕ) : ℕ → ℕ := by
  classical
  exact if h : ∃ c, ε c ≠ 0 ∧ ∀ i, c < i → ε i = 0 then
    fun i => if i < h.choose then ε i else if i = h.choose then ε i - 1
      else maxLStarBlock L (h.choose + 1) i
  else ε

/-- **$\inf(\varepsilon) = \varepsilon$ for infinite support.** Let $L$ be a list of natural
numbers and $\varepsilon : \mathbb{N} \to \mathbb{N}$ a coefficient function with infinitely many
nonzero entries (for every $c$ there is $i > c$ with $\varepsilon_i \ne 0$). Then
$\inf(\varepsilon) = \varepsilon$, where $\inf$ is taken with respect to $L$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public theorem lStarInf_of_infinite_support (L : List ℕ) {ε : ℕ → ℕ}
    (hε : ∀ c, ∃ i, c < i ∧ ε i ≠ 0) : lStarInf L ε = ε := by
  have h : ¬ ∃ c, ε c ≠ 0 ∧ ∀ i, c < i → ε i = 0 := by
    rintro ⟨c, -, hc⟩
    obtain ⟨i, hi, hne⟩ := hε c
    exact hne (hc i hi)
  simp [lStarInf, h]

/-- **$\varepsilon$ and $\inf(\varepsilon)$ have the same value.** Let $L$ be a list of natural
numbers of length at least $2$ with nonzero first entry, let $E^*$ be the set of nonzero
coefficient functions $\mathbb N \to \mathbb N$ that are sums of finitely or infinitely many
disjoint proper $L^*$-blocks, and let $Q$ be a strictly decreasing sequence in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a bijection from $E^*$ onto $(0, 1)$; indices
start at $0$. For $\varepsilon \in E^*$ define $\inf(\varepsilon)$ as follows: if $\varepsilon$
has infinitely many nonzero entries, then $\inf(\varepsilon) = \varepsilon$; otherwise, with $c$
the largest index such that $\varepsilon_c \ne 0$, $\inf(\varepsilon)$ agrees with $\varepsilon$
at the indices below $c$, has entry $\varepsilon_c - 1$ at index $c$, and agrees at the indices
above $c$ with the maximal $L^*$-block starting at index $c + 1$. Then every
$\varepsilon \in E^*$ satisfies $\sum_k \varepsilon_k Q_k = \sum_k \inf(\varepsilon)_k Q_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 4 (`integers-2025-A25-lem-4`; arXiv:2308.12872v1, Section 2.3). -/
public theorem_wanted tsum_lStarInf_mul_eq (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {Q : ℕ → ℝ} (hQ : StrictAnti Q) (hQ01 : ∀ n, 0 < Q n ∧ Q n < 1)
    (hbij : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L)
      (Set.Ioo 0 1)) {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L) :
    ∑' k, (ε k : ℝ) * Q k = ∑' k, (lStarInf L ε k : ℝ) * Q k

/-- **Nearby expansions share long prefixes.** Let $L$ be a list of natural numbers of length at
least $2$ with nonzero first entry, let $E^*$ be its $L^*$-collection, and let $Q$ be a strictly
decreasing sequence in $(0, 1)$ such that $\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a
bijection from $E^*$ onto $(0, 1)$; indices start at $0$. Let $\varepsilon \in E^*$, put
$x = \sum_k \varepsilon_k Q_k$, and let $n \in \mathbb N$. Define $\inf(\varepsilon)$ as follows:
if $\varepsilon$ has infinitely many nonzero entries, then $\inf(\varepsilon) = \varepsilon$;
otherwise, with $c$ the largest index such that $\varepsilon_c \ne 0$, $\inf(\varepsilon)$ agrees
with $\varepsilon$ at indices below $c$, has entry $\varepsilon_c - 1$ at index $c$, and agrees
at indices above $c$ with the maximal $L^*$-block starting at index $c + 1$. Then there is
$\delta > 0$ such that every $\varepsilon' \in E^*$ with
$x < \sum_k \varepsilon'_k Q_k < x + \delta$ satisfies $\varepsilon'_i = \varepsilon_i$ for all
$i \le n$, and every $\varepsilon' \in E^*$ with $x - \delta < \sum_k \varepsilon'_k Q_k < x$
satisfies $\varepsilon'_i = \inf(\varepsilon)_i$ for all $i \le n$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 5 (`integers-2025-A25-lem-5`; arXiv:2308.12872v1, Section 2.3). -/
public theorem_wanted exists_prefix_eq_of_lStar_near (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {Q : ℕ → ℝ} (hQ : StrictAnti Q) (hQ01 : ∀ n, 0 < Q n ∧ Q n < 1)
    (hbij : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L)
      (Set.Ioo 0 1)) {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L) (n : ℕ) :
    ∃ δ > 0,
      (∀ ε' ∈ lStarCollection L, ∑' k, (ε k : ℝ) * Q k < ∑' k, (ε' k : ℝ) * Q k →
        ∑' k, (ε' k : ℝ) * Q k < ∑' k, (ε k : ℝ) * Q k + δ → ∀ i ≤ n, ε' i = ε i) ∧
      (∀ ε' ∈ lStarCollection L, ∑' k, (ε k : ℝ) * Q k - δ < ∑' k, (ε' k : ℝ) * Q k →
        ∑' k, (ε' k : ℝ) * Q k < ∑' k, (ε k : ℝ) * Q k → ∀ i ≤ n, ε' i = lStarInf L ε i)

/-- **Proper blocks below a maximal block.** Let $L = (e_1, \dots, e_N)$ with $N \ge 2$ and
$e_1 \ne 0$, let $\varepsilon \colon \mathbb{N} \to \mathbb{N}$ and $b \in \mathbb{N}$ with
$\varepsilon_i = 0$ for all $i < b$, and let $\bar\beta$ be the maximal $L^*$-block starting at
index $b$. Then $\varepsilon <_d \bar\beta$ in the descending lexicographic order if and only if
there is $k \ge b$ such that the function equal to $\varepsilon_i$ for $i \le k$ and to $0$ for
$i > k$ is a proper $L^*$-block with support interval $[b, k]$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 8 (`integers-2025-A25-lem-8`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted descLexLT_maxLStarBlock_iff (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} {b : ℕ} (hε : ∀ i, i < b → ε i = 0) :
    DescLexLT ε (maxLStarBlock L b) ↔
      ∃ k, b ≤ k ∧ IsProperLStarBlock L (fun i => if i ≤ k then ε i else 0) b k

/-- **Decomposing $L^*$-blocks into $\tilde L^*$-blocks.** Let $L$ and $\tilde L$ be lists of
natural numbers of length at least $2$ with nonzero first entries whose periodic Zeckendorf
collections satisfy $E \subsetneq \tilde E$. If $\zeta$ is a nonzero proper $L^*$-block with
support interval $[i, b]$, then $\zeta$ is a sum of disjoint proper $\tilde L^*$-blocks whose
support intervals all lie in $[0, b]$, one of which has support interval $[a, b]$ for some $a$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 9 (`integers-2025-A25-lem-9`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted exists_lStarBlockSum_of_properLStarBlock (L L' : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {ζ : ℕ → ℕ}
    {i b : ℕ} (hζ : IsProperLStarBlock L ζ i b) (hζ0 : ζ ≠ 0) :
    ∃ I, IsLStarBlockSum L' I ζ ∧ (∀ p ∈ I, p.2 ≤ b) ∧ ∃ a, (a, b) ∈ I

/-- **The tail of an $L^\ast$-block decomposition lies in $\tilde E^\ast$.** Let $L$ and
$\tilde L$ be lists of natural numbers of length at least $2$ with nonzero first entries, such
that the periodic Zeckendorf collection $E$ of $L$ is a proper subset of the periodic Zeckendorf
collection $\tilde E$ of $\tilde L$, and let $\tilde E^*$ be the set of nonzero coefficient
functions $\mathbb N \to \mathbb N$ that are sums of finitely or infinitely many disjoint proper
$\tilde L^*$-blocks. Indices start at $0$. Let $\varepsilon \in \tilde E^*$ and $b \in \mathbb N$,
let $\eta$ agree with $\varepsilon$ at the indices $i < b$ and vanish at the indices $i \ge b$,
and let $\mu$ vanish at the indices $i < b$ and agree with $\varepsilon$ at the indices $i \ge b$.
Suppose that for some set $I$ of pairs $(s, k)$ with $k < b$, $\eta$ is the sum of the disjoint
proper $L^*$-blocks with support intervals $[s, k]$, $(s, k) \in I$, and that $\mu = \bar\beta$
or $\bar\beta <_d \mu$, where $\bar\beta$ is the maximal $L^*$-block starting at index $b$ (the
paper's $\bar\beta^{b+1}$) and $<_d$ is the descending lexicographic order. Then
$\mu \in \tilde E^*$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 2 (`integers-2025-A25-cor-2`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted mem_lStarCollection_of_lStarBar_decomposition (L L' : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {ε : ℕ → ℕ}
    (hε : ε ∈ lStarCollection L') {b : ℕ} {I : Set (ℕ × ℕ)}
    (hI : IsLStarBlockSum L I (fun i => if i < b then ε i else 0)) (hIb : ∀ p ∈ I, p.2 < b)
    (hμ : maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
      DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)) :
    (fun i => if i < b then 0 else ε i) ∈ lStarCollection L'

/-- **Shifted maximal blocks scale geometrically.** Let $L = (e_1, \dots, e_N)$ and $\tilde L$ be
lists of natural numbers of length at least $2$ with nonzero first entries, and let $\tilde Q$ be
a strictly decreasing sequence with values in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$ is a bijection from $\tilde E^*$, the
periodic Zeckendorf collection for $(0, 1)$ determined by $\tilde L$, onto $(0, 1)$. For
$s \in \mathbb{N}$ let $\bar\beta_s$ be the maximal $L^*$-block starting at index $s$: it is $0$
at indices $i < s$ and $e_j$ at indices $i \ge s$ with $j - 1 \equiv i - s \pmod N$. Then
$\sum_k (\bar\beta_s)_k \tilde Q_k = \tilde Q_0^{\,s} \sum_k (\bar\beta_0)_k \tilde Q_k$ for every
$s \in \mathbb{N}$.

Indices are zero-based: $\bar\beta_s$ is the paper's $\bar\beta^{s+1}$ and $\tilde Q_0$ is its
$\tilde Q_1 = \tilde\omega$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 16 (`integers-2025-A25-lem-16`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted tsum_maxLStarBlock_mul_eq (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0) {Q' : ℕ → ℝ}
    (hQ' : StrictAnti Q') (hQ'01 : ∀ n, 0 < Q' n ∧ Q' n < 1)
    (hbij' : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q' k) (lStarCollection L')
      (Set.Ioo 0 1)) (s : ℕ) :
    ∑' k, (maxLStarBlock L s k : ℝ) * Q' k = Q' 0 ^ s * ∑' k, (maxLStarBlock L 0 k : ℝ) * Q' k

/-- **Number of proper $L^*$-blocks with a given support interval.** Let
$L = (e_1, \dots, e_N)$ be a list of natural numbers with $N \ge 2$ and $e_1 \ne 0$, let $s \le k$
be natural numbers, and let $j$ be the integer with $1 \le j \le N$ and
$k - s + 1 \equiv j \pmod N$. Then there are exactly $e_j$ proper $L^*$-blocks with support
interval $[s, k]$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 15 (`integers-2025-A25-lem-15`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted ncard_properLStarBlock (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {s k : ℕ} (hsk : s ≤ k) :
    {ζ : ℕ → ℕ | IsProperLStarBlock L ζ s k}.ncard = L.getD ((k - s) % L.length) 0

/-- **Number of $L^*$-block sums of length $n$.** For a list $L$ of natural numbers and $n \ge 0$,
with coefficient functions indexed from $1$, $C_n$ is the number of functions
$\varepsilon : \mathbb N \to \mathbb N$ that are sums of disjoint proper $L^*$-blocks with
support intervals inside $[1, n]$. The zero function (the empty sum) is counted, so $C_0 = 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (arXiv:2308.12872v1, Section 4.1). -/
public noncomputable def lStarBlockSumCount (L : List ℕ) (n : ℕ) : ℕ :=
  {ε : ℕ → ℕ | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < n}.ncard

/-- **The empty block-sum count.** For every list $L$ of natural numbers, $C_0 = 1$, where $C_n$
is the number of sums of disjoint proper $L^*$-blocks with support intervals inside $[1, n]$:
for $n = 0$ the zero function is the only such sum.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (arXiv:2308.12872v1, Section 4.1, `S_0 = {0}`). -/
public theorem lStarBlockSumCount_zero (L : List ℕ) : lStarBlockSumCount L 0 = 1 := by
  have h : {ε : ℕ → ℕ | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < 0} = {0} := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.not_lt_zero]
    constructor
    · rintro ⟨I, h, hI⟩
      funext i
      exact h.2.2.2 i (fun p hp _ => hI p hp)
    · rintro rfl
      exact ⟨∅, ⟨by simp, by simp, by simp, fun _ _ => rfl⟩, by simp⟩
  rw [lStarBlockSumCount, h, Set.ncard_singleton]

/-- **Recurrence for the number of $L^*$-block sums.** Let $L = (e_1, \dots, e_N)$ be a list of
natural numbers with $N \ge 2$ and $e_1 \ne 0$, index coefficient functions from $1$, and let
$C_n$ be the number of functions $\mathbb N \to \mathbb N$ that are sums of disjoint proper
$L^*$-blocks with support intervals inside $[1, n]$. Then $C_k = \sum_{j=1}^{k} e_j C_{k-j}$ for
$1 \le k \le N$, and $C_n = \sum_{k=1}^{N-1} e_k C_{n-k} + (1 + e_N) C_{n-N}$ for $n \ge N + 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (`integers-2025-A25-prop-4`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted lStarBlockSumCount_recurrence (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    (∀ k, 1 ≤ k → k ≤ L.length → lStarBlockSumCount L k =
      ∑ j ∈ Finset.Icc 1 k, L.getD (j - 1) 0 * lStarBlockSumCount L (k - j)) ∧
    ∀ n, L.length + 1 ≤ n → lStarBlockSumCount L n =
      ∑ k ∈ Finset.Ico 1 L.length, L.getD (k - 1) 0 * lStarBlockSumCount L (n - k) +
        (1 + L.getD (L.length - 1) 0) * lStarBlockSumCount L (n - L.length)

/-- **Generating function of the $L^\ast$-block-sum counts.** Let $L = (e_1, \dots, e_N)$ be a
list of natural numbers with $N \ge 2$ and $e_1 \ne 0$. For each $k$ let $C_k$ be the number of
coefficient functions that are sums of disjoint proper $L^*$-blocks with support intervals inside
$[1, k]$ (the zero function included), and put
$f(x) = 1 - \sum_{k=1}^{N-1} e_k x^k - (1 + e_N) x^N$. Then there is a real $r > 0$ such that for
every real $x$ with $-r < x < r$ the series $\sum_{k \ge 0} C_k x^k$ converges absolutely, with
sum $(1 - x^N) / f(x)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 5 (`integers-2025-A25-prop-5`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted hasSum_lStarBlockSumCount (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Ioo (-r) r,
      HasSum (fun k => (lStarBlockSumCount L k : ℝ) * x ^ k)
        ((1 - x ^ L.length) / (1 - ∑ k ∈ Finset.Ico 1 L.length, (L.getD (k - 1) 0 : ℝ) * x ^ k -
          (1 + (L.getD (L.length - 1) 0 : ℝ)) * x ^ L.length))

/-! ### Sections 3.3-4: the function `δ*` on `(0, 1)`

Definitions and statements below follow the journal version (INTEGERS 25 (2025), Article A25,
pp. 7, 18-38). Zero-based conventions as above: the paper's `β̄^{b+1}` is `maxLStarBlock L b`, its
`β^b` is `Finsupp.single (b - 1) 1`, `res_n(ε)` keeps the indices `< n`, `Q_n` is `Q (n - 1)`,
`ω = Q 0` and `ω̃ = Q' 0` (Theorem 6 gives `Q m = ω ^ (m + 1)`), and `γ = log_φ̃ φ`
is `Real.logb (Q' 0) (Q 0)`. -/

/-- **Periodic Zeckendorf pairs.** Two lists $L$ and $\tilde L$ of natural numbers form a periodic
Zeckendorf pair when both have length at least $2$ and a nonzero first entry, and the periodic
Zeckendorf collection $E$ determined by $L$ is a proper subset of the periodic Zeckendorf
collection $\tilde E$ determined by $\tilde L$.

This is the standing assumption of Sections 3 and 4 of the source.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3.1. -/
public structure IsPeriodicZeckendorfPair (L L' : List ℕ) : Prop where
  two_le_length : 2 ≤ L.length
  head_ne_zero : L.getD 0 0 ≠ 0
  two_le_length' : 2 ≤ L'.length
  head_ne_zero' : L'.getD 0 0 ≠ 0
  ssubset : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L'

/-- **Periodic Zeckendorf pairs are nested.** If the lists $L$ and $\tilde L$ form a periodic
Zeckendorf pair, then the periodic Zeckendorf collection determined by $L$ is contained in the
periodic Zeckendorf collection determined by $\tilde L$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3.1. -/
public theorem IsPeriodicZeckendorfPair.subset {L L' : List ℕ} (h : IsPeriodicZeckendorfPair L L') :
    periodicZeckendorfCollection L ⊆ periodicZeckendorfCollection L' :=
  h.ssubset.subset

/-- **Evaluation of a coefficient function at a real sequence.** For a real sequence $Q$ and a
coefficient function $\varepsilon \colon \mathbb{N} \to \mathbb{N}$, not necessarily finitely
supported, the evaluation $\sum \varepsilon Q$ is the sum of the series
$\sum_{k \ge 0} \varepsilon_k Q_k$, taken to be $0$ when the series is not absolutely summable.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2.1. -/
public noncomputable def zeckendorfRealEval (Q : ℕ → ℝ) (ε : ℕ → ℕ) : ℝ :=
  ∑' k, (ε k : ℝ) * Q k

/-- **Evaluating the zero coefficient function.** For every real sequence $Q$, the evaluation of
the zero coefficient function at $Q$ is $0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2.1. -/
public theorem zeckendorfRealEval_zero (Q : ℕ → ℝ) : zeckendorfRealEval Q 0 = 0 := by
  simp [zeckendorfRealEval]

/-- **Fundamental sequence of an $L^\ast$-collection.** Let $L$ be a list of natural numbers with
$L^*$-collection $E^*$. A real sequence $(Q_n)_{n \ge 0}$ is a fundamental sequence of $E^*$ if
it is strictly decreasing, $0 < Q_n < 1$ for every $n$, and the map
$\varepsilon \mapsto \sum_k \varepsilon_k Q_k$ is a bijection from $E^*$ onto the open interval
$(0, 1)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6 and Definition 18. -/
public structure IsLStarFundamentalSequence (L : List ℕ) (Q : ℕ → ℝ) : Prop where
  strictAnti : StrictAnti Q
  mem_Ioo : ∀ n, Q n ∈ Set.Ioo (0 : ℝ) 1
  bijOn : Set.BijOn (zeckendorfRealEval Q) (lStarCollection L) (Set.Ioo 0 1)

/-- **Fundamental sequences of $E^*$ are positive.** Let $L$ be a list of natural numbers and let
$Q$ be a fundamental sequence of the collection $E^*$ determined by $L$. Then $Q_n > 0$ for every
$n$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6. -/
public theorem IsLStarFundamentalSequence.pos {L : List ℕ} {Q : ℕ → ℝ}
    (h : IsLStarFundamentalSequence L Q) (n : ℕ) : 0 < Q n :=
  (h.mem_Ioo n).1

/-- **Reversal of the first $n$ entries.** For $n \in \mathbb N$ and a coefficient function
$\varepsilon : \mathbb N \to \mathbb N$, $\mathrm{rev}_n(\varepsilon)$ is the finitely supported
coefficient function whose entry at index $j$ is $\varepsilon(n - 1 - j)$ for $j < n$ and $0$
for $j \ge n$ (indices start at $0$). In the paper's one-based indexing this is
$\mathrm{rev}_n(\varepsilon) = (\varepsilon_n, \dots, \varepsilon_1)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 5. -/
public noncomputable def zeckendorfRev (n : ℕ) (ε : ℕ → ℕ) : ℕ →₀ ℕ :=
  ∑ j ∈ Finset.range n, Finsupp.single j (ε (n - 1 - j))

/-- **Reversal of the first three entries.** For every coefficient function
$\varepsilon : \mathbb N \to \mathbb N$, $\mathrm{rev}_3(\varepsilon)$ is the finitely supported
coefficient function with entries $\varepsilon(2)$, $\varepsilon(1)$, $\varepsilon(0)$ at
indices $0$, $1$, $2$ and $0$ at every other index. In the paper's one-based indexing,
$\mathrm{rev}_3(\varepsilon) = (\varepsilon_3, \varepsilon_2, \varepsilon_1)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 5. -/
public theorem zeckendorfRev_three (ε : ℕ → ℕ) :
    zeckendorfRev 3 ε =
      Finsupp.single 0 (ε 2) + Finsupp.single 1 (ε 1) + Finsupp.single 2 (ε 0) := by
  simp [zeckendorfRev, Finset.sum_range_succ]

/-- **The coefficient function $\bar\mu$.** Let $E$ be a set of finitely supported coefficient
functions $\mathbb{N} \to \mathbb{N}$ and $\mu$ a finitely supported coefficient function. If
$\mu$ has an immediate predecessor $\check\mu$ in $E$ (the largest element of $E$ that is
$<_a \mu$ in the ascending lexicographic order) and $\check\mu$ has an immediate successor in
$E$ (the smallest element of $E$ that is $>_a \check\mu$), then $\bar\mu$ is that immediate
successor; otherwise $\bar\mu = 0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 20. -/
public noncomputable def zeckendorfBar (E : Set (ℕ →₀ ℕ)) (μ : ℕ →₀ ℕ) : ℕ →₀ ℕ := by
  classical
  exact if h : ∃ μb μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc μb then
    h.choose else 0

/-- **The bar of a coefficient function is a successor of its predecessor.** Let $E$ be a set of
finitely supported coefficient functions $\mathbb{N} \to \mathbb{N}$ and $\mu$ a finitely supported
coefficient function. Call $\nu$ an immediate predecessor of $\mu$ in $E$ if it is a largest
element of $E$ that is $<_a \mu$ in the ascending lexicographic order, and call $\xi$ an immediate
successor of $\nu$ in $E$ if it is a smallest element of $E$ that is $>_a \nu$. Let $\bar\mu$ be an
immediate successor in $E$ of an immediate predecessor of $\mu$ in $E$ if such a pair exists, and
$\bar\mu = 0$ otherwise. If some immediate predecessor of $\mu$ in $E$ has an immediate successor
in $E$, then $\bar\mu$ is the immediate successor in $E$ of some immediate predecessor of $\mu$ in
$E$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 20. -/
public theorem zeckendorfBar_spec {E : Set (ℕ →₀ ℕ)} {μ : ℕ →₀ ℕ}
    (h : ∃ μb μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc μb) :
    ∃ μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc (zeckendorfBar E μ) := by
  rw [zeckendorfBar, dite_eq_left h]
  exact h.choose_spec

/-- **The closure $\bar E^*$ of $E^*$.** Let $L$ be a list of natural numbers, $E^*$ the collection
determined by $L$, and index coefficient functions from $1$. The collection $\bar E^*$ consists
of the elements of $E^*$ together with every function $\varepsilon : \mathbb N \to \mathbb N$ for
which there is an index $b \ge 0$ such that the function agreeing with $\varepsilon$ at the
indices $\le b$ and vanishing elsewhere is a sum of disjoint proper $L^*$-blocks with support
intervals inside $[1, b]$, and $\varepsilon_i = \bar\beta^{b+1}_i$ for all $i \ge b + 1$, where
$\bar\beta^{b+1}$ is the maximal $L^*$-block starting at index $b + 1$. These extra functions
have the form $\sum_m \zeta^m + \bar\beta^{b+1}$ with proper $L^*$-blocks $\zeta^m$; the case
$b = 0$ gives $\bar\beta^1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 22. -/
public def lStarClosure (L : List ℕ) : Set (ℕ → ℕ) :=
  lStarCollection L ∪ {ε | ∃ b I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
    (∀ p ∈ I, p.2 < b) ∧ ∀ i, b ≤ i → ε i = maxLStarBlock L b i}

/-- **$\bar\beta^1$ lies in $\bar E^*$.** For every list $L$ of natural numbers, the maximal
$L^*$-block starting at index $0$ (the paper's $\bar\beta^1$) belongs to the collection $\bar E^*$
determined by $L$. This is the case of the definition of $\bar E^*$ with no proper blocks, in
which the maximal block starts at index $0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 22. -/
public theorem maxLStarBlock_zero_mem_lStarClosure (L : List ℕ) :
    maxLStarBlock L 0 ∈ lStarClosure L :=
  Set.mem_union_right _ ⟨0, ∅, ⟨by simp, by simp, by simp, fun i _ => by simp⟩, by simp,
    fun _ _ => rfl⟩

/-- **The map $\overline{\mathrm{rev}}$.** Fix a list $L$, and let $E$ be its periodic Zeckendorf
collection, $\bar\beta^1$ the maximal $L^*$-block starting at index $0$, $<_d$ the descending
lexicographic order, $\mathrm{rev}_n$ the reversal of the first $n$ entries, and $\bar\mu$ the
bar of a finitely supported $\mu$ relative to $E$. For a coefficient function
$\varepsilon : \mathbb N \to \mathbb N$, if $\varepsilon <_d \bar\beta^1$ fails then
$\overline{\mathrm{rev}}(\varepsilon) = \bar\beta^1$. If $\varepsilon <_d \bar\beta^1$, then
for each index $i$ the entry of $\overline{\mathrm{rev}}(\varepsilon)$ at $i$ is the eventual
value, as $n \to \infty$, of the entry of $\mathrm{rev}_n(\overline{\mathrm{rev}_n(\varepsilon)})$
at $i$ when that entry is eventually constant, and $0$ when it is not.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfRevBar (L : List ℕ) (ε : ℕ → ℕ) : ℕ → ℕ := by
  classical
  exact if DescLexLT ε (maxLStarBlock L 0) then
    fun i => if h : ∃ v, ∀ᶠ n in Filter.atTop,
        zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε)) i = v
      then h.choose else 0
  else maxLStarBlock L 0

/-- **$\overline{\mathrm{rev}}$ of a function not below $\bar\beta^1$.** Let $L$ be a list of
natural numbers, let $\bar\beta^1$ be the maximal $L^*$-block starting at index $0$, let $<_d$ be
the descending lexicographic order, and let $\overline{\mathrm{rev}}$ be the map determined by
$L$. For every coefficient function $\varepsilon : \mathbb N \to \mathbb N$ such that
$\varepsilon <_d \bar\beta^1$ fails, $\overline{\mathrm{rev}}(\varepsilon) = \bar\beta^1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public theorem zeckendorfRevBar_of_not_descLexLT (L : List ℕ) {ε : ℕ → ℕ}
    (h : ¬ DescLexLT ε (maxLStarBlock L 0)) : zeckendorfRevBar L ε = maxLStarBlock L 0 := by
  rw [zeckendorfRevBar, ite_eq_right h]

/-- **The function $\delta_1^\ast$.** Let $L$ and $\tilde L$ be lists of natural numbers and $Q$
and $\tilde Q$ real sequences with first terms $\omega = Q_0$ and $\tilde\omega = \tilde Q_0$
(indices start at $0$), and put $\gamma = \log_{\tilde\omega} \omega$. Let $\tilde E^*$ be the
collection $E^*$ determined by $\tilde L$, let $\overline{\mathrm{rev}}$ be the map determined by
$L$, and write $\sum \varepsilon R = \sum_k \varepsilon_k R_k$ for the evaluation of a coefficient
function $\varepsilon$ at a real sequence $R$. For real $y$: if some $\varepsilon \in \tilde E^*$
satisfies $\sum \varepsilon \tilde Q = y$, then
$\delta_1^*(y) = \sum \overline{\mathrm{rev}}(\varepsilon) Q / y^\gamma$ for a chosen such
$\varepsilon$; otherwise $\delta_1^*(y) = 0$.

In the paper $\delta_1^*$ is used on $[\tilde\omega, 1)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfDeltaStarOne (L L' : List ℕ) (Q Q' : ℕ → ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : ∃ ε ∈ lStarCollection L', zeckendorfRealEval Q' ε = y then
    zeckendorfRealEval Q (zeckendorfRevBar L h.choose) / y ^ Real.logb (Q' 0) (Q 0) else 0

/-- **The function $\delta^*$.** Let $L$ and $\tilde L$ be lists and $Q$ and $\tilde Q$ real
sequences, let $\tilde\omega$ be the first term of $\tilde Q$, and let $\delta_1^*$ be the function
$\delta_1^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$. For real $y$: if some natural number $m$
satisfies $\tilde\omega^{m+1} \le y < \tilde\omega^m$, then
$\delta^*(y) = \delta_1^*(y / \tilde\omega^m)$ for a chosen such $m$; otherwise
$\delta^*(y) = 0$.

When $0 < \tilde\omega < 1$, the intervals $[\tilde\omega^{m+1}, \tilde\omega^m)$ partition
$(0, 1)$, so $m$ is unique and $\delta^*$ vanishes outside $(0, 1)$. The printed Definition 23
reduces $y$ by powers of the first term $\omega$ of $Q$; since $\delta_1^*$ lives on
$[\tilde\omega, 1)$, Proposition 2 and Equation (12) evaluate $\delta^*$ on $[\tilde\omega, 1)$ as
$\delta_1^*$, and the proof of Theorem 9 glues
$\delta_1^*(\tilde\omega) = \lim_{x \to 1^-} \delta_1^*(x)$, the reduction is by powers of
$\tilde\omega$ (Notation 1).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfDeltaStar (L L' : List ℕ) (Q Q' : ℕ → ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : ∃ m : ℕ, Q' 0 ^ (m + 1) ≤ y ∧ y < Q' 0 ^ m then
    zeckendorfDeltaStarOne L L' Q Q' (y / Q' 0 ^ h.choose) else 0

/-- **$\delta^*$ agrees with $\delta_1^*$ on $[\tilde\omega, 1)$.** Let $L$ and $\tilde L$ be lists
and $Q$ and $\tilde Q$ real sequences such that the first term $\tilde\omega$ of $\tilde Q$
satisfies $0 < \tilde\omega < 1$. Then for every real $y$ with $\tilde\omega \le y < 1$, the
functions $\delta^*$ and $\delta_1^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$ agree at $y$:
$\delta^*(y) = \delta_1^*(y)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public theorem zeckendorfDeltaStar_of_mem_Ico {L L' : List ℕ} {Q Q' : ℕ → ℝ} (h0 : 0 < Q' 0)
    (h1 : Q' 0 < 1) {y : ℝ} (hy : Q' 0 ≤ y) (hy1 : y < 1) :
    zeckendorfDeltaStar L L' Q Q' y = zeckendorfDeltaStarOne L L' Q Q' y := by
  have h : ∃ m : ℕ, Q' 0 ^ (m + 1) ≤ y ∧ y < Q' 0 ^ m := ⟨0, by simpa using hy, by simpa using hy1⟩
  have hm : h.choose = 0 := by
    by_contra hne
    have h2 := h.choose_spec.2
    have h3 := pow_le_of_le_one h0.le h1.le hne
    linarith
  rw [zeckendorfDeltaStar, dite_eq_left h, hm, pow_zero, div_one]

/-- **The generic exponent.** Let $Q$ and $\tilde Q$ be real sequences with first terms $\omega$
and $\tilde\omega$, and put $\gamma = \log_{\tilde\omega} \omega$. The generic exponent $p$ of $Q$
and $\tilde Q$ is the smallest positive integer $p$ with $\gamma \tilde\omega^{p-1} < \omega^p$,
and $p = 0$ if no positive integer satisfies this inequality.

In the paper, $p$ is the exponent of the generic upper bound of the function $\delta^*$
(Definition 25).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 25. -/
public noncomputable def zeckendorfGenericExponent (Q Q' : ℕ → ℝ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ Real.logb (Q' 0) (Q 0) * Q' 0 ^ (p - 1) < Q 0 ^ p}

/-- **The generic exponent satisfies its defining inequality.** Let $Q$ and $\tilde Q$ be real
sequences with first terms $\omega$ and $\tilde\omega$, put $\gamma = \log_{\tilde\omega} \omega$,
and let $p$ be the generic exponent of $Q$ and $\tilde Q$. If some positive integer $q$ satisfies
$\gamma \tilde\omega^{q-1} < \omega^q$, then $p$ is positive and
$\gamma \tilde\omega^{p-1} < \omega^p$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 25. -/
public theorem zeckendorfGenericExponent_spec {Q Q' : ℕ → ℝ}
    (h : ∃ p : ℕ, 0 < p ∧ Real.logb (Q' 0) (Q 0) * Q' 0 ^ (p - 1) < Q 0 ^ p) :
    0 < zeckendorfGenericExponent Q Q' ∧
      Real.logb (Q' 0) (Q 0) * Q' 0 ^ (zeckendorfGenericExponent Q Q' - 1) <
        Q 0 ^ zeckendorfGenericExponent Q Q' :=
  Nat.sInf_mem h

/-- **The set $U$ of evaluations of $\tilde E^* \setminus \bar E^*$.** For lists $L$ and
$\tilde L$ and a real sequence $\tilde Q$, let $\tilde E^*$ be the $\tilde L^*$-collection and
$\bar E^*$ the closure collection of $L$. The set $U \subseteq \mathbb R$ is the image of
$\tilde E^* \setminus \bar E^*$ under the evaluation
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Notation 2. -/
public noncomputable def zeckendorfSmoothSet (L L' : List ℕ) (Q' : ℕ → ℝ) : Set ℝ :=
  zeckendorfRealEval Q' '' (lStarCollection L' \ lStarClosure L)

/-- **Membership in the set $U$.** Let $L$ and $\tilde L$ be lists of natural numbers and let
$\tilde Q = (\tilde Q_k)$ be a sequence of real numbers. Let $\tilde E^*$ be the collection $E^*$
determined by $\tilde L$, let $\bar E^*$ be the closure $\bar E^*$ determined by $L$, and let $U$
be the image of $\tilde E^* \setminus \bar E^*$ under the map
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$. A real number $x$ lies in $U$ if and only if
$x = \sum_k \varepsilon_k \tilde Q_k$ for some $\varepsilon \in \tilde E^*$ with
$\varepsilon \notin \bar E^*$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Notation 2. -/
public theorem mem_zeckendorfSmoothSet_iff {L L' : List ℕ} {Q' : ℕ → ℝ} {x : ℝ} :
    x ∈ zeckendorfSmoothSet L L' Q' ↔
      ∃ ε ∈ lStarCollection L', ε ∉ lStarClosure L ∧ zeckendorfRealEval Q' ε = x := by
  simp [zeckendorfSmoothSet, and_assoc]

/-- **Reversals characterize the nonzero elements of $\bar E^\ast$.** Let $L$ be a list of natural
numbers of length at least $2$ with nonzero first entry, let $E$ be the periodic Zeckendorf
collection determined by $L$, and let $\bar E^*$ be the closure of the collection $E^*$ determined
by $L$. For $n \in \mathbb N$ and a coefficient function $\varepsilon : \mathbb N \to \mathbb N$,
let $\mathrm{rev}_n(\varepsilon)$ be the finitely supported coefficient function whose first $n$
entries are the first $n$ entries of $\varepsilon$ in reverse order and whose other entries are
$0$. Then a nonzero coefficient function $\varepsilon : \mathbb N \to \mathbb N$ satisfies
$\mathrm{rev}_n(\varepsilon) \in E$ for every $n \in \mathbb N$ if and only if
$\varepsilon \in \bar E^*$.

This reads the source's Lemma 3 for nonzero $\varepsilon$ and counts $\bar\beta^1$, the maximal
$L^*$-block starting at the first index, as an element of $\bar E^*$. As printed (no
$\varepsilon \ne 0$, decompositions with at least one block) the lemma fails at
$\varepsilon = 0$, since $\mathrm{rev}_n(0) = 0 \in E$, and at $\varepsilon = \bar\beta^1$,
since $\mathrm{rev}_n(\bar\beta^1)$ is the maximal $L$-block $\theta^{n+1}$, which lies in $E$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 3 (`integers-2025-A25-lem-3`). -/
public theorem_wanted forall_zeckendorfRev_mem_iff_mem_lStarClosure (L : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} (hε : ε ≠ 0) :
    (∀ n, zeckendorfRev n ε ∈ periodicZeckendorfCollection L) ↔ ε ∈ lStarClosure L

/-- **Decomposition along $L^*$-blocks (Corollary 1).** Let $L$ and $\tilde L$ be a periodic
Zeckendorf pair, let $E^*$ and $\tilde E^*$ be the collections determined by $L$ and $\tilde L$,
and let $\varepsilon \in \tilde E^*$. Index coefficient functions from $1$. For $b \ge 0$, let
$\eta_b$ agree with $\varepsilon$ at the indices $\le b$ and vanish elsewhere, and let
$\mu_b = \varepsilon - \eta_b$. Call $b$ a decomposition index of $\varepsilon$ if $\eta_b$ is a
sum of disjoint proper $L^*$-blocks with support intervals inside $[1, b]$ and
$\bar\beta^{b+1} \le_d \mu_b$, where $\bar\beta^{b+1}$ is the maximal $L^*$-block starting at
index $b + 1$ and $\le_d$ means equal or smaller in the descending lexicographic order. Then
$\varepsilon \in E^*$ if and only if $\varepsilon$ has no decomposition index, and if
$\varepsilon \notin E^*$, then $\varepsilon$ has exactly one decomposition index.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 1 (`integers-2025-A25-cor-1`). -/
public theorem_wanted lStarBar_decomposition {L L' : List ℕ} (hp : IsPeriodicZeckendorfPair L L')
    {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    (ε ∈ lStarCollection L ↔ ¬ ∃ b I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
        (∀ p ∈ I, p.2 < b) ∧ (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
          DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i))) ∧
    (ε ∉ lStarCollection L → ∃! b, ∃ I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
        (∀ p ∈ I, p.2 < b) ∧ (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
          DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)))

open Classical in
/-- **Lemma 10: $\mathrm{rev}_n$ of the bar of $\mathrm{rev}_n(\varepsilon)$.** Let
$(L, \tilde L)$ be a periodic Zeckendorf pair, $E$ the periodic Zeckendorf collection of $L$, and
$E^*$ and $\tilde E^*$ the $L^*$- and $\tilde L^*$-collections. Indices start at $0$. Write $<_d$
for the descending lexicographic order, $\bar\beta^{s+1}$ for the maximal $L^*$-block starting at
index $s$, $\mathrm{rev}_n$ for the reversal of the first $n$ entries, $\bar\mu$ for the bar of a
finitely supported $\mu$ relative to $E$, and $\mathrm{res}_n(\varepsilon)$ for $\varepsilon$
with every entry at an index $\ge n$ replaced by $0$. Let $\varepsilon \in \tilde E^*$ with
$\varepsilon <_d \bar\beta^1$. If $\varepsilon \in E^*$, then
$\mathrm{rev}_n(\overline{\mathrm{rev}_n(\varepsilon)}) = \mathrm{res}_n(\varepsilon)$ for every
$n \ge 1$. Moreover, let $b \ge 1$ be such that $\mathrm{res}_b(\varepsilon)$ is a sum of
disjoint proper $L^*$-blocks whose support intervals consist of indices below $b$, and such that
the coefficient function $\mu$ obtained from $\varepsilon$ by replacing every entry at an index
below $b$ by $0$ satisfies $\mu = \bar\beta^{b+1}$ or $\bar\beta^{b+1} <_d \mu$. Then for all
sufficiently large $n$, $\mathrm{rev}_n(\overline{\mathrm{rev}_n(\varepsilon)})$ equals
$\mathrm{res}_b(\varepsilon) + \beta^b$ if $\bar\beta^{b+1} <_d \mu$, where $\beta^b$ has entry
$1$ at index $b - 1$ and $0$ elsewhere, and equals $\mathrm{res}_n(\varepsilon)$ otherwise.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 10 (`integers-2025-A25-lem-10`). -/
public theorem_wanted zeckendorfRev_bar_zeckendorfRev_eq {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hlt : DescLexLT ε (maxLStarBlock L 0)) :
    (ε ∈ lStarCollection L → ∀ n, 1 ≤ n →
      ⇑(zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε))) =
        fun i => if i < n then ε i else 0) ∧
    ∀ b I, 1 ≤ b → IsLStarBlockSum L I (fun i => if i < b then ε i else 0) →
      (∀ p ∈ I, p.2 < b) →
      (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
        DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)) →
      ∀ᶠ n in Filter.atTop,
        ⇑(zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε))) =
          if DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i) then
            (fun i => if i < b then ε i else 0) + ⇑(Finsupp.single (b - 1) 1)
          else fun i => if i < n then ε i else 0

/-- **Fixed points of $\overline{\mathrm{rev}}$ in $\tilde E^*$.** Let $L$ and $\tilde L$ be
lists of natural numbers of length at least $2$ with nonzero first entries, such that the
periodic Zeckendorf collection $E$ of $L$ is a proper subset of the periodic Zeckendorf
collection $\tilde E$ of $\tilde L$. Let $\tilde E^*$ be the collection $E^*$ determined by
$\tilde L$, and let $\bar E^*$ and $\overline{\mathrm{rev}}$ be taken with respect to $L$. Then
for every $\varepsilon \in \tilde E^*$, $\varepsilon \in \bar E^*$ if and only if
$\overline{\mathrm{rev}}(\varepsilon) = \varepsilon$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 11 (`integers-2025-A25-lem-11`). -/
public theorem_wanted mem_lStarClosure_iff_zeckendorfRevBar_eq {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    ε ∈ lStarClosure L ↔ zeckendorfRevBar L ε = ε

/-- **$\overline{\mathrm{rev}}$ of the reversal of an element of $\tilde E$ (Lemma 12).** Let $L$
and $\tilde L$ form a periodic Zeckendorf pair, let $E$ and $\tilde E$ be the periodic Zeckendorf
collections determined by $L$ and $\tilde L$, and index coefficient functions from $0$. Let
$\mu \in \tilde E$ and $t \ge 1$ be such that $\mu_{t-1} \ne 0$ and $\mu_j = 0$ for all $j \ge t$.
Let $\overline{\mathrm{rev}}$ be the map determined by $L$, $\bar\beta^1$ the maximal $L^*$-block
starting at index $0$, $\mathrm{rev}_t$ the reversal of the first $t$ entries, $\bar\mu$ the bar
of $\mu$ relative to $E$, $<_a$ the ascending lexicographic order, and $\theta^{t+1}$ the maximal
$L$-block that vanishes from index $t$ on. If $\mu = \theta^{t+1}$ or $\mu <_a \theta^{t+1}$,
then $\overline{\mathrm{rev}}(\mathrm{rev}_t(\mu)) = \mathrm{rev}_t(\bar\mu)$; if
$\theta^{t+1} <_a \mu$, then $\overline{\mathrm{rev}}(\mathrm{rev}_t(\mu)) = \bar\beta^1$.

In the paper $t$ is the order of $\mu$, and $\theta^{t+1}$ appears as the immediate predecessor
$\hat\beta^{t+1}$ in $E$ of the basis function $\beta^{t+1}$, whose only nonzero entry is a $1$
at index $t$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 12 (`integers-2025-A25-lem-12`). -/
public theorem_wanted zeckendorfRevBar_zeckendorfRev_of_order {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {μ : ℕ →₀ ℕ} (hμ : μ ∈ periodicZeckendorfCollection L')
    {t : ℕ} (ht : 1 ≤ t) (hord : μ (t - 1) ≠ 0 ∧ ∀ j, t ≤ j → μ j = 0) :
    ((μ = periodicTheta L t ∨ AscLexLT μ (periodicTheta L t)) →
      zeckendorfRevBar L (zeckendorfRev t μ) =
        ⇑(zeckendorfRev t (zeckendorfBar (periodicZeckendorfCollection L) μ))) ∧
    (AscLexLT (periodicTheta L t) μ → zeckendorfRevBar L (zeckendorfRev t μ) = maxLStarBlock L 0)

/-- **Transition from the subcollection count to $\delta^\ast$.** Let $L$ and $\tilde L$ form a
periodic Zeckendorf pair, with periodic Zeckendorf collections $E \subsetneq \tilde E$, and let
$Q$ and $\tilde Q$ be fundamental sequences of the $L^*$-collection $E^*$ and the
$\tilde L^*$-collection $\tilde E^*$. Put $\omega = Q_0$, $\tilde\omega = \tilde Q_0$ and
$\gamma = \log_{\tilde\omega} \omega$, and let $\delta^*$ be the function determined by $L$,
$\tilde L$, $Q$ and $\tilde Q$. Let $H$ and $\tilde H$ be strictly increasing sequences of
positive integers such that $\mu \mapsto \sum_k \mu_k H_k$ is a bijection from $E$ onto
$\mathbb N$ and $\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto
$\mathbb N$, and suppose $H_n \omega^n \to \alpha$ and
$\tilde H_n \tilde\omega^n \to \tilde\alpha$ as $n \to \infty$. For each natural number $x$ let
$\mu_x \in \tilde E$ satisfy $\sum_k (\mu_x)_k \tilde H_k = x$, let $n_x$ be one more than the
largest index in the support of $\mu_x$ ($n_x = 0$ if $\mu_x = 0$), and let $z(x)$ be the number
of natural numbers $n < x$ of the form $\sum_k \mu_k \tilde H_k$ with $\mu \in E$. Then, as
$x \to \infty$ through the natural numbers, $z(x) / x^\gamma$ is asymptotically equivalent to
$\delta^*(y_x) \, \alpha / \tilde\alpha^\gamma$, where $y_x = \sum_k \rho_k \tilde Q_k$ and
$\rho = \operatorname{rev}_{n_x}(\mu_x)$ lists the first $n_x$ entries of $\mu_x$ in reverse order.

Indices are zero-based.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 2 (`integers-2025-A25-prop-2`). -/
public theorem_wanted isEquivalent_subcollectionCount_div_rpow_deltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {H H' : ℕ → ℕ} (hmono : StrictMono H)
    (hpos : ∀ k, 0 < H k) (hbij : Set.BijOn (zeckendorfEval H) (periodicZeckendorfCollection L) Set.univ)
    (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) {α α' : ℝ}
    (hα : Filter.Tendsto (fun n => (H n : ℝ) * Q 0 ^ n) Filter.atTop (nhds α))
    (hα' : Filter.Tendsto (fun n => (H' n : ℝ) * Q' 0 ^ n) Filter.atTop (nhds α'))
    {μ : ℕ → ℕ →₀ ℕ}
    (hμ : ∀ x, μ x ∈ periodicZeckendorfCollection L' ∧ zeckendorfEval H' (μ x) = x) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℕ => (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) /
        (x : ℝ) ^ Real.logb (Q' 0) (Q 0))
      (fun x : ℕ => zeckendorfDeltaStar L L' Q Q'
          (zeckendorfRealEval Q' (zeckendorfRev ((μ x).support.sup (· + 1)) (μ x))) *
        (α / α' ^ Real.logb (Q' 0) (Q 0)))

/-- **Lemma 13: behaviour of $\overline{\mathrm{rev}}$ near a point.** Let $(L, \tilde L)$ be a
periodic Zeckendorf pair, let $E^*$ and $\tilde E^*$ be the $L^*$- and $\tilde L^*$-collections,
$\bar E^*$ the closure collection of $L$, $\overline{\mathrm{rev}}$ the map determined by $L$,
$\inf$ the $L^*$-infimum map, and $\tilde Q$ a fundamental sequence of $\tilde E^*$. For
$\eta \in \tilde E^*$ write $x(\eta) = \sum_k \eta_k \tilde Q_k$, and let
$\varepsilon \in \tilde E^*$. If $\varepsilon \notin \bar E^*$, there is $\delta > 0$ such that
$\overline{\mathrm{rev}}(\varepsilon') = \overline{\mathrm{rev}}(\varepsilon)$ for every
$\varepsilon' \in \tilde E^*$ with $|x(\varepsilon') - x(\varepsilon)| < \delta$. If
$\varepsilon \in \bar E^* \setminus E^*$, there is $\delta > 0$ such that
$\inf(\overline{\mathrm{rev}}(\varepsilon')) = \overline{\mathrm{rev}}(\varepsilon)$ for every
$\varepsilon' \in \tilde E^*$ with $x(\varepsilon) < x(\varepsilon') < x(\varepsilon) + \delta$,
and for every $n$ there is $\delta > 0$ such that $\overline{\mathrm{rev}}(\varepsilon')$ and
$\overline{\mathrm{rev}}(\varepsilon)$ agree at all indices $i < n$ for every
$\varepsilon' \in \tilde E^*$ with $x(\varepsilon) - \delta < x(\varepsilon') < x(\varepsilon)$.
If $\varepsilon \in E^*$, then for every $n$ there is $\delta > 0$ such that
$\overline{\mathrm{rev}}(\varepsilon')$ and $\overline{\mathrm{rev}}(\varepsilon)$ agree at all
indices $i < n$ for every $\varepsilon' \in \tilde E^*$ with
$|x(\varepsilon') - x(\varepsilon)| < \delta$. Indices start at $0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 13 (`integers-2025-A25-lem-13`). -/
public theorem_wanted zeckendorfRevBar_eventually_near {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q')
    {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    (ε ∉ lStarClosure L → ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
      |zeckendorfRealEval Q' ε' - zeckendorfRealEval Q' ε| < δ →
        zeckendorfRevBar L ε' = zeckendorfRevBar L ε) ∧
    (ε ∈ lStarClosure L → ε ∉ lStarCollection L →
      (∃ δ > 0, ∀ ε' ∈ lStarCollection L', zeckendorfRealEval Q' ε < zeckendorfRealEval Q' ε' →
        zeckendorfRealEval Q' ε' < zeckendorfRealEval Q' ε + δ →
          lStarInf L (zeckendorfRevBar L ε') = zeckendorfRevBar L ε) ∧
      ∀ n, ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
        zeckendorfRealEval Q' ε - δ < zeckendorfRealEval Q' ε' →
          zeckendorfRealEval Q' ε' < zeckendorfRealEval Q' ε →
            ∀ i < n, zeckendorfRevBar L ε' i = zeckendorfRevBar L ε i) ∧
    (ε ∈ lStarCollection L → ∀ n, ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
      |zeckendorfRealEval Q' ε' - zeckendorfRealEval Q' ε| < δ →
        ∀ i < n, zeckendorfRevBar L ε' i = zeckendorfRevBar L ε i)

/-- **Infinitely many unit reductions stay in the $L^\ast$-closure.** Let
$L = (e_1, \dots, e_N)$ be a list of natural numbers with $N \ge 2$ and $e_1 \ne 0$, and let
$E^* \subseteq \bar E^*$ be the $L^*$-collection and the $L^*$-closure determined by $L$. Let
$\varepsilon \in \bar E^*$, and suppose it is not the case that $\varepsilon \in E^*$ and
$\varepsilon$ has finite support. Then there are infinitely many indices $r$ such that
$\varepsilon_r \ge 1$ and the coefficient function obtained from $\varepsilon$ by lowering its
entry at $r$ by one lies in $\bar E^*$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 14 (`integers-2025-A25-lem-14`). -/
public theorem_wanted infinite_setOf_sub_single_mem_lStarClosure (L : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L)
    (hfin : ¬ (ε ∈ lStarCollection L ∧ ∃ M, ∀ i, M < i → ε i = 0)) :
    {r | 1 ≤ ε r ∧ Function.update ε r (ε r - 1) ∈ lStarClosure L}.Infinite

/-- **Proposition 3: $U$ is a disjoint union of open intervals.** Let $(L, \tilde L)$ be a
periodic Zeckendorf pair, $E^*$ and $\tilde E^*$ the $L^*$- and $\tilde L^*$-collections,
$\bar E^*$ the closure collection of $L$, and $\tilde Q$ a fundamental sequence of $\tilde E^*$.
Write $x(\eta) = \sum_k \eta_k \tilde Q_k$, $\tilde\omega = \tilde Q_0$, and $\bar\beta^{b+1}$
for the maximal $L^*$-block starting at index $b$ (indices start at $0$), and let
$U = \{x(\varepsilon) : \varepsilon \in \tilde E^* \setminus \bar E^*\}$. Call a pair
$(b, \eta)$ with $b \in \mathbb N$ and $\eta : \mathbb N \to \mathbb N$ admissible if $\eta$ is a
sum of disjoint proper $L^*$-blocks whose support intervals consist of indices below $b$ and
$\eta + \bar\beta^{b+1} \notin E^*$. Then $U$ is the union, over all admissible pairs
$(b, \eta)$, of the open intervals $(x(\eta + \bar\beta^{b+1}), x(\eta) + \tilde\omega^b)$; the
intervals of two distinct admissible pairs are disjoint; and $U$ is open and measurable.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 3 (`integers-2025-A25-prop-3`). -/
public theorem_wanted zeckendorfSmoothSet_eq_iUnion {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q') :
    zeckendorfSmoothSet L L' Q' =
      (⋃ (b : ℕ) (η : ℕ → ℕ) (_ : (∃ I, IsLStarBlockSum L I η ∧ ∀ p ∈ I, p.2 < b) ∧
          η + maxLStarBlock L b ∉ lStarCollection L),
        Set.Ioo (zeckendorfRealEval Q' (η + maxLStarBlock L b))
          (zeckendorfRealEval Q' η + Q' 0 ^ b)) ∧
    (∀ b η b' η', (∃ I, IsLStarBlockSum L I η ∧ ∀ p ∈ I, p.2 < b) →
      η + maxLStarBlock L b ∉ lStarCollection L →
      (∃ I, IsLStarBlockSum L I η' ∧ ∀ p ∈ I, p.2 < b') →
      η' + maxLStarBlock L b' ∉ lStarCollection L → (b, η) ≠ (b', η') →
      Disjoint (Set.Ioo (zeckendorfRealEval Q' (η + maxLStarBlock L b))
          (zeckendorfRealEval Q' η + Q' 0 ^ b))
        (Set.Ioo (zeckendorfRealEval Q' (η' + maxLStarBlock L b'))
          (zeckendorfRealEval Q' η' + Q' 0 ^ b'))) ∧
    IsOpen (zeckendorfSmoothSet L L' Q') ∧ MeasurableSet (zeckendorfSmoothSet L L' Q')

/-- **Continuity and local monotonicity of $\delta^{\ast}$.** Let $L$ and $\tilde L$ form a
periodic Zeckendorf pair, let $Q$ be a fundamental sequence of the collection $E^*$ determined by
$L$, and let $\tilde Q$ be a fundamental sequence of the collection $\tilde E^*$ determined by
$\tilde L$. Then the function $\delta^*$ built from $L, \tilde L, Q, \tilde Q$ is continuous on
$(0, 1)$, and at each point $x$ of the smooth set $U$ of $L, \tilde L, \tilde Q$ it is
differentiable and strictly decreasing on some neighbourhood of $x$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 9 (`integers-2025-A25-thm-9`). -/
public theorem_wanted continuousOn_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    ContinuousOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) ∧
      ∀ x ∈ zeckendorfSmoothSet L L' Q', DifferentiableAt ℝ (zeckendorfDeltaStar L L' Q Q') x ∧
        ∃ s ∈ nhds x, StrictAntiOn (zeckendorfDeltaStar L L' Q Q') s

/-- **$\delta^*$ is not differentiable at the evaluations of $\bar E^*$.** Let $L$ and $\tilde L$
be lists of natural numbers of length at least $2$ with nonzero first entries whose periodic
Zeckendorf collections $E$ and $\tilde E$ satisfy $E \subsetneq \tilde E$. Let $Q$ be a fundamental
sequence of the collection $E^*$ determined by $L$, let $\tilde Q$ be a fundamental sequence of the
collection $\tilde E^*$ determined by $\tilde L$, and let $\delta^*$ be the function determined by
$L$, $\tilde L$, $Q$ and $\tilde Q$. For every $\varepsilon$ in the closure $\bar E^*$ determined
by $L$, $\delta^*$ is not differentiable at $\sum_k \varepsilon_k \tilde Q_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 10 (`integers-2025-A25-thm-10`). -/
public theorem_wanted not_differentiableAt_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L) :
    ¬ DifferentiableAt ℝ (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- **The smooth set $U$ has Lebesgue measure $1$.** Let $L$ and $\tilde L$ form a periodic
Zeckendorf pair, let $\tilde E^*$ be the collection $E^*$ determined by $\tilde L$, let $\tilde Q$
be a fundamental sequence of $\tilde E^*$, and let $\bar E^*$ be the closure determined by $L$.
Let $U$ be the image of $\tilde E^* \setminus \bar E^*$ under the evaluation
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$. Then $U$ has Lebesgue measure $1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 11 (`integers-2025-A25-thm-11`). -/
public theorem_wanted volume_zeckendorfSmoothSet {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q') :
    MeasureTheory.volume (zeckendorfSmoothSet L L' Q') = 1

/-- **Local minima of $\delta^\ast$ at finitely supported points.** Let $L$ and $\tilde L$ form a
periodic Zeckendorf pair, let $Q$ and $\tilde Q$ be fundamental sequences of the $L^*$-collection
$E^*$ and the $\tilde L^*$-collection $\tilde E^*$, and let $\delta^*$ be the function determined
by $L$, $\tilde L$, $Q$ and $\tilde Q$. If $\varepsilon \in E^*$ has finite support, then
$\delta^*$ has a local minimum at $\sum_k \varepsilon_k \tilde Q_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 6 (`integers-2025-A25-prop-6`). -/
public theorem_wanted isLocalMin_zeckendorfDeltaStar_of_finite {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L)
    (hfin : ∃ M, ∀ i, M < i → ε i = 0) :
    IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- **$\delta^*$ has no local extremum at infinite expansions in $E^*$.** Let $L$ and $\tilde L$ be
lists of natural numbers of length at least $2$ with nonzero first entries whose periodic
Zeckendorf collections satisfy $E \subsetneq \tilde E$. Let $Q$ be a fundamental sequence of the
collection $E^*$ determined by $L$, let $\tilde Q$ be a fundamental sequence of the collection
$\tilde E^*$ determined by $\tilde L$, and let $\delta^*$ be the function determined by $L$,
$\tilde L$, $Q$ and $\tilde Q$. If $\varepsilon \in E^*$ has infinitely many nonzero entries, then
$\delta^*$ has neither a local minimum nor a local maximum at $\sum_k \varepsilon_k \tilde Q_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 7 (`integers-2025-A25-prop-7`). -/
public theorem_wanted not_isLocalExtr_zeckendorfDeltaStar_of_infinite {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L)
    (hinf : ∀ M, ∃ i, M < i ∧ ε i ≠ 0) :
    ¬ IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε) ∧
      ¬ IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- **Strict local maxima of $\delta^{\ast}$ at the closure points.** Let $L$ and $\tilde L$ form a
periodic Zeckendorf pair, let $Q$ be a fundamental sequence of the collection $E^*$ determined by
$L$, and let $\tilde Q$ be a fundamental sequence of the collection $\tilde E^*$ determined by
$\tilde L$. Let $\varepsilon \in \bar E^* \setminus E^*$, where $\bar E^*$ is the closure
collection of $L$, and put $x = \sum_k \varepsilon_k \tilde Q_k$. Then, for the function
$\delta^*$ built from $L, \tilde L, Q, \tilde Q$, we have $\delta^*(y) < \delta^*(x)$ for all
$y \ne x$ sufficiently close to $x$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 8 (`integers-2025-A25-prop-8`). -/
public theorem_wanted eventually_zeckendorfDeltaStar_lt_of_mem_lStarClosure {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L)
    (hε' : ε ∉ lStarCollection L) :
    ∀ᶠ y in nhdsWithin (zeckendorfRealEval Q' ε) {zeckendorfRealEval Q' ε}ᶜ,
      zeckendorfDeltaStar L L' Q Q' y < zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε)

/-- **Classification of the local extrema of $\delta^\ast$.** Let $L$ and $\tilde L$ form a
periodic Zeckendorf pair, let $Q$ and $\tilde Q$ be fundamental sequences of the $L^*$-collection
$E^*$ and the $\tilde L^*$-collection $\tilde E^*$, let $\bar E^*$ be the $L^*$-closure, and let
$\delta^*$ be the function determined by $L$, $\tilde L$, $Q$ and $\tilde Q$. For a coefficient
function $\varepsilon$ write $x_\varepsilon = \sum_k \varepsilon_k \tilde Q_k$. Then (i) for every
$\varepsilon \in \tilde E^*$ such that either $\varepsilon \notin \bar E^*$, or
$\varepsilon \in E^*$ and $\varepsilon$ has infinite support, $\delta^*$ has neither a local
minimum nor a local maximum at $x_\varepsilon$; (ii) for every $\varepsilon \in E^*$ with finite
support, $\delta^*$ has a local minimum at $x_\varepsilon$; and (iii) for every
$\varepsilon \in \bar E^* \setminus E^*$, $\delta^*$ has a local maximum at $x_\varepsilon$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 12 (`integers-2025-A25-thm-12`). -/
public theorem_wanted isLocalExtr_zeckendorfDeltaStar_classification {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ ε ∈ lStarCollection L', (ε ∉ lStarClosure L ∨
        (ε ∈ lStarCollection L ∧ ∀ M, ∃ i, M < i ∧ ε i ≠ 0)) →
      ¬ IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε) ∧
        ¬ IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)) ∧
    (∀ ε ∈ lStarCollection L, (∃ M, ∀ i, M < i → ε i = 0) →
      IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)) ∧
    ∀ ε ∈ lStarClosure L, ε ∉ lStarCollection L →
      IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- **Generic upper bound for $\delta^*$ (Lemma 17).** Let $L$ and $\tilde L$ be lists of length at
least $2$ with nonzero first entries whose periodic Zeckendorf collections satisfy
$E \subsetneq \tilde E$, and let $Q$ and $\tilde Q$ be fundamental sequences of the collections
$E^*$ and $\tilde E^*$ of $L$ and $\tilde L$. Write $\omega$ and $\tilde\omega$ for the first terms
of $Q$ and $\tilde Q$, $\gamma = \log_{\tilde\omega} \omega$, $p$ for the generic exponent of $Q$
and $\tilde Q$, $\delta^*$ for the function $\delta^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$,
$\overline{\mathrm{rev}}$ for the reversal map of $L$ (Definition 23), $\varepsilon_k$ for the
$k$th entry of a coefficient function $\varepsilon$ ($k \ge 1$), and
$\sum \varepsilon Q = \sum_{k \ge 1} \varepsilon_k Q_k$ (so that $Q_1 = \omega$). Then
$\delta^*(\sum \varepsilon \tilde Q) < (\omega / \tilde\omega)^p / \gamma$ for every
$\varepsilon \in \tilde E^*$, and every $\varepsilon \in \tilde E^*$ with
$\sum \varepsilon \tilde Q \ge \tilde\omega$ satisfies
$\delta^*(\sum \varepsilon \tilde Q) <
\sum \overline{\mathrm{rev}}(\varepsilon) Q / \sum \varepsilon \tilde Q <
(\omega / \tilde\omega)^p / \gamma$.

Without $\sum \varepsilon \tilde Q \ge \tilde\omega$ (the normalization $\varepsilon_1 \ge 1$ that
the proof of Lemma 17 assumes) the middle bound fails: for $L = (1, 0)$, $\tilde L = (1, 1)$ (so
$p = 2$) and $\varepsilon = \beta^4$ (a single $1$ in the fourth entry),
$\overline{\mathrm{rev}}(\varepsilon) = \varepsilon$ and the middle quotient is
$16 \omega^4 = 2.33436\ldots$, while $(\omega / \tilde\omega)^2 / \gamma = 2.20076\ldots$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 17 (`integers-2025-A25-lem-17`). -/
public theorem_wanted zeckendorfDeltaStar_lt_genericBound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ ε ∈ lStarCollection L', zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) <
      (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' / Real.logb (Q' 0) (Q 0)) ∧
    ∀ ε ∈ lStarCollection L', Q' 0 ≤ zeckendorfRealEval Q' ε →
      zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) <
          zeckendorfRealEval Q (zeckendorfRevBar L ε) / zeckendorfRealEval Q' ε ∧
        zeckendorfRealEval Q (zeckendorfRevBar L ε) / zeckendorfRealEval Q' ε <
          (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' / Real.logb (Q' 0) (Q 0)

/-- **Monotonicity of the ratio under steep increments.** Let $L$ and $\tilde L$ form a periodic
Zeckendorf pair, let $Q$ be a fundamental sequence of the collection $E^*$ determined by $L$, and
let $\tilde Q$ be a fundamental sequence of the collection $\tilde E^*$ determined by $\tilde L$.
Put $\omega = Q_0$, $\tilde\omega = \tilde Q_0$ and $\gamma = \log_{\tilde\omega} \omega$, and let
$p$ be the generic exponent of $Q, \tilde Q$. Let $\varepsilon \in \tilde E^*$ with
$x = \sum_k \varepsilon_k \tilde Q_k \ge \tilde\omega$, and put
$y = \sum_k \overline{\mathrm{rev}}(\varepsilon)_k Q_k$, with $\overline{\mathrm{rev}}$ taken
with respect to $L$. If $\Delta x > 0$, $\Delta y > 0$ and
$(\omega / \tilde\omega)^p \le \Delta y / \Delta x$, then
$y / x^\gamma < (y + \Delta y) / (x + \Delta x)^\gamma$.

The hypothesis $x \ge \tilde\omega$ follows the reading of Lemma 17. As printed (for all
$\varepsilon \in \tilde E^*$) the lemma fails for $L = (1, 0)$, $\tilde L = (1, 1)$, $\varepsilon$
the coefficient function with a single $1$ at index $3$ ($x = 1/16$, $y = \omega^4$,
$y / x^\gamma = 1$), $\Delta x = 10^{-8}$ and $\Delta y = (\omega / \tilde\omega)^2 \Delta x$: the
right side is $0.99999999364\ldots$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 18 (`integers-2025-A25-lem-18`). -/
public theorem_wanted div_rpow_lt_add_div_add_rpow_of_genericBound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hx : Q' 0 ≤ zeckendorfRealEval Q' ε) {Δx Δy : ℝ} (hΔx : 0 < Δx) (hΔy : 0 < Δy)
    (hΔ : (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' ≤ Δy / Δx) :
    zeckendorfRealEval Q (zeckendorfRevBar L ε) /
        zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) <
      (zeckendorfRealEval Q (zeckendorfRevBar L ε) + Δy) /
        (zeckendorfRealEval Q' ε + Δx) ^ Real.logb (Q' 0) (Q 0)

/-- **Monotonicity of the ratio under fundamental increments (Corollary 3).** Let $L$ and
$\tilde L$ form a periodic Zeckendorf pair, let $Q$ be a fundamental sequence of the collection
$E^*$ determined by $L$, and let $\tilde Q$ be a fundamental sequence of the collection
$\tilde E^*$ determined by $\tilde L$; indices start at $0$. Put $\omega = Q_0$,
$\tilde\omega = \tilde Q_0$ and $\gamma = \log_{\tilde\omega} \omega$, let $p$ be the generic
exponent of $Q$ and $\tilde Q$, let $\delta^*$ be the function $\delta^*$ of $L$, $\tilde L$, $Q$,
$\tilde Q$, and let $\overline{\mathrm{rev}}$ be the map determined by $L$. Let
$\varepsilon \in \tilde E^*$ with $x = \sum_k \varepsilon_k \tilde Q_k \ge \tilde\omega$, put
$y = \sum_k \overline{\mathrm{rev}}(\varepsilon)_k Q_k$, and let $m$ be a natural number with
$p \le m + 1$. Then $\delta^*(x) = y / x^\gamma$ and
$y / x^\gamma < (y + Q_m) / (x + \tilde Q_m)^\gamma$.

The hypothesis $x \ge \tilde\omega$ follows the reading of Lemma 17; in the paper's one-based
indexing $Q_m$ is $Q_n$ with $n = m + 1 \ge p$. As printed (for all $\varepsilon \in \tilde E^*$)
the corollary fails for $L = (1, 0)$, $\tilde L = (1, 1)$, $n = p = 2$ and
$\varepsilon = \beta^{11} + \beta^{13}$ (single ones in the paper's entries $11$ and $13$), for
which $\overline{\mathrm{rev}}(\varepsilon) = \varepsilon$: the left side $1.18363\ldots$ exceeds
the right side $1.01645\ldots$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 3 (`integers-2025-A25-cor-3`). -/
public theorem_wanted zeckendorfDeltaStar_lt_add_fundamental {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hx : Q' 0 ≤ zeckendorfRealEval Q' ε) {m : ℕ} (hm : zeckendorfGenericExponent Q Q' ≤ m + 1) :
    zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) =
        zeckendorfRealEval Q (zeckendorfRevBar L ε) /
          zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) ∧
      zeckendorfRealEval Q (zeckendorfRevBar L ε) /
          zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) <
        (zeckendorfRealEval Q (zeckendorfRevBar L ε) + Q m) /
          (zeckendorfRealEval Q' ε + Q' m) ^ Real.logb (Q' 0) (Q 0)

/-- **Where $\delta^\ast$ can attain its maximum.** Let $L$ and $\tilde L$ be lists of natural
numbers forming a periodic Zeckendorf pair, let $N$ be the length of $L$, let $E^*$ and
$\tilde E^*$ be the collections determined by $L$ and $\tilde L$, let $\bar E^*$ be the closure
of $E^*$, and let $Q$ and $\tilde Q$ be fundamental sequences of $E^*$ and $\tilde E^*$. Let
$\delta^*$ be the function $\delta^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$, and let $p$ be the
generic exponent of $Q$ and $\tilde Q$. Indices start at $0$: put $\omega = Q_0$ and
$\tilde\omega = \tilde Q_0$, write $\sum \varepsilon \tilde Q = \sum_k \varepsilon_k \tilde Q_k$
for a coefficient function $\varepsilon : \mathbb N \to \mathbb N$, and for $s \in \mathbb N$ let
$\bar\beta_s$ be the maximal $L^*$-block starting at index $s$. First, if $y \in (0, 1)$ and
$\delta^*(x) \le \delta^*(y)$ for all $x \in (0, 1)$, then $y = \sum \varepsilon \tilde Q$ for
some $\varepsilon \in \bar E^*$ with $\varepsilon \notin E^*$. Second, let $\ell \ge 1$ be a
natural number and let $\eta : \mathbb N \to \mathbb N$ be a sum of disjoint proper $L^*$-blocks
(possibly none) whose support intervals $[s, k]$ all satisfy $k < \ell - 1$. If
$\delta^*(x) \le \delta^*\bigl(\sum (\eta + \bar\beta_{\ell - 1}) \tilde Q\bigr)$ for all
$x \in (0, 1)$, then
$$
\ell < \max\left(2,\ p + 1 +
\frac{N \ln(1 / \omega) + \ln\left(1 - \sum \bar\beta_0 \tilde Q + \tilde\omega^N\right)}
{\ln(1 / \tilde\omega) - \ln(1 / \omega)}\right).
$$

In the source's one-based indexing $\bar\beta_s$ is $\bar\beta^{s+1}$, so the blocks
$\zeta^m$ of $\eta$ lie inside $[1, \ell - 1]$, the point is
$\sum (\sum_m \zeta^m + \bar\beta^\ell) \tilde Q$, and with $\varphi = 1 / \omega$,
$\tilde\varphi = 1 / \tilde\omega$ and $\rho = \sum \bar\beta^1 \tilde Q$ the right side is the
source's $\max\{2, p^*\}$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 13 (`integers-2025-A25-thm-13`). -/
public theorem_wanted isMaxOn_zeckendorfDeltaStar_bound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ y ∈ Set.Ioo (0 : ℝ) 1, IsMaxOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) y →
      ∃ ε ∈ lStarClosure L, ε ∉ lStarCollection L ∧ zeckendorfRealEval Q' ε = y) ∧
    ∀ (ℓ : ℕ) (η : ℕ → ℕ) (I : Set (ℕ × ℕ)), 1 ≤ ℓ → IsLStarBlockSum L I η →
      (∀ p ∈ I, p.2 < ℓ - 1) →
      IsMaxOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1)
        (zeckendorfRealEval Q' (η + maxLStarBlock L (ℓ - 1))) →
      (ℓ : ℝ) < max 2 (zeckendorfGenericExponent Q Q' + 1 +
        (L.length * Real.log (Q 0)⁻¹ +
          Real.log (1 - zeckendorfRealEval Q' (maxLStarBlock L 0) + Q' 0 ^ L.length)) /
        (Real.log (Q' 0)⁻¹ - Real.log (Q 0)⁻¹))

/-- **Where $\delta^*$ attains its minimum.** Let $L$ and $\tilde L$ be lists of natural numbers
of length at least $2$ with nonzero first entries whose periodic Zeckendorf collections satisfy
$E \subsetneq \tilde E$. Let $Q$ and $\tilde Q$ be fundamental sequences of the $L^*$-collections
$E^*$ of $L$ and $\tilde E^*$ of $\tilde L$, let $\delta^*$ be the function on $(0, 1)$ built from
$L$, $\tilde L$, $Q$ and $\tilde Q$, and let $p$ be the generic exponent of $Q$ and $\tilde Q$.
Indices start at $0$. Then there is $\varepsilon \in E^*$ with $\varepsilon_i = 0$ for every
$i \ge \max(2, p) - 1$ such that $\delta^*(\sum_k \varepsilon_k \tilde Q_k) \le \delta^*(y)$ for
all $y \in (0, 1)$. Moreover, if $p \le 2$, then $\delta^*(\tilde Q_0) \le \delta^*(y)$ for all
$y \in (0, 1)$ and $\delta^*(\tilde Q_0) = 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 14 (`integers-2025-A25-thm-14`). -/
public theorem_wanted exists_isMinOn_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∃ ε ∈ lStarCollection L, (∀ i, max 2 (zeckendorfGenericExponent Q Q') - 1 ≤ i → ε i = 0) ∧
      IsMinOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) (zeckendorfRealEval Q' ε)) ∧
    (zeckendorfGenericExponent Q Q' ≤ 2 →
      IsMinOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) (Q' 0) ∧
        zeckendorfDeltaStar L L' Q Q' (Q' 0) = 1)

/-- **Shifting a unit one entry down increases $\delta^*$ (Lemma 19).** Let $N \ge 3$, let
$L = (1, \dots, 1, 0)$ ($N - 1$ ones followed by $0$, the $N$th order Zeckendorf collection) and
$\tilde L = (N - 1, \dots, N - 1)$ ($N$ entries, the base-$N$ collection), and let $Q$ and
$\tilde Q$ be fundamental sequences of the collections $E^*$ and $\tilde E^*$ of $L$ and
$\tilde L$. Write $\varepsilon_k$ for the $k$th entry of a coefficient function ($k \ge 1$),
$\beta^k$ for the coefficient function with a single $1$ in entry $k$,
$\sum \varepsilon \tilde Q = \sum_k \varepsilon_k \tilde Q_k$, $\delta^*$ for the function
$\delta^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$, and $p$ for the generic exponent of $Q$ and
$\tilde Q$. Then $p = 1$ if $N \ge 4$. Moreover, let $\varepsilon \in E^*$ with
$\varepsilon_1 \ge 1$ and let $n \ge 3$ with $\varepsilon_n = 1$. If some decomposition of
$\varepsilon$ as a sum of disjoint proper $L^*$-blocks has a block whose support interval ends at
entry $n - 1$, then $\varepsilon' = \varepsilon + \beta^{n-1} - \beta^n$ lies in $E^*$ and
$\delta^*(\sum \varepsilon \tilde Q) < \delta^*(\sum \varepsilon' \tilde Q)$.

As printed, $p = 1$ fails for $N = 3$: with $\omega$ and $\tilde\omega$ the first terms of $Q$ and
$\tilde Q$ and $\gamma = \log_{\tilde\omega} \omega$, $\gamma = 0.55467\ldots$ exceeds
$\omega = 0.54368\ldots$, so $p = 2$. The inequality
$\delta^*(\sum \varepsilon \tilde Q) < \delta^*(\sum \varepsilon' \tilde Q)$ fails without
$\varepsilon_1 \ge 1$ (the normalization used where the paper applies it): $\varepsilon = \beta^4$
and $\varepsilon' = \beta^3$ give the value $1$ on both sides.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 19 (`integers-2025-A25-lem-19`). -/
public theorem_wanted zeckendorfDeltaStar_lt_shift_baseN {N : ℕ} (hN : 3 ≤ N) {Q Q' : ℕ → ℝ}
    (hQ : IsLStarFundamentalSequence (List.replicate (N - 1) 1 ++ [0]) Q)
    (hQ' : IsLStarFundamentalSequence (List.replicate N (N - 1)) Q') :
    (4 ≤ N → zeckendorfGenericExponent Q Q' = 1) ∧
    ∀ ε ∈ lStarCollection (List.replicate (N - 1) 1 ++ [0]), 1 ≤ ε 0 →
      ∀ (n i : ℕ) (I : Set (ℕ × ℕ)), 3 ≤ n → ε (n - 1) = 1 →
        IsLStarBlockSum (List.replicate (N - 1) 1 ++ [0]) I ε → (i, n - 2) ∈ I →
        ε + Pi.single (n - 2) 1 - Pi.single (n - 1) 1 ∈
            lStarCollection (List.replicate (N - 1) 1 ++ [0]) ∧
          zeckendorfDeltaStar (List.replicate (N - 1) 1 ++ [0]) (List.replicate N (N - 1)) Q Q'
              (zeckendorfRealEval Q' ε) <
            zeckendorfDeltaStar (List.replicate (N - 1) 1 ++ [0]) (List.replicate N (N - 1)) Q Q'
              (zeckendorfRealEval Q' (ε + Pi.single (n - 2) 1 - Pi.single (n - 1) 1))

end

end MetaMathlibExt
