/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Int.Interval
public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

/-!
# Subset and subsequence sums with bounded numbers of terms (statements)

Statement-only targets from Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers
of Terms*, INTEGERS 24 (2024), Article A116.

* `boundedSubsetSums α β A` is `Σ^β_α(A)`, the sums of subsets `B ⊆ A` with
  `α ≤ |B| ≤ |A| - β`.
* `generalizedHFoldSumset a r h` is `h^{(r̄)}A` for the ordered set `A = {a₀, …, a_{k-1}}`.
* `yangChenBound r h` is `L(r̄, h)` (Section 1.1).
* A sequence `𝒜 = (A, t̄)` is the multiset `repetitionSequence a t` in which `a i` occurs `t i`
  times, and `boundedSubsequenceSums α β S` is `Σ^β_α(𝒜)`.

Ordered sets `a₀ < a₁ < ⋯` are strictly increasing maps out of `Fin k`; the set `A₀ = A ∪ {0}`
of the paper is `Fin.cons 0 b` (zero first) or `Fin.append c (Fin.cons 0 d)` (negative terms `c`,
zero, positive terms `d`).
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **Generalized $h$-fold sumset.** For elements $a_0, \dots, a_{k-1}$ of an additive commutative
monoid $G$ (not necessarily distinct), natural numbers $\bar r = (r_0, \dots, r_{k-1})$ and a
natural number $h$, the generalized $h$-fold sumset of $A = (a_0, \dots, a_{k-1})$ is the finite
set $h^{(\bar r)}A = \{\sum_j s_j a_j : s_j \in \mathbb{N}, s_j \le r_j, \sum_j s_j = h\}$, where
$s_j a_j$ is the sum of $s_j$ copies of $a_j$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `h^{(r̄)}A`). -/
def generalizedHFoldSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] {k : ℕ}
    (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) : Finset G :=
  ((Fintype.piFinset fun i => Finset.range (r i + 1)).filter fun s => ∑ i, s i = h).image
    fun s => ∑ i, s i • a i

/-- **The Yang–Chen bound.** Let $k, h \in \mathbb{N}$ and $\bar r = (r_0, \dots, r_{k-1})$ with
all $r_j \in \mathbb{N}$; all sums below run over indices $j \in \{0, \dots, k-1\}$. Let $\mu$ be
the largest $m \in \{0, \dots, k\}$ with $\sum_{j < m} r_j \le h$, let $\eta$ be the integer such
that $\eta + 1$ is the least $m \in \{0, \dots, k\}$ with $\sum_{j \ge m} r_j \le h$ (so
$\eta = -1$ when $h \ge \sum_j r_j$), and set $\delta = h - \sum_{j < \mu} r_j$ and
$\theta = h - \sum_{j > \eta} r_j$. The Yang–Chen bound is the integer
$$L(\bar r, h) = \sum_{j > \eta} j r_j - \sum_{j < \mu} j r_j + \theta \eta - \delta \mu + 1.$$

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definitions of `μ`, `η`, `δ`, `θ` and `L(r̄, h)`). -/
def yangChenBound {k : ℕ} (r : Fin k → ℕ) (h : ℕ) : ℤ :=
  let pre : ℕ → ℕ := fun m => ∑ j : Fin k with j.val < m, r j
  let suf : ℕ → ℕ := fun m => ∑ j : Fin k with m ≤ j.val, r j
  let μ : ℕ := Nat.findGreatest (fun m => pre m ≤ h) k
  let m₀ : ℕ := k - Nat.findGreatest (fun n => suf (k - n) ≤ h) k
  let η : ℤ := (m₀ : ℤ) - 1
  let δ : ℤ := (h : ℤ) - pre μ
  let θ : ℤ := (h : ℤ) - suf m₀
  ((∑ j : Fin k with m₀ ≤ j.val, (j.val : ℤ) * r j) - ∑ j : Fin k with j.val < μ, (j.val : ℤ) * r j)
    + θ * η - δ * μ + 1

/-- **Yang–Chen bound at $(1, 1, 1)$ and $h = 2$.** The Yang–Chen bound $L(\bar r, h)$ for
$\bar r = (1, 1, 1)$ and $h = 2$ equals $3$.

Here $\mu = 2$, $\eta = 0$ and $\delta = \theta = 0$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definition of `L(r̄, h)`). -/
theorem yangChenBound_one_one_one_two : yangChenBound (fun _ : Fin 3 => 1) 2 = 3 := by
  decide

/-- **Yang–Chen bound at $(1, 1, 2)$ and $h = 2$.** The Yang–Chen bound $L(\bar r, h)$ for
$\bar r = (1, 1, 2)$ and $h = 2$ equals $4$.

Here $\mu = 2$, $\eta = 1$ and $\delta = \theta = 0$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1.1 (definition of `L(r̄, h)`). -/
theorem yangChenBound_one_one_two_two : yangChenBound ![1, 1, 2] 2 = 4 := by
  decide

/-- **A generalized $2$-fold sumset of $\{0, 1, 2\}$.** For $A = (0, 1, 2)$ in the integers and
$\bar r = (1, 1, 1)$, the generalized $2$-fold sumset $2^{(\bar r)}A$, the set of sums
$s_0 \cdot 0 + s_1 \cdot 1 + s_2 \cdot 2$ with $s_0, s_1, s_2 \in \{0, 1\}$ and
$s_0 + s_1 + s_2 = 2$, equals $\{1, 2, 3\}$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `h^{(r̄)}A`). -/
theorem generalizedHFoldSumset_zero_one_two :
    generalizedHFoldSumset ![(0 : ℤ), 1, 2] (fun _ => 1) 2 = {1, 2, 3} := by
  decide

/-- **Subset sums with a bounded number of terms.** For natural numbers $\alpha, \beta$ and a
finite subset $A$ of an additive commutative monoid $G$, the set $\Sigma^{\beta}_{\alpha}(A)$ is
the union of the restricted sumsets $m^{\wedge} A$ over $\alpha \le m \le |A| - \beta$, that is,
the set of sums $\sum_{b \in B} b$ over subsets $B \subseteq A$ with
$\alpha \le |B| \le |A| - \beta$. Here $|A| - \beta$ is read as $0$ when $\beta > |A|$.

The source assumes $\alpha + \beta \le |A|$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `Σ^β_α(A)`). -/
def boundedSubsetSums {G : Type*} [AddCommMonoid G] [DecidableEq G] (α β : ℕ)
    (A : Finset G) : Finset G :=
  (Finset.Icc α (A.card - β)).biUnion fun m => restrictedSumset m A

/-- **Bounded subset sums of $\{-1, 1, 2\}$.** The set $\Sigma^{1}_{1}(\{-1, 1, 2\})$ of sums of
subsets of the integer set $\{-1, 1, 2\}$ with at least $1$ and at most $2$ elements is
$\{-1, 0, 1, 2, 3\}$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 1 (definition of `Σ^β_α(A)`). -/
theorem boundedSubsetSums_one_one_neg_one_one_two :
    boundedSubsetSums 1 1 ({-1, 1, 2} : Finset ℤ) = {-1, 0, 1, 2, 3} := by
  decide

/-- **Sequence with prescribed multiplicities.** Let $G$ be a type, $k \in \mathbb{N}$,
$A = (a_0, \dots, a_{k-1})$ a $k$-tuple of elements of $G$ and $\bar t = (t_0, \dots, t_{k-1})$ a
$k$-tuple of natural numbers. The sequence $(A, \bar t)$ is the finite multiset of elements of $G$
obtained by taking $t_i$ copies of $a_i$ for each $i < k$; an element $x \in G$ thus occurs
$\sum_{i : a_i = x} t_i$ times.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (notation `(A, t̄)` for a finite sequence). -/
def repetitionSequence {G : Type*} {k : ℕ} (a : Fin k → G) (t : Fin k → ℕ) : Multiset G :=
  ∑ i, Multiset.replicate (t i) (a i)

/-- **Length of a sequence with repetitions.** Let $G$ be a set, $a_0, \dots, a_{k-1} \in G$ (not
necessarily distinct), $t_0, \dots, t_{k-1}$ natural numbers, $A = (a_0, \dots, a_{k-1})$ and
$\bar t = (t_0, \dots, t_{k-1})$. The multiset $(A, \bar t)$, made of $t_i$ copies of $a_i$ for
each $i$, has $t_0 + \dots + t_{k-1}$ elements counted with multiplicity.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (notation `(A, t̄)` for a finite sequence). -/
theorem card_repetitionSequence {G : Type*} {k : ℕ} (a : Fin k → G) (t : Fin k → ℕ) :
    Multiset.card (repetitionSequence a t) = ∑ i, t i := by
  simp [repetitionSequence]

/-- **Subsequence sums with a bounded number of terms.** For natural numbers $\alpha, \beta$ and a
finite sequence $\mathcal{A}$ (a multiset) in an additive commutative monoid $G$,
$\Sigma^\beta_\alpha(\mathcal{A})$ is the finite set of the sums $\sigma(\mathcal{B})$ of the
terms of the subsequences $\mathcal{B}$ of $\mathcal{A}$ (sub-multisets) with
$\alpha \le |\mathcal{B}|$ and $|\mathcal{B}| + \beta \le |\mathcal{A}|$, that is, with at least
$\alpha$ and at most $|\mathcal{A}| - \beta$ terms; it is empty when $\beta > |\mathcal{A}|$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (definition of `Σ^β_α(𝒜)`). -/
def boundedSubsequenceSums {G : Type*} [AddCommMonoid G] [DecidableEq G] (α β : ℕ)
    (S : Multiset G) : Finset G :=
  ((S.powerset.filter fun T => α ≤ Multiset.card T ∧ Multiset.card T + β ≤ Multiset.card S).map
    Multiset.sum).toFinset

/-- **An example of bounded subsequence sums.** For the sequence of integers
$\mathcal{A} = (-2, 7, 7)$, in which $-2$ occurs once and $7$ twice,
$\Sigma^1_1(\mathcal{A}) = \{-2, 5, 7, 14\}$: the sums of the subsequences with at least one and
at most two terms are $-2$, $7$, $-2 + 7 = 5$ and $7 + 7 = 14$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Section 4 (definition of `Σ^β_α(𝒜)`). -/
theorem boundedSubsequenceSums_one_one_example :
    boundedSubsequenceSums 1 1 (repetitionSequence ![(-2 : ℤ), 7] ![1, 2]) = {-2, 5, 7, 14} := by
  decide

/-- **Mixed-sign subset-sum bound.** For natural numbers $n$, $p$, $\alpha$, $\beta$ (the numbers
of negative and positive elements of a set $A$, and the bounds on subset sizes), let
$\kappa = n + p - \beta$, computed in the integers, $T(x) = x(x+1)/2$ and
$S = T(p) + T(n) + 1$. The integer $L_{n,p}(\alpha, \beta)$, written $L(\alpha, \beta, A)$ in
the source, is $S - T(\beta - n) - T(\beta - p)$ if $1 \le \alpha < \kappa < n \le p$;
$S - T(\beta - n)$ if $1 \le \alpha < n \le \kappa < p$ or $1 \le \alpha = n < \kappa \le p$;
$S$ if $1 \le \alpha < n \le p \le \kappa$, or $1 \le \alpha = n < p < \kappa$, or
$1 \le \alpha = n = p < \kappa$; $S - T(\beta - n) - T(\alpha - n)$ if
$1 \le n < \alpha < \kappa \le p$; $S - T(\alpha - n)$ if $1 \le n < \alpha < p < \kappa$ or
$1 \le n < \alpha = p < \kappa$; $S - T(\alpha - n) - T(\alpha - p)$ if
$1 \le n \le p < \alpha < \kappa$; and $0$ otherwise.

These six cases are mutually exclusive, and when $1 \le n \le p$, $1 \le \alpha$ and
$\alpha + \beta + 1 \le n + p$ exactly one of them applies.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (definition of `L(α, β, A)`). -/
def mixedSignSubsetSumBound (n p α β : ℕ) : ℤ :=
  let N : ℤ := n
  let P : ℤ := p
  let a : ℤ := α
  let b : ℤ := β
  let kb : ℤ := N + P - b
  let T : ℤ → ℤ := fun x => x * (x + 1) / 2
  let base : ℤ := T P + T N + 1
  if 1 ≤ a ∧ a < kb ∧ kb < N ∧ N ≤ P then base - T (b - N) - T (b - P)
  else if (1 ≤ a ∧ a < N ∧ N ≤ kb ∧ kb < P) ∨ (1 ≤ a ∧ a = N ∧ N < kb ∧ kb ≤ P) then
    base - T (b - N)
  else if (1 ≤ a ∧ a < N ∧ N ≤ P ∧ P ≤ kb) ∨ (1 ≤ a ∧ a = N ∧ N < P ∧ P < kb) ∨
      (1 ≤ a ∧ a = N ∧ N = P ∧ P < kb) then base
  else if 1 ≤ N ∧ N < a ∧ a < kb ∧ kb ≤ P then base - T (b - N) - T (a - N)
  else if (1 ≤ N ∧ N < a ∧ a < P ∧ P < kb) ∨ (1 ≤ N ∧ N < a ∧ a = P ∧ P < kb) then
    base - T (a - N)
  else if 1 ≤ N ∧ N ≤ P ∧ P < a ∧ a < kb then base - T (a - N) - T (a - P)
  else 0

/-- **A value of the mixed-sign subset-sum bound.** For $n = 1$, $p = 2$ and $\alpha = \beta = 1$,
the mixed-sign subset-sum bound is $L_{1,2}(1, 1) = 5$; this value comes from its second case.

It is attained by $A = \{-1, 1, 2\}$: the sums of subsets of $A$ with one or two elements form
$\{-1, 0, 1, 2, 3\}$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (definition of `L(α, β, A)`). -/
theorem mixedSignSubsetSumBound_one_two_one_one : mixedSignSubsetSumBound 1 2 1 1 = 5 := by
  decide

/-- **Mixed-sign subset-sum bound with zero.** For natural numbers $n$, $p$, $\alpha$, $\beta$
(the numbers of negative and positive elements of a set $A$ that also contains $0$, and the
bounds on subset sizes), let $\kappa = n + p + 1 - \beta$, computed in the integers,
$T(x) = x(x+1)/2$, $T_0(x) = x(x-1)/2$ and $S = T(p) + T(n) + 1$. The integer
$L^0_{n,p}(\alpha, \beta)$, written $L_0(\alpha, \beta, A)$ in the source, is
$S - T_0(\beta - n) - T_0(\beta - p)$ if $1 \le \alpha < \kappa < n \le p$;
$S - T_0(\beta - n)$ if $1 \le \alpha < n \le \kappa < p$ or $1 \le \alpha = n < \kappa \le p$;
$S$ if $1 \le \alpha < n \le p \le \kappa$, or $1 \le \alpha = n < p < \kappa$, or
$1 \le \alpha = n = p < \kappa$; $S - T_0(\beta - n) - T_0(\alpha - n)$ if
$1 \le n < \alpha < \kappa \le p$; $S - T_0(\alpha - n)$ if $1 \le n < \alpha < p < \kappa$ or
$1 \le n < \alpha = p < \kappa$; $S - T_0(\alpha - n) - T_0(\alpha - p)$ if
$1 \le n \le p < \alpha < \kappa$; and $0$ otherwise.

These six cases are mutually exclusive, and when $1 \le n \le p$, $1 \le \alpha$ and
$\alpha + \beta + 1 \le n + p + 1$ exactly one of them applies.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (definition of `L₀(α, β, A)`). -/
def mixedSignZeroSubsetSumBound (n p α β : ℕ) : ℤ :=
  let N : ℤ := n
  let P : ℤ := p
  let a : ℤ := α
  let b : ℤ := β
  let kb : ℤ := N + P + 1 - b
  let T : ℤ → ℤ := fun x => x * (x + 1) / 2
  let T₀ : ℤ → ℤ := fun x => x * (x - 1) / 2
  let base : ℤ := T P + T N + 1
  if 1 ≤ a ∧ a < kb ∧ kb < N ∧ N ≤ P then base - T₀ (b - N) - T₀ (b - P)
  else if (1 ≤ a ∧ a < N ∧ N ≤ kb ∧ kb < P) ∨ (1 ≤ a ∧ a = N ∧ N < kb ∧ kb ≤ P) then
    base - T₀ (b - N)
  else if (1 ≤ a ∧ a < N ∧ N ≤ P ∧ P ≤ kb) ∨ (1 ≤ a ∧ a = N ∧ N < P ∧ P < kb) ∨
      (1 ≤ a ∧ a = N ∧ N = P ∧ P < kb) then base
  else if 1 ≤ N ∧ N < a ∧ a < kb ∧ kb ≤ P then base - T₀ (b - N) - T₀ (a - N)
  else if (1 ≤ N ∧ N < a ∧ a < P ∧ P < kb) ∨ (1 ≤ N ∧ N < a ∧ a = P ∧ P < kb) then
    base - T₀ (a - N)
  else if 1 ≤ N ∧ N ≤ P ∧ P < a ∧ a < kb then base - T₀ (a - N) - T₀ (a - P)
  else 0

/-- **A value of the mixed-sign subset-sum bound with zero.** For $n = p = 1$ and
$\alpha = \beta = 1$, the mixed-sign subset-sum bound with zero is $L^0_{1,1}(1, 1) = 3$; this
value comes from its third case.

It is attained by $A = \{-1, 0, 1\}$: the sums of subsets of $A$ with one or two elements form
$\{-1, 0, 1\}$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (definition of `L₀(α, β, A)`). -/
theorem mixedSignZeroSubsetSumBound_one_one_one_one :
    mixedSignZeroSubsetSumBound 1 1 1 1 = 3 := by
  decide

/-! ## The generalized `h`-fold sumset (Yang and Chen) -/

/-- **Yang–Chen lower bound for generalized $h$-fold sumsets.** Let $k, h \in \mathbb{N}$ and let
$\bar r = (r_0, \dots, r_{k-1})$ be positive integers with $2 \le h \le r_0 + \dots + r_{k-1}$, and
let $L(\bar r, h)$ be the Yang–Chen bound. For all integers $a_0 < a_1 < \dots < a_{k-1}$, the
generalized $h$-fold sumset $h^{(\bar r)}A$ of $A = (a_0, \dots, a_{k-1})$ has at least
$L(\bar r, h)$ elements; and there exist integers $a_0 < a_1 < \dots < a_{k-1}$ for which
$h^{(\bar r)}A$ has exactly $L(\bar r, h)$ elements.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 2 (Yang and Chen) (`integers-2024-A116-thm-2`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_ge {k : ℕ} (r : Fin k → ℕ)
    (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h) (hhr : h ≤ ∑ i, r i) :
    (∀ a : Fin k → ℤ, StrictMono a →
      yangChenBound r h ≤ (generalizedHFoldSumset a r h).card) ∧
    ∃ a : Fin k → ℤ, StrictMono a ∧
      ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h

/-- **Yang–Chen inverse theorem for at least five terms.** Let $k \ge 5$ and $h \ge 2$ be integers,
let $\bar r = (r_0, \dots, r_{k-1})$ be positive integers with $h \le r_0 + \dots + r_{k-1} - 2$,
and let $L(\bar r, h)$ be the Yang–Chen bound. For all integers $a_0 < a_1 < \dots < a_{k-1}$,
with $A = \{a_0, \dots, a_{k-1}\}$, the generalized $h$-fold sumset $h^{(\bar r)}A$ has exactly
$L(\bar r, h)$ elements if and only if $A$ is an arithmetic progression of length $k$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 3 (Yang and Chen) (`integers-2024-A116-thm-3`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_iff_isAP {k : ℕ} (hk : 5 ≤ k)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h) (hhr : h + 2 ≤ ∑ i, r i)
    (a : Fin k → ℤ) (ha : StrictMono a) :
    ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength k

/-- **Yang–Chen inverse theorem for three terms.** Let $a_0 < a_1 < a_2$ be integers,
$A = \{a_0, a_1, a_2\}$, $\bar r = (r_0, r_1, r_2)$ positive integers and $h \ge 2$ an integer
with $h \le r_0 + r_1 + r_2 - 2$, and let $L(\bar r, h)$ be the Yang–Chen bound. If $r_1 = 1$,
then the generalized $h$-fold sumset $h^{(\bar r)}A$ has exactly $L(\bar r, h)$ elements. If
$r_1 \ge 2$, then $h^{(\bar r)}A$ has exactly $L(\bar r, h)$ elements if and only if $A$ is an
arithmetic progression of length $3$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 4 (Yang and Chen) (`integers-2024-A116-thm-4`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_three (a : Fin 3 → ℤ)
    (ha : StrictMono a) (r : Fin 3 → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h)
    (hhr : h + 2 ≤ r 0 + r 1 + r 2) :
    (r 1 = 1 → ((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h) ∧
    (2 ≤ r 1 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength 3))

/-- **Yang–Chen inverse theorem for four terms.** Let $a_0 < a_1 < a_2 < a_3$ be integers,
$A = \{a_0, a_1, a_2, a_3\}$, $\bar r = (r_0, r_1, r_2, r_3)$ positive integers and $h \ge 2$ an
integer with $h \le r_0 + r_1 + r_2 + r_3 - 2$, and let $L(\bar r, h)$ be the Yang–Chen bound.
If $r_1 = r_2 = 1$, then the generalized $h$-fold sumset $h^{(\bar r)}A$ has exactly
$L(\bar r, h)$ elements if and only if $a_1 - a_0 = a_3 - a_2$. If $r_1 \ge 2$ or $r_2 \ge 2$,
then $h^{(\bar r)}A$ has exactly $L(\bar r, h)$ elements if and only if $A$ is an arithmetic
progression of length $4$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 5 (Yang and Chen) (`integers-2024-A116-thm-5`). -/
public theorem_wanted yangChen_card_generalizedHFoldSumset_eq_four (a : Fin 4 → ℤ)
    (ha : StrictMono a) (r : Fin 4 → ℕ) (hr : ∀ i, 0 < r i) (h : ℕ) (hh : 2 ≤ h)
    (hhr : h + 2 ≤ r 0 + r 1 + r 2 + r 3) :
    (r 1 = 1 → r 2 = 1 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      a 1 - a 0 = a 3 - a 2)) ∧
    (2 ≤ r 1 ∨ 2 ≤ r 2 → (((generalizedHFoldSumset a r h).card : ℤ) = yangChenBound r h ↔
      (Set.range a).IsAPOfLength 4))

/-! ## Subset sums as generalized `h`-fold sumsets -/

/-- **Bounded subset sums as a generalized h-fold sumset when zero is not in the set.** Let $G$
be an abelian group and let $A = \{a_1, \dots, a_k\}$ be a set of $k$ distinct nonzero elements
of $G$. If $\alpha, \beta$ are natural numbers with $\alpha + \beta \le k - 1$, then
$\Sigma^\beta_\alpha(A)$, the set of sums of subsets $B \subseteq A$ with
$\alpha \le |B| \le k - \beta$, equals the generalized $(k - \beta)$-fold sumset
$(k - \beta)^{(\bar r)} A_0$ of $A_0 = (a_0, a_1, \dots, a_k)$, where $a_0 = 0$, with
$\bar r = (k - \alpha - \beta, 1, \dots, 1)$, that is, the set of sums $\sum_{j=0}^{k} s_j a_j$
with $0 \le s_j \le r_j$ for all $j$ and $\sum_j s_j = k - \beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 1 (`integers-2024-A116-lem-1`). -/
public theorem_wanted boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_not_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (b : Fin k → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hαβ : α + β + 1 ≤ k) :
    boundedSubsetSums α β (Finset.univ.image b) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (k + 1) → G)
        (Fin.cons (k - α - β) fun _ => 1 : Fin (k + 1) → ℕ) (k - β)

/-- **Bounded subset sums as a generalized h-fold sumset when zero is in the set.** Let $G$ be an
abelian group, let $m$ be a natural number, let $a_1, \dots, a_m$ be distinct nonzero elements
of $G$, put $a_0 = 0$ and $k = m + 1$, and let $A = \{a_0, a_1, \dots, a_m\}$, a set of $k$
elements. If $\alpha, \beta$ are natural numbers with $\alpha \ge 1$, $\beta \le k - 1$ and
$\alpha + \beta \le k$, then $\Sigma^\beta_\alpha(A)$, the set of sums of subsets $B \subseteq A$
with $\alpha \le |B| \le k - \beta$, equals the generalized $(k - \beta)$-fold sumset
$(k - \beta)^{(\bar r)} A$ of $A$ listed as $(a_0, a_1, \dots, a_m)$, with
$\bar r = (k - \alpha - \beta + 1, 1, \dots, 1)$, that is, the set of sums
$\sum_{j=0}^{m} s_j a_j$ with $0 \le s_j \le r_j$ for all $j$ and $\sum_j s_j = k - \beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 2 (`integers-2024-A116-lem-2`). -/
public theorem_wanted boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hα : 1 ≤ α) (hβ : β ≤ m)
    (hαβ : α + β ≤ m + 1) :
    boundedSubsetSums α β (Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → G)) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (m + 1 - α - β + 1) fun _ => 1 : Fin (m + 1) → ℕ) (m + 1 - β)

/-- **Reordering invariance of the generalized $h$-fold sumset.** Let $G$ be an additive
commutative monoid, $a_0, \dots, a_{k-1} \in G$, $r_0, \dots, r_{k-1}$ and $h$ natural numbers,
and write $h^{(\bar r)}A = \{\sum_j s_j a_j : 0 \le s_j \le r_j, \sum_j s_j = h\}$ for the
generalized $h$-fold sumset of $A = (a_0, \dots, a_{k-1})$ with $\bar r = (r_0, \dots, r_{k-1})$.
For every permutation $\pi$ of $\{0, \dots, k-1\}$, the generalized $h$-fold sumset of
$(a_{\pi(0)}, \dots, a_{\pi(k-1)})$ with $(r_{\pi(0)}, \dots, r_{\pi(k-1)})$ equals
$h^{(\bar r)}A$.

The paper assumes $h \ge 2$, all $r_j$ positive and the $a_j$ distinct; none of this is assumed
here.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 3 (`integers-2024-A116-lem-3`). -/
public theorem_wanted generalizedHFoldSumset_comp_perm {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {k : ℕ} (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) (π : Equiv.Perm (Fin k)) :
    generalizedHFoldSumset (a ∘ π) (r ∘ π) h = generalizedHFoldSumset a r h

/-- **Bounded subsequence sums as a generalized h-fold sumset when zero is not a term.** Let $G$
be an abelian group and let $a_1, \dots, a_k$ be distinct nonzero elements of $G$. Let
$t_1, \dots, t_k$ be positive integers, let $\mathcal{A}$ be the sequence in which each $a_i$
occurs $t_i$ times, and let $h = t_1 + \dots + t_k$ be its length. If $\alpha, \beta$ are natural
numbers with $\alpha \ge 1$ and $\alpha + \beta \le h - 1$, then $\Sigma^\beta_\alpha(\mathcal{A})$,
the set of sums of subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$
terms, equals the generalized $(h - \beta)$-fold sumset $(h - \beta)^{(\bar r)} A_0$ of
$A_0 = (a_0, a_1, \dots, a_k)$, where $a_0 = 0$, with
$\bar r = (h - \alpha - \beta, t_1, \dots, t_k)$, that is, the set of sums
$\sum_{j=0}^{k} s_j a_j$ with $0 \le s_j \le r_j$ for all $j$ and $\sum_j s_j = h - \beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 4 (`integers-2024-A116-lem-4`). -/
public theorem_wanted boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (b : Fin k → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (t : Fin k → ℕ) (ht : ∀ i, 0 < t i)
    (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ h) :
    boundedSubsequenceSums α β (repetitionSequence b t) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (k + 1) → G)
        (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)

/-- **Bounded subsequence sums as a generalized h-fold sumset when zero is a term.** Let $G$ be
an abelian group, let $m$ be a natural number, let $a_1, \dots, a_m$ be distinct nonzero elements
of $G$, and put $a_0 = 0$. Let $t_0, \dots, t_m$ be positive integers, let $\mathcal{A}$ be the
sequence in which each $a_i$ occurs $t_i$ times, and let $h = t_0 + \dots + t_m$ be its length.
If $\alpha, \beta$ are natural numbers with $\alpha \ge 1$, $\beta \le h - 1$ and
$\alpha + \beta \le h$, then $\Sigma^\beta_\alpha(\mathcal{A})$, the set of sums of subsequences
of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, equals the generalized
$(h - \beta)$-fold sumset $(h - \beta)^{(\bar r)} A$ of $A = (a_0, a_1, \dots, a_m)$ with
$\bar r = (h - \alpha - \beta + t_0, t_1, \dots, t_m)$, that is, the set of sums
$\sum_{j=0}^{m} s_j a_j$ with $0 \le s_j \le r_j$ for all $j$ and $\sum_j s_j = h - \beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 5 (`integers-2024-A116-lem-5`). -/
public theorem_wanted boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (t : Fin (m + 1) → ℕ) (ht : ∀ i, 0 < t i)
    (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hβ : β + 1 ≤ h) (hαβ : α + β ≤ h) :
    boundedSubsequenceSums α β (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → G) t) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)

/-! ## Direct and inverse theorems for subset sums -/

/-- **Sharp lower bounds for bounded subset sums of nonnegative sets.** Let $k$, $\alpha$, $\beta$
be natural numbers with $k \ge 2$, $\alpha \ge 1$ and $\alpha + \beta + 1 \le k$. For a finite set
$A$ of integers write $\Sigma_\alpha^\beta(A)$ for the set of sums of subsets $B \subseteq A$ with
$\alpha \le |B| \le |A| - \beta$. Every set $A$ of $k$ positive integers satisfies
$|\Sigma_\alpha^\beta(A)| \ge \binom{k+1}{2} - \binom{\alpha+1}{2} - \binom{\beta+1}{2} + 1$,
and every set $A$ of $k$ nonnegative integers containing $0$ satisfies
$|\Sigma_\alpha^\beta(A)| \ge \binom{k}{2} - \binom{\alpha}{2} - \binom{\beta}{2} + 1$. Both
bounds are attained: the first by $A = \{1, 2, \dots, k\}$ and the second by
$A = \{0, 1, \dots, k - 1\}$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 6 (`integers-2024-A116-thm-6`). -/
public theorem_wanted card_boundedSubsetSums_ge_of_nonneg (k α β : ℕ) (hk : 2 ≤ k)
    (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ k) :
    (∀ A : Finset ℤ, A.card = k → (∀ x ∈ A, 0 < x) →
      ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 ≤
        (boundedSubsetSums α β A).card) ∧
    (∀ A : Finset ℤ, A.card = k → (∀ x ∈ A, 0 ≤ x) → 0 ∈ A →
      (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1 ≤ (boundedSubsetSums α β A).card) ∧
    ((boundedSubsetSums α β (Finset.Icc 1 (k : ℤ))).card : ℤ) =
      ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 ∧
    ((boundedSubsetSums α β (Finset.Icc 0 ((k : ℤ) - 1))).card : ℤ) =
      (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1

/-- **Lower bound for bounded subset sums of a mixed-sign set.** Let $n$, $p$, $\alpha$, $\beta$ be
natural numbers with $1 \le n \le p$, $1 \le \alpha$ and $\alpha + \beta + 1 \le n + p$, and let
$L_{n,p}(\alpha, \beta)$ be the mixed-sign subset-sum bound. For a finite set $A$ of integers write
$\Sigma_\alpha^\beta(A)$ for the set of sums of subsets $B \subseteq A$ with
$\alpha \le |B| \le |A| - \beta$. Every finite set $A$ of nonzero integers with exactly $n$
negative and exactly $p$ positive elements satisfies
$|\Sigma_\alpha^\beta(A)| \ge L_{n,p}(\alpha, \beta)$, and some such set $A$ attains equality.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 7 (`integers-2024-A116-thm-7`). -/
public theorem_wanted card_boundedSubsetSums_ge_mixedSign (n p α β : ℕ) (hn : 1 ≤ n)
    (hnp : n ≤ p) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ n + p) :
    (∀ A : Finset ℤ, 0 ∉ A → (A.filter (· < 0)).card = n → (A.filter (0 < ·)).card = p →
      mixedSignSubsetSumBound n p α β ≤ (boundedSubsetSums α β A).card) ∧
    ∃ A : Finset ℤ, 0 ∉ A ∧ (A.filter (· < 0)).card = n ∧ (A.filter (0 < ·)).card = p ∧
      ((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β

/-- **Lower bound for subset sums of a mixed-sign set containing zero.** Let $n, p, \alpha, \beta$
be natural numbers with $1 \le n \le p$, $1 \le \alpha$ and $\alpha + \beta \le n + p$. Every
finite set $A$ of integers that contains $0$, exactly $n$ negative integers and exactly $p$
positive integers satisfies $|\Sigma^{\beta}_{\alpha}(A)| \ge L_0(\alpha, \beta, A)$, and some
such set $A$ attains equality. Here $\Sigma^{\beta}_{\alpha}(A)$ is the set of sums of subsets
$B \subseteq A$ with $\alpha \le |B| \le |A| - \beta$, and $L_0(\alpha, \beta, A)$ is the
mixed-sign bound with zero, which depends only on $n$, $p$, $\alpha$ and $\beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 8 (`integers-2024-A116-thm-8`). -/
public theorem_wanted card_boundedSubsetSums_ge_mixedSign_zero (n p α β : ℕ) (hn : 1 ≤ n)
    (hnp : n ≤ p) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ n + p + 1) :
    (∀ A : Finset ℤ, 0 ∈ A → (A.filter (· < 0)).card = n → (A.filter (0 < ·)).card = p →
      mixedSignZeroSubsetSumBound n p α β ≤ (boundedSubsetSums α β A).card) ∧
    ∃ A : Finset ℤ, 0 ∈ A ∧ (A.filter (· < 0)).card = n ∧ (A.filter (0 < ·)).card = p ∧
      ((boundedSubsetSums α β A).card : ℤ) = mixedSignZeroSubsetSumBound n p α β

/-- **Inverse theorem for subset sums of nonnegative sets.** Let $k \ge 3$ and let $\alpha, \beta$
be natural numbers with $1 \le \alpha \le k - 2$, $\beta \le k - 2$ and $\alpha + \beta \le k - 1$.
Let $A$ be a set of $k$ integers, and let $\Sigma^{\beta}_{\alpha}(A)$ be the set of sums of
subsets $B \subseteq A$ with $\alpha \le |B| \le k - \beta$. If all elements of $A$ are positive
and $|\Sigma^{\beta}_{\alpha}(A)| = \binom{k+1}{2} - \binom{\alpha+1}{2} - \binom{\beta+1}{2} + 1$,
then $A = d \cdot \{1, 2, \dots, k\}$ for some integer $d > 0$ when $k \ne 3$, and
$A = \{x, y, x + y\}$ for some integers $0 < x < y$ when $k = 3$. If all elements of $A$ are
nonnegative, $0 \in A$ and
$|\Sigma^{\beta}_{\alpha}(A)| = \binom{k}{2} - \binom{\alpha}{2} - \binom{\beta}{2} + 1$, then
$A = d \cdot \{0, 1, \dots, k - 1\}$ for some integer $d > 0$ when $k \ge 5$,
$A = \{0, x, y\}$ for some integers $0 < x < y$ when $k = 3$, and
$A = \{0, x, y, x + y\}$ for some integers $0 < x < y$ when $k = 4$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 9 (`integers-2024-A116-thm-9`). -/
public theorem_wanted boundedSubsetSums_inverse_of_nonneg (A : Finset ℤ) (k α β : ℕ)
    (hk : 3 ≤ k) (hA : A.card = k) (hα : 1 ≤ α) (hα2 : α + 2 ≤ k) (hβ : β + 2 ≤ k)
    (hαβ : α + β + 1 ≤ k) :
    ((∀ x ∈ A, 0 < x) → ((boundedSubsetSums α β A).card : ℤ) =
        ((k + 1).choose 2 : ℤ) - (α + 1).choose 2 - (β + 1).choose 2 + 1 →
      (k ≠ 3 → ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc 1 (k : ℤ)) ∧
      (k = 3 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {x, y, x + y})) ∧
    ((∀ x ∈ A, 0 ≤ x) → 0 ∈ A → ((boundedSubsetSums α β A).card : ℤ) =
        (k.choose 2 : ℤ) - α.choose 2 - β.choose 2 + 1 →
      (5 ≤ k → ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc 0 ((k : ℤ) - 1)) ∧
      (k = 3 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {0, x, y}) ∧
      (k = 4 → ∃ x y : ℤ, 0 < x ∧ x < y ∧ A = {0, x, y, x + y}))

/-- **Inverse theorem for subset sums of a mixed-sign set.** Let $n, p, \alpha, \beta$ be natural
numbers with $1 \le n \le p$, put $k = n + p$, and assume $1 \le \alpha \le k - 2$,
$\beta \le k - 2$ and $\alpha + \beta \le k - 1$. Let $A$ be a finite set of integers that does
not contain $0$ and has exactly $n$ negative and exactly $p$ positive elements, and write $E$ for
the equation $|\Sigma^{\beta}_{\alpha}(A)| = L(\alpha, \beta, A)$. If $k = 3$, $\alpha = 1$ and
$\beta = 0$, then $E$ holds if and only if $A = d \cdot \{-1, 1, 2\}$ for some integer $d > 0$.
If $k = 3$ and $\alpha = \beta = 1$, then $E$ holds if and only if $A = \{x, x + y, y\}$ for some
integers $x, y$ with $x < 0 < x + y < y$. If $k \ge 4$, then $E$ holds if and only if
$A = d \cdot \{-n, \dots, -1, 1, \dots, p\}$ for some integer $d > 0$. Here
$\Sigma^{\beta}_{\alpha}(A)$ is the set of sums of subsets $B \subseteq A$ with
$\alpha \le |B| \le |A| - \beta$, and $L(\alpha, \beta, A)$ is the mixed-sign bound, which
depends only on $n$, $p$, $\alpha$ and $\beta$.

The factor $d$ is then the least positive element of $A$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 10 (`integers-2024-A116-thm-10`). -/
public theorem_wanted boundedSubsetSums_inverse_mixedSign (A : Finset ℤ) (n p α β : ℕ)
    (hA0 : 0 ∉ A) (hneg : (A.filter (· < 0)).card = n) (hpos : (A.filter (0 < ·)).card = p)
    (hn : 1 ≤ n) (hnp : n ≤ p) (hα : 1 ≤ α) (hα2 : α + 2 ≤ n + p) (hβ : β + 2 ≤ n + p)
    (hαβ : α + β + 1 ≤ n + p) :
    (n + p = 3 → α = 1 → β = 0 →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ d : ℤ, 0 < d ∧ A = d • ({-1, 1, 2} : Finset ℤ))) ∧
    (n + p = 3 → α = 1 → β = 1 →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ x y : ℤ, x < 0 ∧ 0 < x + y ∧ x + y < y ∧ A = {x, x + y, y})) ∧
    (4 ≤ n + p →
      (((boundedSubsetSums α β A).card : ℤ) = mixedSignSubsetSumBound n p α β ↔
        ∃ d : ℤ, 0 < d ∧ A = d • (Finset.Icc (-(n : ℤ)) p).erase 0))

/-- **Inverse theorem for subset sums of a mixed-sign set containing zero.** Let $n, p, \alpha,
\beta$ be natural numbers with $1 \le n \le p$, put $k = n + p + 1$, and assume
$1 \le \alpha \le k - 2$, $\beta \le k - 2$ and $\alpha + \beta \le k - 1$. Let $A$ be a finite set
of integers that contains $0$, exactly $n$ negative integers and exactly $p$ positive integers.
Then $|\Sigma^{\beta}_{\alpha}(A)| = L_0(\alpha, \beta, A)$ if and only if
$A = d \cdot \{-n, -n + 1, \dots, p\}$ for some integer $d > 0$. Here $\Sigma^{\beta}_{\alpha}(A)$
is the set of sums of subsets $B \subseteq A$ with $\alpha \le |B| \le |A| - \beta$, and
$L_0(\alpha, \beta, A)$ is the mixed-sign bound with zero, which depends only on $n$, $p$,
$\alpha$ and $\beta$.

The factor $d$ is then the least positive element of $A$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 11 (`integers-2024-A116-thm-11`). -/
public theorem_wanted boundedSubsetSums_inverse_mixedSign_zero (A : Finset ℤ) (n p α β : ℕ)
    (hA0 : 0 ∈ A) (hneg : (A.filter (· < 0)).card = n) (hpos : (A.filter (0 < ·)).card = p)
    (hn : 1 ≤ n) (hnp : n ≤ p) (hα : 1 ≤ α) (hα2 : α + 2 ≤ n + p + 1) (hβ : β + 2 ≤ n + p + 1)
    (hαβ : α + β + 1 ≤ n + p + 1) :
    ((boundedSubsetSums α β A).card : ℤ) = mixedSignZeroSubsetSumBound n p α β ↔
      ∃ d : ℤ, 0 < d ∧ A = d • Finset.Icc (-(n : ℤ)) p

/-! ## Direct theorems for subsequence sums -/

/-- **Lower bound for bounded subsequence sums of a positive sequence.** Let $k \ge 2$, let
$t_1, \dots, t_k$ be positive integers, let $h = t_1 + \dots + t_k$, and let $\alpha, \beta$ be
natural numbers with $1 \le \alpha$ and $\alpha + \beta \le h - 1$. Put
$\bar r = (h - \alpha - \beta, t_1, \dots, t_k)$. For integers $0 < b_1 < \dots < b_k$, let
$\mathcal{A}$ be the sequence in which $b_i$ occurs $t_i$ times. Then
$|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$ for all such $b$, and equality
holds for some such $b$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$ is the set of sums of
subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, and $L$ is the
Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 13 (`integers-2024-A116-thm-13`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_of_pos {k : ℕ} (hk : 2 ≤ k)
    (t : Fin k → ℕ) (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ b : Fin k → ℤ, StrictMono b → (∀ i, 0 < b i) →
      yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence b t)).card) ∧
    ∃ b : Fin k → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
      ((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)

/-- **Lower bound for bounded subsequence sums of a nonnegative sequence containing zero.** Let
$m \ge 1$, let $t_0, \dots, t_m$ be positive integers, let $h = t_0 + \dots + t_m$, and let
$\alpha, \beta$ be natural numbers with $1 \le \alpha$, $\beta \le h - 1$ and
$\alpha + \beta \le h$. Put $\bar r = (h - \alpha - \beta + t_0, t_1, \dots, t_m)$. For integers
$0 < b_1 < \dots < b_m$, let $\mathcal{A}$ be the sequence in which $0$ occurs $t_0$ times and
$b_i$ occurs $t_i$ times. Then $|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$
for all such $b$, and equality holds for some such $b$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$
is the set of sums of subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$
terms, and $L$ is the Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 14 (`integers-2024-A116-thm-14`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_of_nonneg_zero {m : ℕ} (hm : 1 ≤ m)
    (t : Fin (m + 1) → ℕ) (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ)
    (hα : 1 ≤ α) (hβ : β + 1 ≤ h) (hαβ : α + β ≤ h) :
    (∀ b : Fin m → ℤ, StrictMono b → (∀ i, 0 < b i) →
      yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ≤
        (boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card) ∧
    ∃ b : Fin m → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
      ((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)

/-- **Lower bound for bounded subsequence sums of a mixed-sign sequence.** Let $1 \le n \le p$, let
$t_0, \dots, t_{n-1}$ and $t_{n+1}, \dots, t_{n+p}$ be positive integers, let $h$ be their sum,
and let $\alpha, \beta$ be natural numbers with $1 \le \alpha$ and $\alpha + \beta \le h - 1$.
Put $\bar r = (t_0, \dots, t_{n-1}, h - \alpha - \beta, t_{n+1}, \dots, t_{n+p})$. For integers
$c_0 < \dots < c_{n-1} < 0 < d_1 < \dots < d_p$, let $\mathcal{A}$ be the sequence in which
$c_i$ occurs $t_i$ times and $d_j$ occurs $t_{n+j}$ times. Then
$|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$ for all such $c$ and $d$, and
equality holds for some such $c$ and $d$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$ is the set
of sums of subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, and
$L$ is the Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 15 (`integers-2024-A116-thm-15`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_mixedSign {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (tn : Fin n → ℕ) (tp : Fin p → ℕ) (htn : ∀ i, 0 < tn i)
    (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + ∑ j, tp j) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c → (∀ i, c i < 0) → StrictMono d →
      (∀ j, 0 < d j) →
      yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card) ∧
    ∃ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c ∧ (∀ i, c i < 0) ∧ StrictMono d ∧
      (∀ j, 0 < d j) ∧
      ((boundedSubsequenceSums α β (repetitionSequence c tn + repetitionSequence d tp)).card :
          ℤ) = yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β)

/-- **Lower bound for bounded subsequence sums of a mixed-sign sequence containing zero.** Let
$1 \le n \le p$, let $t_0, \dots, t_{n-1}$, $t_n$ and $t_{n+1}, \dots, t_{n+p}$ be positive
integers, let $h = t_0 + t_1 + \dots + t_{n+p}$, and let $\alpha, \beta$ be natural numbers with
$1 \le \alpha$ and $\alpha + \beta \le h - 1$. Put
$\bar r = (t_0, \dots, t_{n-1}, h - \alpha - \beta + t_n, t_{n+1}, \dots, t_{n+p})$. For integers
$c_0 < \dots < c_{n-1} < 0 < d_1 < \dots < d_p$, let $\mathcal{A}$ be the sequence in which
$c_i$ occurs $t_i$ times, $0$ occurs $t_n$ times and $d_j$ occurs $t_{n+j}$ times. Then
$|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$ for all such $c$ and $d$, and
equality holds for some such $c$ and $d$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$ is the set
of sums of subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, and
$L$ is the Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 16 (`integers-2024-A116-thm-16`). -/
public theorem_wanted card_boundedSubsequenceSums_ge_mixedSign_zero {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (tn : Fin n → ℕ) (tz : ℕ) (tp : Fin p → ℕ) (htn : ∀ i, 0 < tn i)
    (htz : 0 < tz) (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + tz + ∑ j, tp j)
    (α β : ℕ) (hα : 1 ≤ α) (hαβ : α + β + 1 ≤ h) :
    (∀ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c → (∀ i, c i < 0) → StrictMono d →
      (∀ j, 0 < d j) →
      yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card) ∧
    ∃ (c : Fin n → ℤ) (d : Fin p → ℤ), StrictMono c ∧ (∀ i, c i < 0) ∧ StrictMono d ∧
      (∀ j, 0 < d j) ∧
      ((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
        yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β)

/-! ## Inverse theorems for subsequence sums -/

/-- **Inverse theorem for bounded subsequence sums of positive sequences.** Let $k \ge 2$, let
$a_1 < \dots < a_k$ be positive integers and $A = \{a_1, \dots, a_k\}$, let $t_1, \dots, t_k$ be
positive integers, let $\mathcal{A}$ be the sequence in which each $a_i$ occurs $t_i$ times, and
let $h = t_1 + \dots + t_k$. Let $\alpha, \beta$ be natural numbers with
$1 \le \alpha \le h - 2$, $\beta \le h - 2$ and $\alpha + \beta \le h - 1$, put
$\bar r = (h - \alpha - \beta, t_1, \dots, t_k)$, and write $E$ for the equality
$|\Sigma^\beta_\alpha(\mathcal{A})| = L(\bar r, h - \beta)$, where $L$ is the Yang–Chen bound.
For an integer $e$ and a set $X$ write $e \cdot X = \{e x : x \in X\}$. Then:
(a) if $k = 2$ and $t_1 = 1$, then $E$ holds; if $k = 2$ and $t_1 \ge 2$, then $E$ holds if and
only if $A = e \cdot \{1, 2\}$ for some integer $e > 0$;
(b) if $k = 3$ and $t_1 = t_2 = 1$, then $E$ holds if and only if $A = \{x, y, x + y\}$ for some
integers $0 < x < y$; if $k = 3$ and $t_1 \ge 2$ or $t_2 \ge 2$, then $E$ holds if and only if
$A = e \cdot \{1, 2, 3\}$ for some integer $e > 0$;
(c) if $k \ge 4$, then $E$ holds if and only if $A = e \cdot \{1, 2, \dots, k\}$ for some integer
$e > 0$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 17 (`integers-2024-A116-thm-17`). -/
public theorem_wanted boundedSubsequenceSums_inverse_of_pos {k : ℕ} (hk : 2 ≤ k)
    (b : Fin k → ℤ) (hb : StrictMono b) (hbpos : ∀ i, 0 < b i) (t : Fin k → ℕ)
    (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β + 1 ≤ h) :
    (∀ hk2 : k = 2, t ⟨0, by omega⟩ = 1 →
      ((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β)) ∧
    (∀ hk2 : k = 2, 2 ≤ t ⟨0, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (2 : ℤ))) ∧
    (∀ hk3 : k = 3, t ⟨0, by omega⟩ = 1 → t ⟨1, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧ Finset.univ.image b = {x, y, x + y})) ∧
    (∀ hk3 : k = 3, 2 ≤ t ⟨0, by omega⟩ ∨ 2 ≤ t ⟨1, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (3 : ℤ))) ∧
    (4 ≤ k →
      (((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧ Finset.univ.image b = e • Finset.Icc 1 (k : ℤ)))

/-- **Inverse theorem for bounded subsequence sums of nonnegative sequences containing zero.** Let
$m \ge 2$, let $0 < a_1 < \dots < a_m$ be integers, put $a_0 = 0$ and
$A = \{a_0, a_1, \dots, a_m\}$, let $t_0, t_1, \dots, t_m$ be positive integers, let
$\mathcal{A}$ be the sequence in which each $a_i$ occurs $t_i$ times, and let
$h = t_0 + t_1 + \dots + t_m$. Let $\alpha, \beta$ be natural numbers with
$1 \le \alpha \le h - 2$, $\beta \le h - 2$ and $\alpha + \beta \le h - 1$, put
$\bar r = (h - \alpha - \beta + t_0, t_1, \dots, t_m)$, and write $E$ for the equality
$|\Sigma^\beta_\alpha(\mathcal{A})| = L(\bar r, h - \beta)$, where $L$ is the Yang–Chen bound.
For an integer $e$ and a set $X$ write $e \cdot X = \{e x : x \in X\}$. Then:
(a) if $m = 2$ and $t_1 = 1$, then $E$ holds; if $m = 2$ and $t_1 \ge 2$, then $E$ holds if and
only if $A = e \cdot \{0, 1, 2\}$ for some integer $e > 0$;
(b) if $m = 3$ and $t_1 = t_2 = 1$, then $E$ holds if and only if $A = \{0, x, y, x + y\}$ for
some integers $0 < x < y$; if $m = 3$ and $t_1 \ge 2$ or $t_2 \ge 2$, then $E$ holds if and only
if $A = e \cdot \{0, 1, 2, 3\}$ for some integer $e > 0$;
(c) if $m \ge 4$, then $E$ holds if and only if $A = e \cdot \{0, 1, \dots, m\}$ for some integer
$e > 0$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 18 (`integers-2024-A116-thm-18`). -/
public theorem_wanted boundedSubsequenceSums_inverse_of_nonneg_zero {m : ℕ} (hm : 2 ≤ m)
    (b : Fin m → ℤ) (hb : StrictMono b) (hbpos : ∀ i, 0 < b i) (t : Fin (m + 1) → ℕ)
    (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β + 1 ≤ h) :
    (m = 2 → t ⟨1, by omega⟩ = 1 →
      ((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β)) ∧
    (m = 2 → 2 ≤ t ⟨1, by omega⟩ →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (2 : ℤ))) ∧
    (m = 3 → t ⟨1, by omega⟩ = 1 → t ⟨2, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = {0, x, y, x + y})) ∧
    (m = 3 → 2 ≤ t ⟨1, by omega⟩ ∨ 2 ≤ t ⟨2, by omega⟩ →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (3 : ℤ))) ∧
    (4 ≤ m →
      (((boundedSubsequenceSums α β
          (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → ℤ) t)).card : ℤ) =
          yangChenBound (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → ℤ) = e • Finset.Icc 0 (m : ℤ)))

/-- **Inverse theorem for bounded subsequence sums of mixed-sign sequences without zero.** Let
$1 \le n \le p$, let $c_1 < \dots < c_n < 0 < d_1 < \dots < d_p$ be integers and
$A = \{c_1, \dots, c_n, d_1, \dots, d_p\}$, let $s_1, \dots, s_n, t_1, \dots, t_p$ be positive
integers, let $\mathcal{A}$ be the sequence in which each $c_i$ occurs $s_i$ times and each $d_j$
occurs $t_j$ times, and let $h = s_1 + \dots + s_n + t_1 + \dots + t_p$, with $h \ge 3$. Let
$\alpha, \beta$ be natural numbers with $1 \le \alpha \le h - 2$, $\beta \le h - 2$ and
$\alpha + \beta \le h - 1$, put $\bar r = (s_1, \dots, s_n, h - \alpha - \beta, t_1, \dots, t_p)$,
and write $E$ for the equality $|\Sigma^\beta_\alpha(\mathcal{A})| = L(\bar r, h - \beta)$, where
$L$ is the Yang–Chen bound. Then:
(a) if $n + p = 3$, $\alpha + \beta = h - 1$ and $t_1 = 1$, then $E$ holds if and only if
$A = \{x - y, x, y\}$ for some integers $0 < x < y$;
(b) in every other case, except $n + p = 2$ with $\alpha + \beta = h - 1$, $E$ holds if and only
if $A = \{e x : x \in \{-n, \dots, -1, 1, \dots, p\}\}$ for some integer $e > 0$.

The source states (b) also for $n + p = 2$ and $\alpha + \beta = h - 1$, but there $E$ holds for
every $A$: for $A = \{-2, 7\}$ with $s_1 = 1$, $t_1 = 2$ and $\alpha = \beta = 1$ one has
$|\Sigma^1_1(\mathcal{A})| = |\{-2, 5, 7, 14\}| = 4 = L((1, 1, 2), 2)$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 19 (`integers-2024-A116-thm-19`). -/
public theorem_wanted boundedSubsequenceSums_inverse_mixedSign {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (c : Fin n → ℤ) (d : Fin p → ℤ) (hc : StrictMono c) (hcneg : ∀ i, c i < 0)
    (hd : StrictMono d) (hdpos : ∀ j, 0 < d j) (tn : Fin n → ℕ) (tp : Fin p → ℕ)
    (htn : ∀ i, 0 < tn i) (htp : ∀ j, 0 < tp j) (h : ℕ) (hh : h = ∑ i, tn i + ∑ j, tp j)
    (hh3 : 3 ≤ h) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h) (hβ : β + 2 ≤ h)
    (hαβ : α + β + 1 ≤ h) :
    (n + p = 3 → α + β + 1 = h → tp ⟨0, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β
          (repetitionSequence c tn + repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧ Finset.univ.image c ∪ Finset.univ.image d = {x - y, x, y})) ∧
    (¬ (n + p = 3 ∧ α + β + 1 = h ∧ tp ⟨0, by omega⟩ = 1) → ¬ (n + p = 2 ∧ α + β + 1 = h) →
      (((boundedSubsequenceSums α β
          (repetitionSequence c tn + repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          Finset.univ.image c ∪ Finset.univ.image d = e • (Finset.Icc (-(n : ℤ)) p).erase 0))

/-- **Inverse theorem for bounded subsequence sums of mixed-sign sequences containing zero.** Let
$1 \le n \le p$, let $c_1 < \dots < c_n < 0 < d_1 < \dots < d_p$ be integers and
$A = \{c_1, \dots, c_n, 0, d_1, \dots, d_p\}$, a set of $k = n + p + 1$ elements, let
$s_1, \dots, s_n, z, t_1, \dots, t_p$ be positive integers, let $\mathcal{A}$ be the sequence in
which each $c_i$ occurs $s_i$ times, $0$ occurs $z$ times and each $d_j$ occurs $t_j$ times, and
let $h = s_1 + \dots + s_n + z + t_1 + \dots + t_p$. Let $\alpha, \beta$ be natural numbers with
$1 \le \alpha \le h - 2$, $\beta \le h - 2$ and $\alpha + \beta \le h$, put
$\bar r = (s_1, \dots, s_n, h - \alpha - \beta + z, t_1, \dots, t_p)$, and write $E$ for the
equality $|\Sigma^\beta_\alpha(\mathcal{A})| = L(\bar r, h - \beta)$, where $L$ is the Yang–Chen
bound. For an integer $e$ and a set $X$ write $e \cdot X = \{e x : x \in X\}$. Then:
(a) if $k = 3$ and $\alpha + \beta = h$, then $E$ holds when $z = 1$, and for $z \ge 2$, $E$ holds
if and only if $A = e \cdot \{-1, 0, 1\}$ for some integer $e > 0$;
(b) if $k = 3$ and $\alpha + \beta \le h - 1$, then $E$ holds if and only if
$A = e \cdot \{-1, 0, 1\}$ for some integer $e > 0$;
(c) if $k = 4$ and $\alpha + \beta = h$, then for $z = t_1 = 1$, $E$ holds if and only if
$A = \{x - y, 0, x, y\}$ for some integers $0 < x < y$, and for $z \ge 2$ or $t_1 \ge 2$, $E$
holds if and only if $A = e \cdot \{-1, 0, 1, 2\}$ for some integer $e > 0$;
(d) if $k = 4$ and $\alpha + \beta \le h - 1$, then $E$ holds if and only if
$A = e \cdot \{-1, 0, 1, 2\}$ for some integer $e > 0$;
(e) if $k \ge 5$, then $E$ holds if and only if $A = e \cdot \{-n, \dots, p\}$ for some integer
$e > 0$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 20 (`integers-2024-A116-thm-20`). -/
public theorem_wanted boundedSubsequenceSums_inverse_mixedSign_zero {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) (c : Fin n → ℤ) (d : Fin p → ℤ) (hc : StrictMono c) (hcneg : ∀ i, c i < 0)
    (hd : StrictMono d) (hdpos : ∀ j, 0 < d j) (tn : Fin n → ℕ) (tz : ℕ) (tp : Fin p → ℕ)
    (htn : ∀ i, 0 < tn i) (htz : 0 < tz) (htp : ∀ j, 0 < tp j) (h : ℕ)
    (hh : h = ∑ i, tn i + tz + ∑ j, tp j) (α β : ℕ) (hα : 1 ≤ α) (hα2 : α + 2 ≤ h)
    (hβ : β + 2 ≤ h) (hαβ : α + β ≤ h) :
    (n + p + 1 = 3 → α + β = h → tz = 1 →
      ((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
        yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β)) ∧
    (n + p + 1 = 3 → α + β = h → 2 ≤ tz →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 1)) ∧
    (n + p + 1 = 3 → α + β + 1 ≤ h →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 1)) ∧
    (n + p + 1 = 4 → α + β = h → tz = 1 → tp ⟨0, by omega⟩ = 1 →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ x y : ℤ, 0 < x ∧ x < y ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = {x - y, 0, x, y})) ∧
    (n + p + 1 = 4 → α + β = h → 2 ≤ tz ∨ 2 ≤ tp ⟨0, by omega⟩ →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 2)) ∧
    (n + p + 1 = 4 → α + β + 1 ≤ h →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-1 : ℤ) 2)) ∧
    (5 ≤ n + p + 1 →
      (((boundedSubsequenceSums α β (repetitionSequence c tn + Multiset.replicate tz 0 +
          repetitionSequence d tp)).card : ℤ) =
          yangChenBound (Fin.append tn (Fin.cons (h - α - β + tz) tp)) (h - β) ↔
        ∃ e : ℤ, 0 < e ∧
          insert 0 (Finset.univ.image c ∪ Finset.univ.image d) = e • Finset.Icc (-(n : ℤ)) p))

end

end MetaMathlibExt
