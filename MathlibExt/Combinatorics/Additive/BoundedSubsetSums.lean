/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

/-!
# Subset and subsequence sums with bounded numbers of terms

For a finite set containing zero, a subset sum with a bounded number of terms can be written
as a generalized sum with a fixed number of terms by padding with zeros.
-/

namespace MetaMathlibExt

@[expose] public section

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
public theorem generalizedHFoldSumset_comp_perm {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {k : ℕ} (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) (π : Equiv.Perm (Fin k)) :
    generalizedHFoldSumset (a ∘ π) (r ∘ π) h = generalizedHFoldSumset a r h := by
  ext x
  simp only [generalizedHFoldSumset, Finset.mem_image, Finset.mem_filter,
    Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨s, ⟨hs, htotal⟩, hsum⟩
    refine ⟨s ∘ π.symm, ⟨?_, (Equiv.sum_comp π.symm s).trans htotal⟩, ?_⟩
    · intro i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hs (π.symm i)
    · have hreindex := Equiv.sum_comp π.symm (fun i => s i • a (π i))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hreindex.trans hsum
  · rintro ⟨s, ⟨hs, htotal⟩, hsum⟩
    exact ⟨s ∘ π, ⟨fun i => hs (π i), (Equiv.sum_comp π s).trans htotal⟩,
      (Equiv.sum_comp π (fun i => s i • a i)).trans hsum⟩

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
public theorem boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hα : 1 ≤ α) (hβ : β ≤ m)
    (hαβ : α + β ≤ m + 1) :
    boundedSubsetSums α β (Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → G)) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (m + 1 - α - β + 1) fun _ => 1 : Fin (m + 1) → ℕ) (m + 1 - β) := by
  have hA : Finset.univ.image (Fin.cons 0 b : Fin (m + 1) → G) =
      insert 0 (Finset.univ.image b) := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  have hzero : 0 ∉ Finset.univ.image b := by simpa using hb0
  have hcard : (insert 0 (Finset.univ.image b)).card = m + 1 := by
    simp [Finset.card_insert_of_notMem hzero, Finset.card_image_of_injective _ hb]
  ext x
  simp only [hA, boundedSubsetSums, Finset.mem_biUnion, Finset.mem_Icc, hcard,
    restrictedSumset, Finset.mem_image, Finset.mem_powersetCard, generalizedHFoldSumset,
    Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨n, ⟨hnlo, hnhi⟩, B, ⟨hB, hBn⟩, rfl⟩
    obtain ⟨T, hT⟩ := Finset.subset_univ_image_iff.mp (Finset.subset_insert_iff.mp hB)
    have hTcard : T.card = (B.erase 0).card := by
      rw [← hT, Finset.card_image_of_injective _ hb]
    have hlo := Finset.pred_card_le_card_erase (s := B) (a := 0)
    have hhi := Finset.card_erase_le (s := B) (a := 0)
    -- Pad the indicator of the nonzero terms to the prescribed length.
    refine ⟨Fin.cons (m + 1 - β - T.card) (fun i => if i ∈ T then 1 else 0), ⟨?_, ?_⟩, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        omega
      · by_cases hj : j ∈ T <;> simp [hj]
    · simp [Fin.sum_univ_succ]
      omega
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, nsmul_zero, zero_add,
        ite_smul, one_nsmul, zero_nsmul, Fintype.sum_ite_mem]
      rw [← Finset.sum_image hb.injOn (f := fun a => a), hT]
      exact Finset.sum_erase B (f := fun a => a) rfl
  · rintro ⟨s, ⟨hs, htotal⟩, rfl⟩
    let T := Finset.univ.filter fun i : Fin m => s i.succ = 1
    have hcoeff (i : Fin m) : s i.succ = if i ∈ T then 1 else 0 := by
      have hi : s i.succ ≤ 1 := by simpa using hs i.succ
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      split <;> omega
    have hlen : s 0 + T.card = m + 1 - β := by
      simpa [Fin.sum_univ_succ, hcoeff] using htotal
    have hcap : s 0 ≤ m + 1 - α - β + 1 := by simpa using hs 0
    have hsum : ∑ i, s i • (Fin.cons 0 b : Fin (m + 1) → G) i = ∑ a ∈ T.image b, a := by
      simp [Fin.sum_univ_succ, hcoeff, ite_smul, one_nsmul, Finset.sum_image hb.injOn]
    rw [hsum]
    have hTcard := Finset.card_image_of_injective T hb
    have hTsub : T.image b ⊆ Finset.univ.image b := Finset.image_subset_image (Finset.subset_univ T)
    -- Keep one zero exactly when the nonzero terms alone fall short of the lower bound.
    by_cases hmin : α ≤ T.card
    · exact ⟨T.card, ⟨hmin, by omega⟩, T.image b,
        ⟨hTsub.trans (Finset.subset_insert ..), hTcard⟩, rfl⟩
    · have hz : 0 ∉ T.image b := fun hz => hzero (hTsub hz)
      refine ⟨T.card + 1, ⟨by omega, by omega⟩, insert 0 (T.image b),
        ⟨Finset.insert_subset_insert _ hTsub, ?_⟩, ?_⟩
      · rw [Finset.card_insert_of_notMem hz, hTcard]
      · simp [hz]

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
public theorem boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_not_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (b : Fin k → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (α β : ℕ) (hαβ : α + β + 1 ≤ k) :
    boundedSubsetSums α β (Finset.univ.image b) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (k + 1) → G)
        (Fin.cons (k - α - β) fun _ => 1 : Fin (k + 1) → ℕ) (k - β) := by
  have hA : Finset.univ.image (Fin.cons 0 b : Fin (k + 1) → G) =
      insert 0 (Finset.univ.image b) := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  have hzero : 0 ∉ Finset.univ.image b := by simpa using hb0
  have hcard : (Finset.univ.image b).card = k := by
    simp [Finset.card_image_of_injective _ hb]
  have hcardInsert : (insert 0 (Finset.univ.image b)).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hzero, hcard]
  -- Adjoining zero raises the lower size bound by one without changing the upper bound.
  have hpad : boundedSubsetSums α β (Finset.univ.image b) =
      boundedSubsetSums (α + 1) (β + 1) (insert 0 (Finset.univ.image b)) := by
    ext x
    simp only [boundedSubsetSums, Finset.mem_biUnion, Finset.mem_Icc, restrictedSumset,
      Finset.mem_image, Finset.mem_powersetCard, hcard, hcardInsert]
    constructor
    · rintro ⟨n, ⟨hlo, hhi⟩, S, ⟨hS, hScard⟩, rfl⟩
      by_cases h : α + 1 ≤ n
      · exact ⟨n, ⟨h, by omega⟩, S, ⟨hS.trans (Finset.subset_insert ..), hScard⟩, rfl⟩
      · have hz : 0 ∉ S := fun hz => hzero (hS hz)
        refine ⟨n + 1, ⟨by omega, by omega⟩, insert 0 S,
          ⟨Finset.insert_subset_insert _ hS, ?_⟩, ?_⟩
        · rw [Finset.card_insert_of_notMem hz, hScard]
        · simp [hz]
    · rintro ⟨n, ⟨hlo, hhi⟩, S, ⟨hS, hScard⟩, rfl⟩
      have hlower := Finset.pred_card_le_card_erase (s := S) (a := 0)
      have hupper := Finset.card_erase_le (s := S) (a := 0)
      exact ⟨(S.erase 0).card, ⟨by omega, by omega⟩, S.erase 0,
        ⟨Finset.subset_insert_iff.mp hS, rfl⟩, Finset.sum_erase S (f := fun a => a) rfl⟩
  rw [hpad, ← hA]
  have h := boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_mem b hb hb0
    (α + 1) (β + 1) (by omega) (by omega) (by omega)
  rwa [show k + 1 - (α + 1) - (β + 1) + 1 = k - α - β by omega,
    show k + 1 - (β + 1) = k - β by omega] at h

end

end MetaMathlibExt
