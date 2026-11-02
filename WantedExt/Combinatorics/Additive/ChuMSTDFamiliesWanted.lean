/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chu et al.'s families of MSTD sets

Statements from Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a
New Family of MSTD Sets*, INTEGERS 24 (2024), Article A32.

Sets are written by their sequence of consecutive differences (Spohn's notation, Theorem 5's
notation paragraph): `(a₁ | g₁, …, g_r)` is `{a₁, a₁ + g₁, a₁ + g₁ + g₂, …}`, and
`M^k` is the difference sequence `1, 4, …, 4, 3` with `k` fours. A set `A` is MSTD
(sum-dominated) when `|A + A| > |A - A|`, balanced when `|A + A| = |A - A|`, and
difference-dominated when `|A + A| < |A - A|`; a family has one of these properties when
every member has it.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-- **Sets given by consecutive differences.** For an integer $a$ and natural numbers
$g_1, \dots, g_r$, the set $(a \mid g_1, \dots, g_r)$ is the finite set of integers
$\{a, a + g_1, a + g_1 + g_2, \dots, a + g_1 + \dots + g_r\}$; for $r = 0$ it is $\{a\}$.

When every $g_i$ is positive, the differences between consecutive elements of this set, listed
from the smallest element to the largest, are $g_1, \dots, g_r$; a zero gap repeats a partial
sum, which the set records once.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public def setOfConsecutiveDifferences : ℤ → List ℕ → Finset ℤ
  | a, [] => {a}
  | a, g :: l => insert a (setOfConsecutiveDifferences (a + g) l)

/-- **Prepending a gap.** For an integer $a$ and natural numbers $g_1, \dots, g_r$ ($r \ge 0$),
write $(a \mid g_1, \dots, g_r)$ for the set of partial sums
$\{a, a + g_1, \dots, a + g_1 + \dots + g_r\}$. Then for every natural number $g$,
$(a \mid g, g_1, \dots, g_r) = \{a\} \cup (a + g \mid g_1, \dots, g_r)$.

When $g > 0$, the new element $a$ is smaller than every element of $(a + g \mid g_1, \dots, g_r)$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_cons (a : ℤ) (g : ℕ) (l : List ℕ) :
    setOfConsecutiveDifferences a (g :: l) = insert a (setOfConsecutiveDifferences (a + g) l) :=
  rfl

/-- **An example of difference notation.** The set with least element $0$ and consecutive
differences $1, 5, 1, 1, 9, 7$ is $(0 \mid 1, 5, 1, 1, 9, 7) = \{0, 1, 6, 7, 8, 17, 24\}$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_example :
    setOfConsecutiveDifferences 0 [1, 5, 1, 1, 9, 7] = {0, 1, 6, 7, 8, 17, 24} := by
  decide

/-- **Chu difference block.** For a natural number $k$, the difference block $M^k$ is the list of
natural numbers $1, 4, \ldots, 4, 3$ of length $k + 2$: a $1$, then $k$ copies of $4$, then a $3$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public def chuBlock (k : ℕ) : List ℕ :=
  1 :: List.replicate k 4 ++ [3]

/-- **The Chu difference blocks $M^1$ and $M^2$.** The Chu difference block $M^1$ is the list
$1, 4, 3$, and the Chu difference block $M^2$ is the list $1, 4, 4, 3$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public theorem chuBlock_one_two : chuBlock 1 = [1, 4, 3] ∧ chuBlock 2 = [1, 4, 4, 3] :=
  ⟨rfl, rfl⟩

/-- **A balanced family of Chu et al.** Let $k$ be a positive integer and let
$A = (0 \mid 1, 1, 2, M^k, M^{k+1}, 1, 1) \subseteq \mathbb{Z}$ be the set of partial sums,
starting at $0$, of the difference sequence formed by $1, 1, 2$, the Chu difference blocks $M^k$
and $M^{k+1}$, and $1, 1$. Then $A$ is balanced: $|A + A| = |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 1 (`integers-2024-A32-thm-1`). -/
public theorem_wanted chu_family_balanced {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card = (A - A).card

/-- **A difference-dominated family of Chu et al.** Let $k$ be a positive integer and let
$A = (0 \mid 1, 1, 2, M^k, M^{k+1}, M^{k+1}, 1, 1) \subseteq \mathbb{Z}$ be the set of partial
sums, starting at $0$, of the difference sequence formed by $1, 1, 2$, the Chu difference blocks
$M^k$, $M^{k+1}$ and $M^{k+1}$, and $1, 1$. Then $A$ is difference-dominated:
$|A + A| < |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 2 (`integers-2024-A32-thm-2`). -/
public theorem_wanted chu_family_difference_dominated {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card < (A - A).card

/-- **MSTD sets with $M^k$ before $M^{k+1}$ (Theorem 3).** Let $k$ be a positive integer, let
$M^n$ denote the block $1, 4, \dots, 4, 3$ with $n$ fours, and let $M_1$ be one of the
sequences $(1, 1, 2)$, $(1, 1, 2, 1)$. Let $A = (0 \mid 1, 1, 2, M^k, M^{k+1}, M_1)$ be the set
of partial sums, starting from $0$, of the concatenated sequence $1, 1, 2, M^k, M^{k+1}, M_1$.
Then $A$ is sum-dominated: $|A - A| < |A + A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 3 (`integers-2024-A32-thm-3`). -/
public theorem_wanted chu_family_mstd_increasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ M₁)
    (A - A).card < (A + A).card

/-- **MSTD sets with $M^{k+1}$ before $M^k$ (Theorem 4).** Let $k$ be a positive integer, let
$M^n$ denote the block $1, 4, \dots, 4, 3$ with $n$ fours, and let $M_1$ be one of the
sequences $(1, 1)$, $(1, 1, 2)$, $(1, 1, 2, 1)$. Let $A = (0 \mid 1, 1, 2, M^{k+1}, M^k, M_1)$
be the set of partial sums, starting from $0$, of the concatenated sequence
$1, 1, 2, M^{k+1}, M^k, M_1$. Then $A$ is sum-dominated: $|A - A| < |A + A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 4 (`integers-2024-A32-thm-4`). -/
public theorem_wanted chu_family_mstd_decreasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1] ∨ M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock (k + 1) ++ chuBlock k ++ M₁)
    (A - A).card < (A + A).card

/-- **Kumar–Mohan–Pandey sets.** For natural numbers $k$, $l$, $t$, let $M^n$ be the block
$1, 4, \dots, 4, 3$ with $n$ fours, and let $D$ be the sequence made of $t$ copies of the block
$1, 1, 2, M^k, \dots, M^k$ (with $l$ copies of $M^k$) followed by $1, 1, 2, 1$. The set
$A_{k,l,t}$ is $(0 \mid D)$, the set of partial sums of $D$ starting from $0$.

Each block $1, 1, 2, M^k, \dots, M^k$ has sum $4(kl + l + 1)$, matching the bounds
$t(kl + l + 1)$ in Lemmas 1-7 of the paper.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public def chuFamilyKLT (k l t : ℕ) : Finset ℤ :=
  setOfConsecutiveDifferences 0
    ((List.replicate t ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten ++
      [1, 1, 2, 1])

/-- **The Kumar–Mohan–Pandey set $A_{1,1,1}$.** For $k = l = t = 1$, the Kumar–Mohan–Pandey set
$A_{1,1,1}$, the set of partial sums starting from $0$ of the sequence
$1, 1, 2, 1, 4, 3, 1, 1, 2, 1$, is $\{0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17\}$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public theorem chuFamilyKLT_one_one_one :
    chuFamilyKLT 1 1 1 = {0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17} := by
  decide

/-- **Differences in the Kumar–Mohan–Pandey sets (Lemma 1).** Let $k$, $l$, $t$ be positive
integers, let $A = A_{k,l,t}$ be the Kumar–Mohan–Pandey set, and put $T = t(kl + l + 1)$. Then
the difference set $A - A$ contains $4i$ and $1 + 4i$ for every integer $i$ with
$1 \le i \le 1 + T$, and contains $3 + 4i$ for every integer $i$ with $0 \le i \le T$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 1 (`integers-2024-A32-lem-1`). -/
public theorem_wanted chuFamilyKLT_mem_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, 1 ≤ i → i ≤ 1 + t * (k * l + l + 1) →
        4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t ∧
          1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ t * (k * l + l + 1) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t

/-- **Positive differences of the form 6 + 4m in the Chu family set.** Let $k$, $l$, $t$ be
positive integers and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$,
$t$. Then exactly $lt + t$ elements $d$ of $A - A$ satisfy $d \ge 6$ and $d \equiv 2 \pmod 4$;
that is, exactly $lt + t$ positive differences of $A$ have the form $6 + 4m$ with $m \ge 0$ an
integer.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 3 (`integers-2024-A32-lem-3`). -/
public theorem_wanted chuFamilyKLT_card_sub_six_add_four_mul {k l t : ℕ} (hk : 0 < k)
    (hl : 0 < l) (ht : 0 < t) :
    ((chuFamilyKLT k l t - chuFamilyKLT k l t).filter
        fun d => 6 ≤ d ∧ d % 4 = 2).card = l * t + t

/-- **Elements of the Kumar–Mohan–Pandey sets (Lemma 4).** Let $k$, $l$, $t$ be positive
integers, let $A = A_{k,l,t}$ be the Kumar–Mohan–Pandey set, and put $T = t(kl + l + 1)$. Then
$1 + 4i \in A$ for every integer $i$ with $0 \le i \le 1 + T$, and $2 + 4T \in A$ and
$4 + 4T \in A$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 4 (`integers-2024-A32-lem-4`). -/
public theorem_wanted chuFamilyKLT_mem {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 1 + t * (k * l + l + 1) → 1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t) ∧
      2 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t ∧
      4 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t

/-- **Elements of the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive integers, let
$A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$, and let
$T = t(kl + l + 1)$. Then $1 + 4i$ and $2 + 4i$ lie in $A + A$ for every integer $i$ with
$0 \le i \le 2 + 2T$, and $3 + 4i$ lies in $A + A$ for every integer $i$ with $0 \le i \le 1 + 2T$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 5 (`integers-2024-A32-lem-5`). -/
public theorem_wanted chuFamilyKLT_mem_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 2 + 2 * (t * (k * l + l + 1)) →
        1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
          2 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ 1 + 2 * (t * (k * l + l + 1)) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t

/-- **Block starting points of the Chu family set.** Let $k$, $l$, $t$ be positive integers and
let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$4 + (4k + 4)i + (4kl + 4l + 4)j \in A$ for all integers $i$, $j$ with $0 \le i \le l$ and
$0 \le j \le t - 1$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 6 (`integers-2024-A32-lem-6`). -/
public theorem_wanted chuFamilyKLT_mem_block_starts {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
    4 + (4 * k + 4) * (i : ℤ) + (4 * k * l + 4 * l + 4) * (j : ℤ) ∈ chuFamilyKLT k l t

/-- **Size of the difference set of the Chu family set.** Let $k$, $l$, $t$ be positive integers
and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$|A - A| = 11 + 6klt + 8lt + 8t$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 6 (`integers-2024-A32-thm-6`). -/
public theorem_wanted chuFamilyKLT_card_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (chuFamilyKLT k l t - chuFamilyKLT k l t).card = 11 + 6 * k * l * t + 8 * l * t + 8 * t

/-- **Lower bound for the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive integers
and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$|A + A| \ge 11 + 6klt + 10lt + 8t$.

Together with $|A - A| = 11 + 6klt + 8lt + 8t$ (Theorem 6), this shows that $A$ is sum-dominated
(MSTD): $|A + A| > |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 7 (`integers-2024-A32-thm-7`). -/
public theorem_wanted chuFamilyKLT_card_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    11 + 6 * k * l * t + 10 * l * t + 8 * t ≤ (chuFamilyKLT k l t + chuFamilyKLT k l t).card

/-- **Six disjoint families in the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive
integers, let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$, and
let $P = 8kl + 8l + 8$. Let $X_1$, $X_2$, $X_4$, $X_5$ be the sets of the integers
$Pj + (4k + 4)i + 4$, $Pj + (4k + 4)i + 8$, $Pj + 4kl + 4l + (4k + 4)i + 8$ and
$Pj + 4kl + 4l + (4k + 4)i + 12$ respectively, for $1 \le i \le l$ and $0 \le j \le t - 1$, and
let $X_3$, $X_6$ be the sets of the integers $Pj + 4kl + 4l + 12$ and $Pj + 8kl + 8l + 16$
respectively, for $0 \le j \le t - 1$. Then $A + A$ contains $\{0, 4, 8\}$ and each of
$X_1, \ldots, X_6$, and the sets $X_1, \ldots, X_6$ are pairwise disjoint.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 7 (`integers-2024-A32-lem-7`). -/
public theorem_wanted chuFamilyKLT_add_supset_six_families {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) :
    let P : ℤ := 8 * k * l + 8 * l + 8
    let X₁ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 4
    let X₂ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 8
    let X₃ := (Finset.range t).image fun j : ℕ => P * j + (4 * k * l + 4 * l) + 12
    let X₄ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 8
    let X₅ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 12
    let X₆ := (Finset.range t).image fun j : ℕ => P * j + (8 * k * l + 8 * l) + 16
    {0, 4, 8} ∪ X₁ ∪ X₂ ∪ X₃ ∪ X₄ ∪ X₅ ∪ X₆ ⊆ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
      Pairwise fun a b : Fin 6 =>
        Disjoint (![X₁, X₂, X₃, X₄, X₅, X₆] a) (![X₁, X₂, X₃, X₄, X₅, X₆] b)

/-- **Two families of runs with the same sums (Proposition 1).** Let $k$, $l$, $t$ be natural
numbers, let $M^k$ be the block $1, 4, \dots, 4, 3$ with $k$ fours, and let $B$ be the
concatenation of $l$ copies of $M^k$. For $j \ge 1$ let $R_1(j)$ be the sequence $1, 1$ followed
by $j$ copies of $2, B, 1, 1$, and let $R_3(j)$ be the sequence $2$ followed by $j$ copies of
$B, 1, 1, 2$. Then the sums of the entries of $R_1(j)$ for $1 \le j \le t$ form the same set as
the sums of the entries of $R_3(j)$ for $1 \le j \le t$.

In the paper, $R_1$ and $R_3$ are runs of consecutive differences of the set of Lemma 2, so
they give the same positive differences of that set. The paper's hypothesis $k, l, t \ge 1$ is
not needed.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Proposition 1
(`integers-2024-A32-prop-1`). -/
public theorem_wanted chuFamilyKLT_run_sums_R1_eq_R3 (k l t : ℕ) :
    (Finset.Icc 1 t).image (fun j =>
        ([1, 1] ++ (List.replicate j
          (2 :: (List.replicate l (chuBlock k)).flatten ++ [1, 1])).flatten).sum) =
      (Finset.Icc 1 t).image (fun j =>
        (2 :: (List.replicate j
          ((List.replicate l (chuBlock k)).flatten ++ [1, 1, 2])).flatten).sum)

end

end MetaMathlibExt
