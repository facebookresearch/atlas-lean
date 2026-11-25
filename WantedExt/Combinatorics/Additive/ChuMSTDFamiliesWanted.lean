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
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies

namespace MetaMathlibExt

@[expose] public section

open Pointwise

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

end

end MetaMathlibExt
