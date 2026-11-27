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
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyDifferenceDominated
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdIncreasing
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardAdd
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardSubSixAddFourMul
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdDecreasing

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

/-- **Size of the difference set of the Chu family set.** Let $k$, $l$, $t$ be positive integers
and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$|A - A| = 11 + 6klt + 8lt + 8t$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 6 (`integers-2024-A32-thm-6`). -/
public theorem_wanted chuFamilyKLT_card_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (chuFamilyKLT k l t - chuFamilyKLT k l t).card = 11 + 6 * k * l * t + 8 * l * t + 8 * t

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
