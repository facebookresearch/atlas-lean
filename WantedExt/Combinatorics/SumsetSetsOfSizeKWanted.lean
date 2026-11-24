/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Torsion
public import MathlibExt.Combinatorics.SumsetSetsOfSizeK

/-!
# The sumset of sets of size `k`

Statements from Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26
(2026), Article A31.

The definitions of `R_G(h, k)` and of the trivial elements of `hA` are taken from the
arXiv version of the paper (arXiv:2505.07679v2, Section 1, Notation before
Definition 1.8 and Definition 1.8).  Throughout, `R_G(h, k)` is written out as the set
of cardinalities `(h • A).card` of `k`-element finsets `A`, and a `k`-element set
`a 0 < a 1 < ⋯ < a (k - 1)` is given by a function `a : ℕ → G` restricted to
`Finset.range k`.
-/

open scoped Pointwise

namespace MetaMathlibExt

@[expose] public section

/-- **Many nontrivial sums when the last gap is not a multiple of the previous one.** Let $G$ be
a linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-3}$. Suppose that
$a_{k-2} = a_{k-3} + b$ and $a_{k-1} = a_{k-3} + b + c$, where $b, c \in G$ satisfy $b > 0$,
$c > 0$ and $c \ne db$ for every integer $d \ge 1$. Then at least $h - 1$ elements of the
$h$-fold sumset $h\{a_0, \ldots, a_{k-1}\}$ (the set of sums of $h$ elements of
$\{a_0, \ldots, a_{k-1}\}$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-1}$.

The paper takes $h > 1$; the bound is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 1 (`integers-2026-A31-thm-1`; arXiv:2505.07679v2,
Theorem 3.3). -/
public theorem_wanted nontrivial_sumset_card_of_last_gap_ne_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b c : G) (hb : 0 < b) (hc : 0 < c)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + c)
    (hcb : ∀ d : ℕ, 1 ≤ d → c ≠ d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card

/-- **Equal last two gaps: an arithmetic progression or many nontrivial sums.** Let $G$ be a
linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-1}$ and
$a_{k-1} - a_{k-2} = a_{k-2} - a_{k-3}$. Then either $a_i = i a_1$ for every $i < k$, or at
least $h - 1$ elements of the $h$-fold sumset $hB$ of $B = \{a_0, \ldots, a_{k-2}\}$ (the set
of sums of $h$ elements of $B$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-2}$.

The gap hypothesis is the paper's $b_{k-2} = b_{k-3}$, where $b_j = a_{j+1} - a_j$ for
$j \ge 1$. The paper takes $h > 1$; the second alternative is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 3 (`integers-2026-A31-thm-3`; arXiv:2505.07679v2,
Theorem 3.5). -/
public theorem_wanted arithProg_or_nontrivial_sumset_card_of_last_gaps_eq
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 < k → a i < a (i + 1))
    (hgap : a (k - 1) - a (k - 2) = a (k - 2) - a (k - 3)) :
    (∀ i < k, a i = i • a 1) ∨
      h - 1 ≤ (h • (Finset.range (k - 1)).image a \
        sumsetTrivialElements h (k - 1) a).card

/-- **A gap in the possible sumset sizes.** Let $G$ be a torsion-free additive commutative
group and let $h$ and $k \ge 4$ be natural numbers. For every $k$-element set $A \subseteq G$,
the $h$-fold sumset $hA$ (the set of sums of $h$ elements of $A$) does not satisfy
$hk - h + 2 \le |hA| \le hk - 1$.

Equivalently, writing $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets
$A \subseteq G$, $R_G(h, k) \cap [hk - h + 2, hk - 1] = \emptyset$. The interval is empty for
$h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 4 (`integers-2026-A31-thm-4`; arXiv:2505.07679v2,
Theorem 3.6). -/
public theorem_wanted card_nsmul_notMem_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉ Set.Icc (h * k - h + 2) (h * k - 1)

/-- **Sumset sizes between $hk - h + 1$ and $hk$.** Let $G$ be a nontrivial torsion-free
additive commutative group and let $h \ge 1$ and $k \ge 4$ be natural numbers. For a finite
set $A \subseteq G$ write $hA$ for its $h$-fold sumset, the set of sums of $h$ elements of $A$,
and write $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets $A \subseteq G$. Then
$R_G(h, k) \cap [hk - h + 1, hk] = \{hk - h + 1, hk\}$.

The hypotheses that $G$ is nontrivial (otherwise there is no $k$-element set and
$R_G(h, k)$ is empty) and that $h \ge 1$ (for $h = 0$ the interval $[1, 0]$ is empty while
the right side is $\{1, 0\}$) are added. The arXiv version states only $hk \in R_G(h, k)$
(Corollary 3.8); the rest combines Theorem 4 with the arithmetic-progression size
$hk - h + 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Corollary 1 (`integers-2026-A31-cor-1`). -/
public theorem_wanted sumsetSizes_inter_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [Nontrivial G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (hh : 1 ≤ h) :
    {n : ℕ | ∃ A : Finset G, A.card = k ∧ (h • A).card = n} ∩
        Set.Icc (h * k - h + 1) (h * k) = {h * k - h + 1, h * k}

/-- **Rajagopal's family of missing sumset sizes.** Let $G$ be a torsion-free additive
commutative group and let $h$, $k$ and $\ell$ be natural numbers with $\ell + 3 \le \min(h, k)$.
For every $k$-element set $A \subseteq G$, the $h$-fold sumset $hA$ (the set of sums of $h$
elements of $A$) does not satisfy
$hk - h + 2 + \ell h \le |hA| \le hk - h + 1 + \ell h + (h - 2 - \ell)$.

Equivalently, writing $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets
$A \subseteq G$, $R_G(h, k)$ misses the interval
$[hk - h + 2 + \ell h, hk - h + 1 + \ell h + (h - 2 - \ell)]$ for each
$0 \le \ell \le \min(h, k) - 3$, stated here one $\ell$ at a time. The journal statement does
not name the group; torsion-freeness is the setting of Theorem 4 and Corollary 1, which this
generalizes ($\ell = 0$ is Theorem 4, here also for $k = 3$).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 6 (`integers-2026-A31-thm-6`, journal version; credited to Rajagopal,
Theorem 1.3). -/
public theorem_wanted card_nsmul_notMem_Icc_add_mul_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k ℓ : ℕ) (hℓ : ℓ + 3 ≤ min h k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉
      Set.Icc (h * k - h + 1 + ℓ * h + 1) (h * k - h + 1 + ℓ * h + (h - 2 - ℓ))

end

end MetaMathlibExt
