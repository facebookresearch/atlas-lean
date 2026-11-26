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
