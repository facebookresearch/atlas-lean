/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Set.Card

/-!
# Colored partitions and Euler-type identities (statements)

Statement-only targets from Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and
Euler-Type Identities*, INTEGERS 26 (2026), Article A20.

A colored part `m_j` (size `m`, color `j`, `1 ≤ j ≤ m`) is the pair `(m, j) : ℕ × ℕ`. A colored
partition with distinct colors (or with fully different parts) has no repeated colored part,
so it is a finset of colored parts; a general colored partition is a multiset. A composition is
a list of positive integers; a part of size `k` colored by a composition is a pair
`(k, c) : ℕ × List ℕ`. A partition of a multiset into blocks is a multiset of nonempty
multisets whose sum (`Multiset.join`) is the multiset; a block is constant when it is
`Multiset.replicate c x`. Counts of infinite carrier types use `Set.ncard`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Colored partitions with distinct colors.** A colored part is a pair $(m, j)$ of integers
with $1 \le j \le m$, read as the part $m$ in color $j$. For every $n \ge 0$, the number of
nonempty finite sets of colored parts $(m, j)$ with $m \le n$ in which no two colored parts have
the same color $j$ is $(n + 1)! - 1$.

A colored partition whose parts have pairwise different colors has no repeated colored part, so
it is the same as a finite set of colored parts; the empty partition is not counted.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 1 (`integers-2026-A20-thm-1`). -/
public theorem_wanted card_coloredPartitions_differentColors (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.snd).card = T.card)).card = (n + 1).factorial - 1

/-- **Formula for colored partitions into fully different parts.** A colored part is a pair
$(m, j)$ of integers with $1 \le j \le m$, read as the part $m$ in color $j$. For $n \ge 0$, let
$\mathrm{pf}_c(n)$ be the number of finite sets of colored parts whose sizes $m$ sum to $n$ and
in which no two colored parts have the same size and no two have the same color. Then
$\mathrm{pf}_c(n)$ is the sum, over all partitions of $n$ into distinct parts
$p_1 > p_2 > \cdots > p_k$, of the product $p_k (p_{k-1} - 1) \cdots (p_1 - (k - 1))$.

The identity is stated for all $n \ge 0$; at $n = 0$ both sides equal $1$, while the paper states
it for $n \ge 1$.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 2 (`integers-2026-A20-thm-2`). -/
public theorem_wanted card_coloredPartitions_fullyDifferent (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => ∑ x ∈ T, x.1 = n ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card =
      ∑ μ ∈ Nat.Partition.distincts n,
        ((μ.parts.sort (· ≤ ·)).mapIdx fun i q => q - i).prod

/-- **Colored partitions into fully different parts with bounded size.** A colored part is a pair
$(m, j)$ of integers with $1 \le j \le m$, read as the part $m$ in color $j$. For every $n \ge 0$,
the number of nonempty finite sets of colored parts $(m, j)$ with $m \le n$ in which no two
colored parts have the same size $m$ and no two have the same color $j$ is $B_{n+1} - 1$, where
$B_k$ denotes the $k$-th Bell number.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 3 (`integers-2026-A20-thm-3`). -/
public theorem_wanted card_coloredPartitions_fullyDifferent_le (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card = Nat.bell (n + 1) - 1

/-- **Constant-block partitions and double compositions.** For $n \ge 0$, count the pairs
$(A, P)$ where $A$ is a multiset of $n$ positive integers whose distinct elements are exactly
$1, \dots, k$ for some $k \ge 0$, and $P$ is a partition of $A$ into constant blocks, that is,
a multiset of nonempty multisets, each with all its elements equal, whose sum is $A$. The number
of such pairs equals the number $d_c(n)$ of double compositions of $n$, that is, compositions of
$n$ in which each summand $m$ is colored by a partition of $m$:
$$d_c(n) = \sum_{(c_1, \dots, c_r)} p(c_1) \cdots p(c_r),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ and $p(m)$ is the number of
partitions of $m$.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 4 (`integers-2026-A20-thm-4`). -/
public theorem_wanted ncard_constantBlockPartitions_eq_doubleCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = n ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => Fintype.card (Nat.Partition m)).prod

/-- **Distinct constant-block partitions and colored compositions.** For $n \ge 0$, count the
pairs $(A, P)$ where $A$ is a multiset of $n$ positive integers whose distinct elements are
exactly $1, \dots, k$ for some $k \ge 0$, and $P$ is a partition of $A$ into pairwise distinct
constant blocks, that is, a multiset of pairwise distinct nonempty multisets, each with all its
elements equal, whose sum is $A$. The number of such pairs equals the number of compositions of
$n$ in which each summand $m$ is colored by a partition of $m$ into distinct parts:
$$\sum_{(c_1, \dots, c_r)} q(c_1) \cdots q(c_r),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ and $q(m)$ is the number of
partitions of $m$ into distinct parts.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 1 (`integers-2026-A20-cor-1`). -/
public theorem_wanted ncard_distinctConstantBlockPartitions_eq_coloredCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = n ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => (Nat.Partition.distincts m).card).prod

/-- **Generalized Euler partition theorem.** Let $S$ be a set of compositions (finite sequences
of positive integers) such that doubling every summand of a member of $S$ gives a member of $S$,
and halving every summand of a member of $S$ whose summands are all even gives a member of $S$.
Let $n \ge 0$. The number of partitions of $n$ into colored parts in which each part $k$ is
colored by a composition in $S$ with sum $k$, and no colored part (a pair of part and color)
appears twice, equals the number of such partitions of $n$, with repetition allowed, in which no
even part is colored by a composition whose summands are all even. The same holds when each part
$k$ is colored by a composition in $S$ with sum at most $k$.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 5 (`integers-2026-A20-thm-5`). -/
public theorem_wanted generalized_euler_partition_theorem (S : Set (List ℕ))
    (hS : ∀ c ∈ S, ∀ x ∈ c, 0 < x) (hdouble : ∀ c ∈ S, c.map (2 * ·) ∈ S)
    (hhalf : ∀ c ∈ S, (∀ x ∈ c, Even x) → c.map (· / 2) ∈ S) (n : ℕ) :
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum = x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum = x.1 ∧
        (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧ (M.map Prod.fst).sum = n}.ncard ∧
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum ≤ x.1 ∧
        (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧ (M.map Prod.fst).sum = n}.ncard

/-- **Euler partition theorem for restricted compositions.** A composition (a finite sequence of
positive integers) is $\ell$-restricted if it has at most $\ell$ summands. Let $\ell \ge 0$ and
$n \ge 0$. The number of partitions of $n$ into colored parts in which each part $k$ is colored
by an $\ell$-restricted composition of $k$, and no colored part (a pair of part and color)
appears twice, equals the number of such partitions of $n$, with repetition allowed, in which no
even part is colored by a composition whose summands are all even.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 3 (`integers-2026-A20-cor-3`). -/
public theorem_wanted euler_partition_theorem_restrictedCompositions (ℓ n : ℕ) :
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ (∀ y ∈ x.2, 0 < y) ∧
        x.2.length ≤ ℓ ∧ x.2.sum = x.1) ∧ (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ (∀ y ∈ x.2, 0 < y) ∧
        x.2.length ≤ ℓ ∧ x.2.sum = x.1 ∧ (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧
        (M.map Prod.fst).sum = n}.ncard

/-- **Colored partitions with different parts.** A colored part is a pair $(m, j)$ of integers
with $1 \le j \le m$, read as the part $m$ in color $j$, and a colored partition of $n$ is a
finite multiset of colored parts whose sizes $m$ sum to $n$. For every $n \ge 0$, the number of
colored partitions of $n$ in which no colored part is repeated equals the number of colored
partitions of $n$ in which no even part has an even color, and it also equals the number of
colored partitions of $n$ in which no even part has an odd color.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 4 (`integers-2026-A20-cor-4`). -/
public theorem_wanted coloredPartitions_differentParts_eq_restrictedColors (n : ℕ) :
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → ¬ Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard ∧
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard

end

end MetaMathlibExt
