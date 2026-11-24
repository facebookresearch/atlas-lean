/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiset reconstruction from pairwise products and total sum

Statements from Stella Jiahui Li, "A Note on Multiset Reconstruction
from Pairwise Products and Total Sum", *INTEGERS* 26 (2026),
Article A16 (<https://math.colgate.edu/~integers/aa16/aa16.pdf>).

The paper's `pre₂ λ` is the partition whose parts are the products
`λᵢ λⱼ` over `i < j`.  Here that operation is recorded directly as a
multiset of natural numbers.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Powerset

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProductsWanted

/-- **Pairwise products of a multiset.** If a multiset $s$ of natural numbers consists of
$x_1, \dots, x_k$, listed with multiplicity, then the pairwise products of $s$ form the multiset
of the products $x_i x_j$ over all pairs of indices $1 \le i < j \le k$; equal elements at
different positions give separate products, and the result is empty when $k < 2$.

Applied to the parts of a partition $\lambda$, this gives the parts of the partition
$\mathrm{pre}_2(\lambda)$ of Li's note on multiset reconstruction. -/
def pairwiseProducts (s : Multiset ℕ) : Multiset ℕ :=
  (s.powersetCard 2).map Multiset.prod

/-- **Li's lemma: reconstruction from the largest part and pairwise products.** Let $n$ be a
positive integer and let $\lambda$ and $\mu$ be partitions of $n$ with a common largest part,
that is, some $a$ is a part of both $\lambda$ and $\mu$ and no part of either exceeds $a$. If the
pairwise products of the parts of $\lambda$ and the pairwise products of the parts of $\mu$ form
the same multiset, then $\lambda = \mu$.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Lemma 1. -/
theorem_wanted partition_eq_of_pairwiseProducts_eq_of_max_eq
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n)
    (hmax : ∃ a : ℕ, a ∈ lam.parts ∧ a ∈ mu.parts ∧
      (∀ x ∈ lam.parts, x ≤ a) ∧ (∀ x ∈ mu.parts, x ≤ a))
    (hpre : pairwiseProducts lam.parts = pairwiseProducts mu.parts) :
    lam = mu

/-- **Li's theorem: partitions are determined by their pairwise products.** Let $n$ be a positive
integer and let $\lambda$ and $\mu$ be partitions of $n$. The pairwise products of the parts of
$\lambda$ and the pairwise products of the parts of $\mu$ form the same multiset if and only if
$\lambda = \mu$.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Theorem 1. -/
theorem_wanted partition_pairwiseProducts_eq_iff
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n) :
    pairwiseProducts lam.parts = pairwiseProducts mu.parts ↔ lam = mu

end MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProductsWanted
