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

/-- The multiset of pairwise products of elements of a multiset of
natural numbers: one product for each two-element submultiset. This
is the parts multiset of the paper's `pre₂`. -/
def pairwiseProducts (s : Multiset ℕ) : Multiset ℕ :=
  (s.powersetCard 2).map Multiset.prod

/-- Li's Lemma 1: partitions of the same positive integer with the
same largest part and the same pairwise-product multiset are equal.

The common largest part `λ₁ = μ₁` is expressed by a common element
maximal in both parts multisets.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Lemma 1. -/
theorem_wanted partition_eq_of_pairwiseProducts_eq_of_max_eq
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n)
    (hmax : ∃ a : ℕ, a ∈ lam.parts ∧ a ∈ mu.parts ∧
      (∀ x ∈ lam.parts, x ≤ a) ∧ (∀ x ∈ mu.parts, x ≤ a))
    (hpre : pairwiseProducts lam.parts = pairwiseProducts mu.parts) :
    lam = mu

/-- Li's Theorem 1: for partitions of the same positive integer,
equality of the pairwise-product multisets is equivalent to equality
of the partitions.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Theorem 1. -/
theorem_wanted partition_pairwiseProducts_eq_iff
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n) :
    pairwiseProducts lam.parts = pairwiseProducts mu.parts ↔ lam = mu

end MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProductsWanted
