/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProducts

open MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProductsWanted

example : pairwiseProducts 0 = 0 := rfl

example (a : ℕ) : pairwiseProducts {a} = 0 := rfl

-- Equal parts at different positions contribute separate products in Li's example.
example : pairwiseProducts {4, 2, 1, 1} = {8, 4, 4, 2, 2, 1} := by decide

-- The unique partition of a positive total with no pairwise products has just one part.
example {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) :
    pairwiseProducts p.parts = 0 ↔ p = Nat.Partition.indiscrete n := by
  simpa [Nat.Partition.indiscrete_parts hn.ne', pairwiseProducts,
    Multiset.powersetCard_eq_empty] using
    partition_pairwiseProducts_eq_iff hn p (Nat.Partition.indiscrete n)

-- Reconstruct a partition with a repeated largest part from its numerical data.
example (p : Nat.Partition 10) (hmem : 4 ∈ p.parts) (hle : ∀ x ∈ p.parts, x ≤ 4)
    (hprod : pairwiseProducts p.parts = {16, 8, 8}) :
    p.parts = {4, 4, 2} := by
  let q : Nat.Partition 10 := ⟨{4, 4, 2}, by decide, by decide⟩
  have heq : p = q :=
    partition_eq_of_pairwiseProducts_eq_of_max_eq (by decide) p q
      ⟨4, hmem, by decide, hle, by decide⟩ (hprod.trans (by decide))
  exact congrArg Nat.Partition.parts heq
