/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProducts

open MathlibExt.Combinatorics.Enumerative.Partition.MultisetReconstructionPairwiseProductsWanted

-- Equal parts at different positions contribute separate products in Li's example.
example : pairwiseProducts {4, 2, 1, 1} = {8, 4, 4, 2, 2, 1} := by decide

-- The unique partition of a positive total with no pairwise products has just one part.
example {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) :
    pairwiseProducts p.parts = 0 ↔ p = Nat.Partition.indiscrete n := by
  simpa [Nat.Partition.indiscrete_parts hn.ne', pairwiseProducts,
    Multiset.powersetCard_eq_empty] using
    partition_pairwiseProducts_eq_iff hn p (Nat.Partition.indiscrete n)
