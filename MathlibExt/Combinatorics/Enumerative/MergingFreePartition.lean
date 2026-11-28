/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Merging-free partitions.** Let $n$ be a natural number. A finite sequence
$(B_1, \dots, B_m)$ of subsets of $\{0, 1, \dots, n-1\}$ is a merging-free partition when the
sets $B_i$ are nonempty, pairwise disjoint and cover $\{0, 1, \dots, n-1\}$; their minima increase
strictly, $\min B_1 < \min B_2 < \dots < \min B_m$; and $\max B_i > \min B_{i+1}$ for every
$i < m$.

Source: concept `jis_sem_b7c50ba5c98632f7e1692f88`, source `jis_source_6a539d4a69c1cba832a9f1a4`,
statement `jis_a73f3b4e90f7919cc07e8594`, slash-ordered block representation. -/
def IsMergingFreePartition (n : ℕ) (P : List (Finset (Fin n))) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
    P.Pairwise (fun B C => B ∩ C = ∅) ∧
    (∀ x, ∃ B ∈ P, x ∈ B) ∧
    P.Pairwise (fun B C =>
      ∃ mB ∈ B, ∃ mC ∈ C,
        (∀ b ∈ B, mB ≤ b) ∧ (∀ c ∈ C, mC ≤ c) ∧ mB < mC) ∧
    P.IsChain (fun B C =>
      ∃ mC ∈ C, ∃ mB ∈ B,
        (∀ c ∈ C, mC ≤ c) ∧ (∀ b ∈ B, b ≤ mB) ∧ mC < mB)

end

end MetaMathlibExt
