/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.DistinctOddPartsTriangularParity

open MetaMathlibExt

private def triangularSum (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
    distinctOddPartsCount (n - k * (k + 1) / 2)

example : Even (distinctOddPartsCount 1 + distinctOddPartsCount 0) := by
  have h : Even (triangularSum 1) := distinctOddParts_triangular_sum_even 1 (by decide)
  have hindices : ((Finset.range (1 + 1)).filter (fun k => k * (k + 1) / 2 ≤ 1)) = {0, 1} :=
    by decide
  unfold triangularSum at h
  rw [hindices, Finset.sum_insert (by decide), Finset.sum_singleton] at h
  exact h

-- At `n = 4`, the triangle `3` contributes alongside `0` and `1`.
example : Even (distinctOddPartsCount 4 + (distinctOddPartsCount 3 + distinctOddPartsCount 1)) := by
  have h : Even (triangularSum 4) := distinctOddParts_triangular_sum_even 4 (by decide)
  have hindices : ((Finset.range (4 + 1)).filter (fun k => k * (k + 1) / 2 ≤ 4)) = {0, 1, 2} :=
    by decide
  unfold triangularSum at h
  rw [hindices, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h
  exact h

-- Even parts can repeat: the partition `2 + 2` is eligible at `n = 4`.
example : Nat.Partition.ofSums 4 ({2, 2} : Multiset ℕ) (by decide) ∈
    (Finset.univ : Finset (Nat.Partition 4)).filter
      (fun p => ∀ i ∈ p.parts, Odd i → p.parts.count i = 1) := by
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by decide⟩

-- The only term at zero counts the empty partition.
example : ¬ Even (triangularSum 0) := by decide
