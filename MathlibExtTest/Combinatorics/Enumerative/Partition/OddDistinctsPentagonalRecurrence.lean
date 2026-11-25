/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.OddDistinctsPentagonalRecurrence

open MetaMathlibExt

-- At `n = 1` only `k = 0` contributes, and `1 = m(3m+1)/2` for `m = -1` with sign `+1`.
example : (Nat.Partition.oddDistincts 1).card = 1 := by
  have h := oddDistincts_pentagonal_recurrence 1
  rw [show ((Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ)).filter
      fun k : ℤ => k * (3 * k + 1) ≤ ((1 : ℕ) : ℤ)) = {0} by decide,
    show (∑ m ∈ Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ),
      if m * (3 * m + 1) / 2 = ((1 : ℕ) : ℤ) then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0) = 1
      by decide] at h
  simpa using h

-- At `n = 2` the terms `k = 0, -1` contribute, and `2 = m(3m+1)/2` for `m = 1` with sign `-1`.
example : (Nat.Partition.oddDistincts 2).card + 1 = (Nat.Partition.oddDistincts 0).card := by
  have h := oddDistincts_pentagonal_recurrence 2
  rw [show ((Finset.Icc (-((2 : ℕ) : ℤ)) (2 : ℕ)).filter
      fun k : ℤ => k * (3 * k + 1) ≤ ((2 : ℕ) : ℤ)) = {-1, 0} by decide,
    show (∑ m ∈ Finset.Icc (-((2 : ℕ) : ℤ)) (2 : ℕ),
      if m * (3 * m + 1) / 2 = ((2 : ℕ) : ℤ) then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0) = -1
      by decide] at h
  simp at h
  omega

-- `3` is not of the form `m(3m+1)/2`, so the alternating sum vanishes: `pdo(3) = pdo(1)`.
example : (Nat.Partition.oddDistincts 3).card = (Nat.Partition.oddDistincts 1).card := by
  have h := oddDistincts_pentagonal_recurrence 3
  rw [show ((Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)).filter
      fun k : ℤ => k * (3 * k + 1) ≤ ((3 : ℕ) : ℤ)) = {-1, 0} by decide,
    show (∑ m ∈ Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ),
      if m * (3 * m + 1) / 2 = ((3 : ℕ) : ℤ) then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0) = 0
      by decide] at h
  simp at h
  omega
