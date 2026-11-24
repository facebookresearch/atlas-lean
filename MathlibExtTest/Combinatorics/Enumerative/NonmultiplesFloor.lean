/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NonmultiplesFloor

open MetaMathlibExt

-- At the smallest modulus the formula enumerates the positive odd numbers.
example : 7 ∈ (fun n : ℕ => (2 * n - 1) / (2 - 1)) '' {n | 1 ≤ n} := by
  rw [image_floor_eq_nonMultiples (u := 2) (hu := by decide)]
  exact (show 1 ≤ (7 : ℕ) ∧ ¬ 2 ∣ 7 by decide)

-- At modulus five the enumeration skips five and resumes at six.
example : 6 ∈ (fun n : ℕ => (5 * n - 1) / (5 - 1)) '' {n | 1 ≤ n} := by
  rw [image_floor_eq_nonMultiples (u := 5) (hu := by decide)]
  exact (show 1 ≤ (6 : ℕ) ∧ ¬ 5 ∣ 6 by decide)

example : 5 ∉ (fun n : ℕ => (5 * n - 1) / (5 - 1)) '' {n | 1 ≤ n} := by
  rw [image_floor_eq_nonMultiples (u := 5) (hu := by decide)]
  exact (show ¬ (1 ≤ (5 : ℕ) ∧ ¬ 5 ∣ 5) by decide)

-- The positive indexing keeps zero out even with truncated subtraction.
example : 0 ∉ (fun n : ℕ => (5 * n - 1) / (5 - 1)) '' {n | 1 ≤ n} := by
  rw [image_floor_eq_nonMultiples (u := 5) (hu := by decide)]
  exact (show ¬ (1 ≤ (0 : ℕ) ∧ ¬ 5 ∣ 0) by decide)
