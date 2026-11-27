/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosSequenceDiscrepancy

open MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted

-- The closed singleton interval counts repeated fractional parts with multiplicity.
example (x : ℕ → ℤ) (N : ℕ) : CountQ x 0 N 0 0 = N := by
  simp [CountQ]

-- A nonzero rational endpoint is included even when the interval has width zero.
example (N : ℕ) : CountQ (fun _ => 1) (1 / 2) N (1 / 2) (1 / 2) = N := by
  norm_num [CountQ]

-- Every admissible interval has zero error for the empty prefix.
example (x : ℕ → ℤ) (α : ℝ) : discrep x α 0 = 0 := by
  unfold discrep
  convert csSup_singleton (0 : ℝ) using 1
  congr 1
  ext d
  constructor
  · rintro ⟨p, q, _, _, _, rfl⟩
    simp [CountQ]
  · rintro (rfl : d = 0)
    exact ⟨0, 0, by simp [CountQ]⟩

example (h : conjecture) : False := conjecture_refuted h
