/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MaynardVariationalBoundsEventuallyLogSubLtMaynardM

/-!
# Tests for the growth bound for Maynard's variational quantity

The growth bound holds at an index at least `105`.

Source: J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383-413;
numbering of arXiv:1311.4600v3, Proposition 4.3(3).
-/

namespace MathlibExtTest.NumberTheory.MaynardVariationalBoundsEventuallyLogSubLtMaynardM

open MathlibExt.NumberTheory.GPYMaynard

example : ∃ k : ℕ, 105 ≤ k ∧
    Real.log k - 2 * Real.log (Real.log k) - 2 < maynardM k := by
  obtain ⟨K, hK⟩ :=
    WantedExt.NumberTheory.MaynardVariationalBounds.eventually_log_sub_lt_maynardM
  exact ⟨max K 105, le_max_right _ _, hK _ (le_max_left _ _)⟩

end MathlibExtTest.NumberTheory.MaynardVariationalBoundsEventuallyLogSubLtMaynardM
