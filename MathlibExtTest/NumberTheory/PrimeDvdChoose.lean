/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeDvdChoose
import Mathlib.Order.Interval.Finset.Nat

/-- Arbitrarily large rows have an even middle entry. The lower bound makes the entry interior. -/
example (N : ℕ) : ∃ n > N + 1, Even (n.choose (n / 2)) := by
  obtain ⟨n, hn, hN⟩ := (MetaMathlibExt.infinite_setOf_prime_dvd_choose Nat.prime_two).exists_gt
    (N + 1)
  exact ⟨n, hN, even_iff_two_dvd.mpr (hn (n / 2) (by omega) (by omega))⟩
