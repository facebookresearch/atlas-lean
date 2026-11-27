/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import MathlibExt.Combinatorics.Enumerative.StableMatchingDisjointProfiles

/-! # Tests for counting disjoint stable-matching preference profiles -/

namespace MathlibExtTest.Combinatorics.Enumerative.StableMatchingDisjointProfiles

open MetaMathlibExt.StableMatchingSequences

private abbrev DisjointProfile (n : ℕ) :=
  {P : PreferenceProfile n // Function.Bijective fun ij : Fin n × Fin n =>
    ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)}

-- These cardinalities are computed by enumerating the preference lists.
example : Nat.card (DisjointProfile 0) = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

example : Nat.card (DisjointProfile 2) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

-- At size two, the upper bound and the divisor are both nontrivial.
example : Nat.card (DisjointProfile 2) ≤ 24 ∧ 4 ∣ Nat.card (DisjointProfile 2) :=
  disjoint_profiles_card_le_and_dvd 2

end MathlibExtTest.Combinatorics.Enumerative.StableMatchingDisjointProfiles
