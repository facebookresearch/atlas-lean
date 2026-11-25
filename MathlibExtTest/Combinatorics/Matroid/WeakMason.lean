/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.Matroid.Constructions
import MathlibExt.Combinatorics.Matroid.WeakMason

namespace MathlibExt.Combinatorics.WeakMasonWanted.Tests

open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

private def ground : Finset ℕ := {1, 3, 5}

local instance freeOnGroundFinite : (Matroid.freeOn (↑ground : Set ℕ)).Finite :=
  ⟨by simpa only [Matroid.freeOn_ground] using ground.finite_toSet⟩

private lemma freeCount (k : ℕ) :
    independentSetCount (Matroid.freeOn (↑ground : Set ℕ)) k = (3 : ℕ).choose k := by
  classical
  have hcard : ground.card = 3 := by decide
  rw [← hcard, ← Finset.card_powersetCard, independentSetCount, ← Set.ncard_coe_finset]
  congr 1
  ext I
  simp [Finset.mem_powersetCard, and_comm]

-- The first inequality for a three-element free matroid on an infinite ambient type.
example : (3 : ℕ).choose 0 * (3 : ℕ).choose 2 ≤ ((3 : ℕ).choose 1) ^ 2 := by
  simpa only [freeCount] using
    independentSetCount_logConcave (Matroid.freeOn (↑ground : Set ℕ)) 1 (hk := le_rfl)

example : independentSetCount (Matroid.freeOn (↑ground : Set ℕ)) 4 = 0 := by
  rw [freeCount]
  decide

-- The upper-tail inequality for the empty ground set.
example :
    independentSetCount (Matroid.emptyOn ℕ) 2 * independentSetCount (Matroid.emptyOn ℕ) 4 ≤
      independentSetCount (Matroid.emptyOn ℕ) 3 ^ 2 :=
  independentSetCount_logConcave (Matroid.emptyOn ℕ) 3 (hk := by decide)

end MathlibExt.Combinatorics.WeakMasonWanted.Tests
