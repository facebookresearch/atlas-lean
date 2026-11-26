/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.Matroid.Constructions
import MathlibExt.Combinatorics.Matroid.WeakMason

/-! # Tests for `MathlibExt.Combinatorics.Matroid.WeakMason` -/

namespace MathlibExtTest.Combinatorics.Matroid.WeakMason

open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason
open MathlibExt.Combinatorics.WeakMasonWanted

private def ground : Finset ℕ := {0, 1}

private abbrev M : _root_.Matroid ℕ := Matroid.freeOn (ground : Set ℕ)

private instance : M.Finite := ⟨ground.finite_toSet⟩

-- The ambient type is infinite, but the ground set has just two elements.
example : M.E.ncard = 2 := by
  rw [Matroid.freeOn_ground, Set.ncard_coe_finset]
  decide

-- At `k = 1`, the neighboring counts are both nonzero.
example : independentSetCount M 0 * independentSetCount M 2 ≤ independentSetCount M 1 ^ 2 :=
  independentSetCount_logConcave M 1 (by decide)

-- At `k = |M.E| = 2`, the next count vanishes.
example : independentSetCount M 1 * independentSetCount M 3 ≤ independentSetCount M 2 ^ 2 :=
  independentSetCount_logConcave M 2 (by decide)

-- Truncated subtraction would give `f₀ f₁ ≤ f₀²` at zero, which need not hold.
example : ¬ (independentSetCount M (0 - 1) * independentSetCount M (0 + 1) ≤
    independentSetCount M 0 ^ 2) := by
  have hcount (k : ℕ) : independentSetCount M k = (ground.card).choose k := by
    have hset : {I ∈ Set.powersetCard ℕ k | M.Indep I} = ↑(ground.powersetCard k) := by
      ext I
      simp [Matroid.freeOn_indep_iff, and_comm]
    rw [independentSetCount, hset, Set.ncard_coe_finset, Finset.card_powersetCard]
  simp only [hcount]
  decide

end MathlibExtTest.Combinatorics.Matroid.WeakMason
