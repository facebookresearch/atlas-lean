/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74

/-! Regression tests for the statement of Kourovka Notebook Problem 20.74(a). -/

open MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
open scoped Pointwise

example (G : Type) [Group G] : HasLargeInverseClosedNormalSubsetWithSmallSquare G ↔
    ∃ S : Set G, (∀ g s : G, s ∈ S → g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧
      (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard ∧ S * S ≠ Set.univ :=
  Iff.rfl

example : ¬ ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → HasLargeInverseClosedNormalSubsetWithSmallSquare G →
    Nat.card G ≤ N :=
  finitelyManySimpleGroupsWithLargeNormalSubset_refuted
