/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75

/-! Regression for the exact statement and the finite counterexample used in its proof. -/

open MathlibExt.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75Wanted
open SambaleCounterexample

example : ¬ twoGroupOrderBoundByAbelianRank := twoGroupOrderBoundByAbelianRank_refuted

example : ∃ (G : Type) (_ : Group G) (_ : Finite G),
    IsPGroup 2 G ∧ Nat.card G = 2 ^ 85 ∧ Monoid.exponent G ∣ 2 ^ 2 ∧
      ∀ A : Subgroup G, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
        ∃ s : Finset G, s.card ≤ 28 ∧ Subgroup.closure (s : Set G) = A := counterexample

example (b : Bilin) (x : CocycleGroup b) : x ^ 4 = 1 := fourth x
