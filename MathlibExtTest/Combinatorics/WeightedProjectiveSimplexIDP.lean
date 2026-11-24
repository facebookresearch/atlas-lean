/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexIDP

/-! # Examples of the two-supported classification -/

open MetaMathlibExt

-- With multiplicities two and three, both classified support pairs satisfy the condition.
example : SatisfiesSupportIDPNecessary ![1, 3] ![2, 3] := by
  unfold SatisfiesSupportIDPNecessary
  decide

example : SatisfiesSupportIDPNecessary ![4, 9] ![2, 3] := by
  apply (two_supported_classification _ _ (by decide) (by decide)
    (Fin.strictMono_iff_lt_succ.mpr (by decide))).2
  exact Or.inr ⟨rfl, rfl⟩

-- The larger weight still equals one plus twice the smaller, but the smaller equation fails.
example : ¬ SatisfiesSupportIDPNecessary ![2, 5] ![2, 3] := by
  unfold SatisfiesSupportIDPNecessary
  decide
