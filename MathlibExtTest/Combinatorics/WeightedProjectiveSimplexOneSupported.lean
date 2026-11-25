/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexOneSupported

/-! # Examples of the one-supported weight constraint -/

open MetaMathlibExt

-- A nonempty list of twos is excluded, including the single weight at multiplicity one.
example (k : ℕ) : ¬ (IsReflexive (weightedSimplexList (2 :: List.replicate k 2)) ∧
    HasIDP (weightedSimplexList (2 :: List.replicate k 2))) := by
  rintro ⟨href, hidp⟩
  have h := one_supported_idp_reflexive_support_eq_one 2 (k + 1) (by decide)
    (Nat.succ_pos k) href hidp
  exact absurd h (by decide)
