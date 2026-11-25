/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ScottishBook95

/-! # Tests for the permutation representation of the additive reals -/

open MathlibExt.GroupTheory.ScottishBook95Wanted

-- Every nonzero real moves some natural number.
example : ∃ f : Multiplicative ℝ →* Equiv.Perm ℕ,
    ∀ x : ℝ, x ≠ 0 → ∃ n : ℕ, f (.ofAdd x) n ≠ n := by
  obtain ⟨f, hf⟩ := real_addGroup_embeds_in_perm_nat
  refine ⟨f, fun x hx => ?_⟩
  by_contra! h
  have hperm : f (.ofAdd x) = 1 := Equiv.ext h
  exact hx (congrArg Multiplicative.toAdd (hf (hperm.trans f.map_one.symm)))
