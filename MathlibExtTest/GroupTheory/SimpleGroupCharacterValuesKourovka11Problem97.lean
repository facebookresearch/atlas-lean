/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97

open MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted

-- Applying the refutation yields one common set of character values for arbitrarily large groups.
example :
    ∃ S : Set ℂ, S.Finite ∧ ∀ N : ℕ,
      ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
        (∃ a b : G, a * b ≠ b * a) ∧ (∃ g : G, irrCharValues g = S) ∧ N < Nat.card G := by
  have h := finitelyManySimpleGivenCharacterValues_refuted
  unfold finitelyManySimpleGivenCharacterValues at h
  push Not at h
  exact h
