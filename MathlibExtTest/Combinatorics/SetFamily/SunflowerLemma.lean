/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SetFamily.SunflowerLemma

/-!
# Tests for the Erdős–Rado sunflower lemma

The hypotheses are instantiated on concrete families, including three pairs (`w = 2`, `p = 2`: `2! · 1 ^ 2 = 2 < 3`) and a family of `3`-sets.
-/

open Finset MathlibExt.Combinatorics.SetFamily.SunflowerLemma

namespace MathlibExtTest.Combinatorics.SetFamily.SunflowerLemma

/-- Two singletons form a sunflower with two petals (`w = 1`, `p = 2`, `1 < 2`). -/
example : ∃ S ⊆ ({{0}, {1}} : Finset (Finset ℕ)), S.card = 2 ∧ IsDeltaSystem S :=
  exists_isDeltaSystem 1 2 _ (by decide) (by decide)

/-- Three pairs give a two-petal sunflower (`w = 2`, `p = 2`, `2 < 3`). -/
example : ∃ S ⊆ ({{0, 1}, {2, 3}, {0, 2}} : Finset (Finset ℕ)), S.card = 2 ∧ IsDeltaSystem S :=
  exists_isDeltaSystem 2 2 _ (by decide) (by decide)

/-- A family of three singletons has a `3`-petal sunflower
(`w = 1`, `p = 3`: `1! · 2 = 2 < 3`). -/
example : ∃ S ⊆ ({{0}, {1}, {2}} : Finset (Finset ℕ)), S.card = 3 ∧ IsDeltaSystem S :=
  exists_isDeltaSystem 1 3 _ (by decide) (by decide)

/-- The kernel of a sunflower need not be empty: `{0, 1}, {0, 2}, {0, 3}` has kernel `{0}`. -/
example : IsDeltaSystem ({{0, 1}, {0, 2}, {0, 3}} : Finset (Finset ℕ)) :=
  ⟨{0}, by decide⟩

end MathlibExtTest.Combinatorics.SetFamily.SunflowerLemma
