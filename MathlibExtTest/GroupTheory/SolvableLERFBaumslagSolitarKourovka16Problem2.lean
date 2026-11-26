/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2

open MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted

-- Recover the existential version of the negative answer from the public theorem.
example : ∃ (G : Type) (_ : Group G), Group.FG G ∧ Group.IsSolvable G ∧
    ¬ (IsLocallySubgroupSeparable G ↔
      ¬ ∃ n : ℕ, 1 < n ∧ ∃ f : BS1 n →* G, Function.Injective f) := by
  by_contra h
  apply solvableLERFIffNoBaumslagSolitar_refuted
  intro G inst hfg hsol
  by_contra he
  exact h ⟨G, inst, hfg, hsol, he⟩

-- The identity map separates every subgroup of a finite group.
example (G : Type) [Group G] [Finite G] : IsLocallySubgroupSeparable G := by
  intro H _ x hx
  exact ⟨G, inferInstance, inferInstance, MonoidHom.id G, by simpa using hx⟩
