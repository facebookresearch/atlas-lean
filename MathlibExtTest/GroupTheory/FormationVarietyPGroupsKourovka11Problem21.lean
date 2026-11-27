/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21

open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

-- A single generator as a law cuts out precisely the trivial groups.
example (G : Type) [Group G] : SatisfiesLaws {FreeGroup.of 0} G ↔ Subsingleton G := by
  constructor
  · intro h
    apply subsingleton_of_forall_eq 1
    intro g
    simpa using h _ (Set.mem_singleton _) (FreeGroup.lift (fun _ => g))
  · intro h _ _ _
    exact h.elim _ _

-- Extract the counterexample with the same prime and formation for every choice of laws.
example : ∃ p : ℕ, p.Prime ∧ ∃ F : GroupClass, IsFormation F ∧
    (∀ (G : Type) [Group G], F G → IsPGroup p G) ∧
    ∀ W : Set (FreeGroup ℕ), ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
      (F G ↔ SatisfiesLaws W G) := by
  by_contra h
  apply subformationOfPGroupsIsVarietal_refuted
  intro p hp F hF hpF
  by_contra hW
  exact h ⟨p, hp, F, hF, hpF, fun W h => hW ⟨W, h⟩⟩
