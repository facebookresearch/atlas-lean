/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted

private abbrev emptyClass : FiniteGroupClass := fun _ _ _ => False

example : IsFormation emptyClass := by
  constructor
  · intro _ _ _ _ _ _ _ _ h
    exact h.elim
  · intro _ _ _ _ _ _ _ h
    exact h.elim

-- Joining the empty formation to a formation leaves every membership predicate unchanged.
example (X : FiniteGroupClass) (hX : IsFormation X) : formationJoin emptyClass X = X := by
  funext G _ _
  apply propext
  constructor
  · intro h
    exact h X hX fun _ _ _ h => h.elim False.elim id
  · intro h Y _ hinc
    exact hinc G (Or.inr h)

-- Packaging injectivity as an embedding gives the same obstruction.
example (embed : ∀ (L : Type) [Lattice L] [IsModularLattice L] [Finite L],
    ∃ f : L ↪ FiniteGroupClass, (∀ a, IsFormation (f a)) ∧
      (∀ a b, f (a ⊓ b) = classMeet (f a) (f b)) ∧
      ∀ a b, f (a ⊔ b) = formationJoin (f a) (f b)) : False := by
  apply finiteModularLatticeEmbedsInFormations_refuted
  intro L _ _ _
  obtain ⟨f, hform, hmeet, hjoin⟩ := embed L
  exact ⟨f, hform, f.injective, hmeet, hjoin⟩
