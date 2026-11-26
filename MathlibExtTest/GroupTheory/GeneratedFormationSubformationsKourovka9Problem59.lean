/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FormationSubformationsFiniteKourovka16Problem31
import MathlibExt.GroupTheory.GeneratedFormationSubformationsKourovka9Problem59

/-!
# Tests for subformations of a generated formation (Kourovka Problem 9.59)

The refutation gives a finite group whose generated formation contains infinitely many formations.
The generated formation contains its generator and lies in every formation containing it, and it
agrees with the generated formation of the Kourovka 16.31 entry. The 9.59 proposition agrees with
the Lean statement of Problem 16.31, which specializes that problem (about groups with a
composition series) to finite groups.
-/

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
open MathlibExt.GroupTheory.FiniteGroupFormationShared
open MathlibExt.GroupTheory.GeneratedFormationSubformationsKourovka9Problem59Wanted
open MathlibExt.GroupTheory

example : ∃ (G : Type) (_ : Group G) (_ : Finite G),
    {𝔊 : FiniteGroupClass | IsFormation 𝔊 ∧ ClassLE 𝔊 (formationGeneratedBy G)}.Infinite := by
  by_contra! h
  exact generatedFormationFinitelyManySubformations_refuted h

example (G : Type) [Group G] [Finite G] : formationGeneratedBy G G :=
  fun _ _ hG ↦ hG

example (G : Type) [Group G] [Finite G] (𝔉 : FiniteGroupClass) (h𝔉 : IsFormation 𝔉) (hG : 𝔉 G) :
    ClassLE (formationGeneratedBy G) 𝔉 :=
  fun _ _ _ hH ↦ hH 𝔉 h𝔉 hG

example (G H : Type) [Group G] [Finite G] [Group H] [Finite H] :
    formationGeneratedBy G H ↔
      FormationSubformationsFiniteKourovka16Problem31Wanted.formationGeneratedBy G H :=
  Iff.rfl

example : generatedFormationFinitelyManySubformations ↔
    FormationSubformationsFiniteKourovka16Problem31Wanted.finitelyManySubformations :=
  Iff.rfl
