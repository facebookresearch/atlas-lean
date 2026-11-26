/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97
import Mathlib.GroupTheory.QuotientGroup.Basic

open MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted

-- The empty series admits the trivial group for every choice of factor.
example (T : Type) [Group T] : AllCompositionFactorsIso T Unit :=
  ⟨0, fun _ ↦ ⊥, rfl, Subsingleton.elim _ _, Fin.elim0⟩

-- A member of an isomorphism-closed class has trivial residual.
example (X : GroupClass) (G : Type) [Group G] (hg : X.mem G) : residual X G = ⊥ := by
  apply bot_unique
  exact iInf_le_of_le (⊥ : Subgroup G) (iInf_le _ ⟨inferInstance,
    X.iso G _ QuotientGroup.quotientBot.symm hg⟩)

-- In particular a single proper nontrivial subformation cannot square to the whole formation.
example (T : Type) [Group T] [Finite T] (hs : IsSimpleGroup T) (hn : ∃ a b : T, a * b ≠ b * a)
    (X : GroupClass) (hX : IsFormation X) (hx : NontrivialClass X)
    (hsub : ∀ (G : Type) [Group G] [Finite G], X.mem G → AllCompositionFactorsIso T G)
    (hproper : IsProperIn T X) :
    ¬ ∀ (G : Type) [Group G] [Finite G], AllCompositionFactorsIso T G ↔ X.mem (residual X G) :=
  compositionFactorFormationIndecomposable_holds T hs hn X X hX hX hx hx hsub hsub hproper hproper
