/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialEnoughInjectives
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Injective presentations in nonadditive diagram categories

Diagrams of types indexed by an independent discrete type have injective
presentations, including when the index is empty. These clients check the
component embeddings and extension through monomorphisms. They also obtain
injective presentations of inverse sequences of types, where the value
category has finite limits but no preadditive structure.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SequentialEnoughInjectivesTests

universe u v

noncomputable section

section DiscreteTypes

variable {I : Type v}

local instance : EnoughInjectives (Discrete I ⥤ Type u) := enoughInjectives_discrete I

/-- For a diagram of types, the chosen injective presentation is injective at every index, with
independent index and value universes. -/
theorem typeDiscrete_component_injective (D : Discrete I ⥤ Type u) (i : Discrete I) :
    Function.Injective ((Injective.ι D).app i) := by
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

/-- A map into the chosen injective diagram extends through any monomorphism of discrete diagrams.
  -/
theorem typeDiscrete_extension (D : Discrete I ⥤ Type u)
    {A B : Discrete I ⥤ Type u} (f : A ⟶ B) [Mono f]
    (g : A ⟶ Injective.under D) :
    f ≫ Injective.factorThru g f = g := by
  simp

end DiscreteTypes

section EmptyDiscrete

local instance : EnoughInjectives (Discrete PEmpty.{v + 1} ⥤ Type u) :=
  enoughInjectives_discrete PEmpty.{v + 1}

/-- For an empty index, the chosen presentation map is an isomorphism of diagrams. -/
theorem emptyDiscrete_presentation_isIso
    (D : Discrete PEmpty.{v + 1} ⥤ Type u) : IsIso (Injective.ι D) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  cases i.as

end EmptyDiscrete

/-- An inverse sequence of types admits a monomorphism into an injective inverse sequence. -/
theorem typeSequential_mono_presentation (A : ℕᵒᵖ ⥤ Type u) :
    ∃ (J : ℕᵒᵖ ⥤ Type u) (η : A ⟶ J), Injective J ∧ Mono η := by
  fail_if_success
    have : HasZeroMorphisms (Type u) := inferInstance
  fail_if_success
    have : Preadditive (Type u) := inferInstance
  have : EnoughInjectives (ℕᵒᵖ ⥤ Type u) := enoughInjectives_sequential
  exact ⟨Injective.under A, Injective.ι A, inferInstance, inferInstance⟩

end
end SequentialEnoughInjectivesTests
