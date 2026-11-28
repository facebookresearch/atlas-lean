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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialInjective
public import MathlibExtTest.CategoryTheory.Limits.Shapes.SequentialCofree

/-!
# Injective inverse-sequence clients

These clients use injectivity in the category of inverse sequences to split
successor transitions under finite-product and zero-morphism hypotheses.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits.SequentialInjectiveTests

universe u v

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C]
variable (J : ℕᵒᵖ ⥤ C) [Injective J]

example :
    (sequentialCofreeUnit C).app J ≫ sequentialInjectiveCofreeRetraction C J = 𝟙 J := by
  fail_if_success
    have _ : EnoughInjectives C := inferInstance
  exact sequentialInjectiveCofreeUnit_retraction C J

variable [HasZeroMorphisms C]

example (n : ℕ) :
    sequentialInjectiveTransitionSection C J n ≫
        J.map (homOfLE (Nat.le_succ n)).op = 𝟙 (J.obj (op n)) :=
  (sequentialInjectiveTransitionSplitEpi C J n).id

example (n : ℕ) : IsSplitEpi (J.map (homOfLE (Nat.le_succ n)).op) :=
  inferInstance

example (n : ℕ) : Epi (J.map (homOfLE (Nat.le_succ n)).op) :=
  inferInstance

/-- The existing zero-transition integer tower cannot be an injective diagram. -/
example : ¬ Injective SequentialCofreeTests.zeroTower := by
  intro h
  have : Injective SequentialCofreeTests.zeroTower := h
  have he : SequentialCofreeTests.zeroTower.map (homOfLE (Nat.le_succ 0)).op =
      (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) :=
    Functor.ofOpSequence_map_homOfLE_succ
      (X := fun _ : ℕ => ModuleCat.of ℤ ℤ)
      (fun _ : ℕ => (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) 0
  have hepi : Epi (SequentialCofreeTests.zeroTower.map (homOfLE (Nat.le_succ 0)).op) :=
    inferInstance
  have hz : Epi (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) := he ▸ hepi
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective
    (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)).1 hz (1 : ℤ)
  have h01 : (0 : ℤ) = 1 := by
    simpa only [ModuleCat.hom_zero, LinearMap.zero_apply] using hm
  exact zero_ne_one h01

end CategoryTheory.Limits.SequentialInjectiveTests
