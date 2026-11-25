/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
import MathlibExt.CategoryTheory.Functor.CoaugmentationHomEquivalence
import Mathlib.CategoryTheory.Types.Basic
import Batteries.Tactic.Lint

/-!
# Natural coaugmentation Hom-test clients

The terminal functor example has a source whose coaugmentation is not an
isomorphism. It still satisfies the two exact hypotheses needed for the
target Hom equivalence. The general clients retain the original inverse
formula and both source and target naturality with independent universes.
-/

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Functor.CoaugmentationHomTests

namespace MathlibExtTest.CoaugmentationHomTests

private def terminalFunctor : Type u ⥤ Type u :=
  (Functor.const (Type u)).obj PUnit.{u + 1}

private def terminalUnit : 𝟭 (Type u) ⟶ terminalFunctor where
  app _X := ↾fun _ => PUnit.unit
  naturality {_X _Y} _f := rfl

private instance terminalUnit_isIso :
    IsIso (terminalUnit.app PUnit.{u + 1}) := by
  have h : terminalUnit.app PUnit.{u + 1} = 𝟙 PUnit.{u + 1} := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl
  rw [h]
  exact ⟨𝟙 PUnit.{u + 1}, Category.id_comp _, Category.id_comp _⟩

/-- The actual source coaugmentation is not invertible in this example. -/
theorem terminalUnit_empty_not_isIso :
    ¬ IsIso (terminalUnit.app PEmpty.{u + 1}) := by
  intro h
  have hb := (CategoryTheory.isIso_iff_bijective _).mp h
  obtain ⟨x, hx⟩ := hb.2 PUnit.unit
  cases x

/-- Hom tests need invertibility only at the chosen target and functor-image arrow. -/
theorem terminal_target_hom_test :
    Function.Bijective (fun g : PUnit.{u + 1} ⟶ PUnit.{u + 1} =>
      (↾fun x : PEmpty.{u + 1} => nomatch x) ≫ g) := by
  let f : PEmpty.{u + 1} ⟶ PUnit.{u + 1} := ↾fun x => nomatch x
  have hQ : IsIso (terminalFunctor.map f) := by
    change IsIso (𝟙 PUnit.{u + 1})
    infer_instance
  exact CategoryTheory.Functor.CoaugmentedTestRetract.precomp_bijective_of_map_isIso
    terminalFunctor terminalUnit f

section GeneralClients

variable {C : Type u} [Category.{v} C] {Q : C ⥤ C}
  (η : 𝟭 C ⟶ Q) {X Y E E' : C} (f : X ⟶ Y)
  [IsIso (Q.map f)] [IsIso (η.app E)]

example (g : X ⟶ E) :
    (homEquiv η f).symm g =
      η.app Y ≫ inv (Q.map f) ≫ Q.map g ≫ inv (η.app E) :=
  homEquiv_symm_apply η f g

example (g : X ⟶ E) : f ≫ (homEquiv η f).symm g = g :=
  (homEquiv η f).apply_symm_apply g

example (g : Y ⟶ E) : (homEquiv η f).symm (f ≫ g) = g :=
  (homEquiv η f).symm_apply_apply g

example {X' Y' : C} (f' : X' ⟶ Y') [IsIso (Q.map f')]
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f) (g : X ⟶ E) :
    b ≫ (homEquiv η f).symm g = (homEquiv η f').symm (a ≫ g) :=
  homEquiv_symm_source η f f' a b w g

example [IsIso (η.app E')] (g : X ⟶ E) (k : E ⟶ E') :
    (homEquiv η f).symm (g ≫ k) = (homEquiv η f).symm g ≫ k :=
  homEquiv_symm_target η f g k

end GeneralClients

#print axioms CategoryTheory.Functor.CoaugmentationHomTests.homEquiv
#print axioms CategoryTheory.Functor.CoaugmentedTestRetract.precomp_bijective_of_map_isIso
#print axioms MathlibExtTest.CoaugmentationHomTests.terminal_target_hom_test

#lint only unusedArguments in MathlibExt.CategoryTheory.Functor.CoaugmentationHomEquivalence

end MathlibExtTest.CoaugmentationHomTests
