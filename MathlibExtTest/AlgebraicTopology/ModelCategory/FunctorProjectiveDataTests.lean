/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Full original generator and five-class clients for ordinary projective models -/
set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
namespace MathlibExtTest.FunctorProjectiveData
variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} D] [LocallySmall.{w} D] (d : CofibrantGenerationData M κ)

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    CofibrantGenerationData (D ⥤ M) κ := FunctorProjective.generationData d

example : (FunctorProjective.freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ :=
  FunctorProjective.freeI_eligible d

example : (FunctorProjective.freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ :=
  FunctorProjective.freeJ_eligible d

example (x : D) {A B : M} (f : A ⟶ B) (hf : d.I f) :
    FunctorProjective.freeGenerators d d.I ((FunctorProjective.freeFunctor d x).map f) :=
  FunctorProjective.freeGenerator_mem d d.I x f hf

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp :=
  FunctorProjective.cofibrations_eq_objectwise_llp d

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  FunctorProjective.trivialCofibrations_eq_objectwise_llp d

example {X Y : D ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    cofibrations (D ⥤ M) f → ∀ x, cofibrations M (f.app x) :=
  FunctorProjective.cofibrations_le_objectwise d f

example {X Y : D ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    trivialCofibrations (D ⥤ M) f → ∀ x, trivialCofibrations M (f.app x) :=
  FunctorProjective.trivialCofibrations_le_objectwise d f

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.generationData d).I.rlp = trivialFibrations (D ⥤ M) :=
by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact (FunctorProjective.generationData d).I_rlp

example : letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.generationData d).J.rlp = fibrations (D ⥤ M) :=
by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory (J := D) d
  exact (FunctorProjective.generationData d).J_rlp

section Empty
example {X Y : Discrete PEmpty ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (Discrete PEmpty ⥤ M) :=
      FunctorProjective.modelCategory.{w} (J := Discrete PEmpty) d
    trivialFibrations (Discrete PEmpty ⥤ M) f := by
  let _ : ModelCategory (Discrete PEmpty ⥤ M) :=
    FunctorProjective.modelCategory.{w} (J := Discrete PEmpty) d
  rw [FunctorProjective.trivialFibrations_eq d]
  rintro ⟨x⟩
  exact x.elim
end Empty

section Infinite
example {X Y : Discrete ℕ ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (Discrete ℕ ⥤ M) :=
      FunctorProjective.modelCategory.{w} (J := Discrete ℕ) d
    fibrations (Discrete ℕ ⥤ M) f ↔ ∀ n : ℕ, fibrations M (f.app ⟨n⟩) := by
  let _ : ModelCategory (Discrete ℕ ⥤ M) :=
    FunctorProjective.modelCategory.{w} (J := Discrete ℕ) d
  rw [FunctorProjective.fibrations_eq d]
  exact ⟨fun h n => h ⟨n⟩, fun h n => h n.as⟩
end Infinite

section Nonthin
example {X Y : SingleObj (Multiplicative ℕ) ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.modelCategory.{w} (J := SingleObj (Multiplicative ℕ)) d
    fibrations (SingleObj (Multiplicative ℕ) ⥤ M) f ↔
      fibrations M (f.app (SingleObj.star (Multiplicative ℕ))) := by
  let _ : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
    FunctorProjective.modelCategory.{w} (J := SingleObj (Multiplicative ℕ)) d
  rw [FunctorProjective.fibrations_eq d]
  constructor
  · exact fun h => h _
  · intro h x
    cases x
    exact h
end Nonthin

section RaisedIndex
local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Small.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : LocallySmall.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) where
  hom_small x y := by
    let _ : Small.{w} (x.objDown.down ⟶ y.objDown.down) :=
      LocallySmall.hom_small _ _
    exact small_map Equiv.ulift
example : letI : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
    FunctorProjective.modelCategory.{w} (J := ULiftHom.{vD + 1} (ULift.{uD + 1} D)) d
    CofibrantGenerationData (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) κ :=
  FunctorProjective.generationData d
end RaisedIndex
end MathlibExtTest.FunctorProjectiveData
