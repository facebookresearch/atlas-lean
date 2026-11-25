/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Existence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Original carrier and actual selected-data projective contracts -/
set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.FunctorProjectiveExistence

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] [HasCompatibleCofibrantGeneration.{w} M]
  [Small.{w} D] [LocallySmall.{w} D]

example : ModelCategory (D ⥤ M) := FunctorProjective.Selected.modelCategory

example :
    letI : Fact (FunctorProjective.Selected.cardinal (M := M)).IsRegular :=
      FunctorProjective.Selected.cardinal_regular
    letI : OrderBot (FunctorProjective.Selected.cardinal (M := M)).ord.ToType :=
      FunctorProjective.Selected.orderBot
    FunctorProjective.Selected.modelCategory (D := D) (M := M) =
      FunctorProjective.modelCategory (J := D) (FunctorProjective.Selected.baseData (M := M)) :=
  FunctorProjective.Selected.modelCategory_eq_fixed

section OriginalModel

local instance : Fact (FunctorProjective.Selected.cardinal (M := M)).IsRegular :=
  FunctorProjective.Selected.cardinal_regular
/-- The original selected ordinal bottom used by all projective test contracts. -/
local instance originalSelectedOrderBot :
    OrderBot (FunctorProjective.Selected.cardinal (M := M)).ord.ToType :=
  FunctorProjective.Selected.orderBot

/-- The actual selected projective model on the original test carrier. -/
local instance originalSelectedFunctorModel : ModelCategory (D ⥤ M) :=
  FunctorProjective.Selected.modelCategory


example : CofibrantGenerationData (D ⥤ M) (FunctorProjective.Selected.cardinal (M := M)) :=
  FunctorProjective.Selected.generationData

example : (FunctorProjective.Selected.generationData (D := D) (M := M)).I =
    FunctorProjective.freeGenerators (D := D) (FunctorProjective.Selected.baseData (M := M))
      (FunctorProjective.Selected.baseData (M := M)).I :=
  FunctorProjective.Selected.generationData_I

example :
    (FunctorProjective.Selected.generationData (D := D) (M := M)).J.IsCardinalForSmallObjectArgument
      (FunctorProjective.Selected.cardinal (M := M)) :=
  FunctorProjective.Selected.generationData_J_eligible

example : cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp :=
  FunctorProjective.Selected.cofibrations_eq

example : trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  FunctorProjective.Selected.trivialCofibrations_eq

example {X Y : D ⥤ M} (f : X ⟶ Y) :
    cofibrations (D ⥤ M) f → ∀ x, cofibrations M (f.app x) :=
  FunctorProjective.Selected.cofibrations_le_objectwise f

example : FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  FunctorProjective.Selected.cofibrantFactorizationData

example : FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  FunctorProjective.Selected.fibrantFactorizationData

example : FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M) =
    FunctorProjective.cofibrantFactorizationData (FunctorProjective.Selected.baseData (M := M)) :=
  FunctorProjective.Selected.cofibrantFactorizationData_eq_fixed

example (f : Arrow (D ⥤ M)) (x : D) :
    ((FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
      ((FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).p.app f).app x =
        f.hom.app x :=
  FunctorProjective.Selected.fibrantFactorizationData_fac_app f x

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    φ.left.app x ≫
      ((FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app g).app x =
        ((FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
          ((FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).Z.map φ).app x
      :=
  FunctorProjective.Selected.cofibrantFactorizationData_i_naturality_app φ x

example {f g k : Arrow (D ⥤ M)} (φ : f ⟶ g) (ψ : g ⟶ k) :
    (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z.map (φ ≫ ψ) =
      (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z.map φ ≫
        (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z.map ψ :=
  (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z.map_comp φ ψ

example : IsWeakFactorizationSystem (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  inferInstance

example : IsWeakFactorizationSystem (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  inferInstance

example (f : Arrow (D ⥤ M)) :
    (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app f ≫
      (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).p.app f =
        f.hom :=
  (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).fac_app

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    φ.left ≫ (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app g =
      (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app f ≫
        (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).Z.map φ :=
  (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.naturality φ

example {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z.map φ ≫
        (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).p.app g =
      (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).p.app f ≫ φ.right :=
  (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).p.naturality φ

example (f : Arrow (D ⥤ M)) :
    cofibrations (D ⥤ M)
      ((FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).i.app f) :=
  (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).hi f

example (f : Arrow (D ⥤ M)) :
    trivialFibrations (D ⥤ M)
      ((FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).p.app f) :=
  (FunctorProjective.Selected.cofibrantFactorizationData (D := D) (M := M)).hp f

example (f : Arrow (D ⥤ M)) :
    trivialCofibrations (D ⥤ M)
      ((FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).i.app f) :=
  (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).hi f

example (f : Arrow (D ⥤ M)) :
    fibrations (D ⥤ M)
      ((FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).p.app f) :=
  (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).hp f

example :
    letI : (FunctorProjective.freeGenerators (D := D) (FunctorProjective.Selected.baseData (M := M))
      (FunctorProjective.Selected.baseData (M := M)).J).IsCardinalForSmallObjectArgument
        (FunctorProjective.Selected.cardinal (M := M)) :=
          FunctorProjective.freeJ_eligible (FunctorProjective.Selected.baseData (M := M))
    (FunctorProjective.Selected.fibrantFactorizationData (D := D) (M := M)).Z =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (FunctorProjective.Selected.baseData (M := M))
          (FunctorProjective.Selected.baseData (M := M)).J)
        (FunctorProjective.Selected.cardinal (M := M))).Z :=
  FunctorProjective.Selected.fibrantFactorizationData_Z

end OriginalModel

section OtherWitness

variable {μ : Cardinal.{w}} [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
  (e : CofibrantGenerationData M μ)

example :
    let m := FunctorProjective.Selected.modelCategory (D := D) (M := M)
    let n := FunctorProjective.modelCategory (J := D) e
    m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = n.categoryWithFibrations.fibrations ∧
      m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations ∧
      m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithFibrations.fibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithCofibrations.cofibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithCofibrations.cofibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences :=
  FunctorProjective.Selected.prescribed_classes_eq_fixed e

end OtherWitness

section Empty

example {X Y : Discrete PEmpty ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (Discrete PEmpty ⥤ M) :=
      FunctorProjective.Selected.modelCategory.{w} (D := Discrete PEmpty)
    trivialFibrations (Discrete PEmpty ⥤ M) f := by
  let _ : ModelCategory (Discrete PEmpty ⥤ M) :=
    FunctorProjective.Selected.modelCategory.{w} (D := Discrete PEmpty)
  rw [FunctorProjective.Selected.trivialFibrations_eq]
  rintro ⟨x⟩
  exact x.elim

end Empty

section Infinite

example {X Y : Discrete ℕ ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (Discrete ℕ ⥤ M) :=
      FunctorProjective.Selected.modelCategory.{w} (D := Discrete ℕ)
    fibrations (Discrete ℕ ⥤ M) f ↔ ∀ n : ℕ, fibrations M (f.app ⟨n⟩) := by
  let _ : ModelCategory (Discrete ℕ ⥤ M) :=
    FunctorProjective.Selected.modelCategory.{w} (D := Discrete ℕ)
  rw [FunctorProjective.Selected.fibrations_eq]
  exact ⟨fun h n => h ⟨n⟩, fun h n => h n.as⟩

end Infinite

section Nonthin

example {X Y : SingleObj (Multiplicative ℕ) ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.Selected.modelCategory.{w} (D := SingleObj (Multiplicative ℕ))
    fibrations (SingleObj (Multiplicative ℕ) ⥤ M) f ↔
      fibrations M (f.app (SingleObj.star (Multiplicative ℕ))) := by
  let _ : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
    FunctorProjective.Selected.modelCategory.{w} (D := SingleObj (Multiplicative ℕ))
  rw [FunctorProjective.Selected.fibrations_eq]
  constructor
  · exact fun h => h _
  · intro h x
    cases x
    exact h

end Nonthin

section RaisedIndex

/-- The original category after raising only its object universe. -/
local instance raisedIndexCategory : Category.{vD} (ULift.{uD + 1} D) :=
  uliftCategory D

local instance : Small.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
/-- The original index category with independently raised Hom and object universes. -/
local instance raisedIndexHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

local instance : LocallySmall.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) where
  hom_small x y := by
    let _ : Small.{w} (x.objDown.down ⟶ y.objDown.down) :=
      LocallySmall.hom_small _ _
    exact small_map Equiv.ulift

example : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
  FunctorProjective.Selected.modelCategory.{w} (D := ULiftHom.{vD + 1} (ULift.{uD + 1} D))

end RaisedIndex

end MathlibExtTest.FunctorProjectiveExistence
