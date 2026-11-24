/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The designated simplicial-space category

`SimplicialSpace` stores an actual simplicial object in simplicial sets. Its
ordinary category, forgetful equivalence and morphisms use the native
induced-category construction. No model or enrichment is chosen here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- A designated simplicial space contains an actual simplicial object in
simplicial sets of the specified value universe. -/
@[ext]
structure SimplicialSpace : Type (u + 1) where
  /-- The underlying simplicial-space diagram. -/
  diagram : SimplicialObject SSet.{u}

namespace SimplicialSpace

/-- The native ordinary category induced by the stored diagram. -/
instance category : Category.{u} SimplicialSpace.{u} :=
  inferInstanceAs
    (Category.{u} (InducedCategory (SimplicialObject SSet.{u}) SimplicialSpace.diagram))

/-- Forget only the designation, retaining the actual diagram and maps. -/
@[simps! obj map]
def forget : SimplicialSpace.{u} ⥤ SimplicialObject SSet.{u} :=
  inducedFunctor SimplicialSpace.diagram

/-- Wrap an actual simplicial-space diagram and its natural transformations. -/
@[simps! obj map_hom]
def ofSimplicialObject : SimplicialObject SSet.{u} ⥤ SimplicialSpace.{u} where
  obj X := ⟨X⟩
  map f := InducedCategory.homMk f

/-- Designated maps identify with the original natural transformations. -/
def homEquiv {X Y : SimplicialSpace.{u}} : (X ⟶ Y) ≃ (X.diagram ⟶ Y.diagram) :=
  InducedCategory.homEquiv

/-- The equivalence with the original ordinary simplicial-space category.
Both unit and counit have identity underlying components. -/
def equivalenceSimplicialObject : SimplicialSpace.{u} ≌ SimplicialObject SSet.{u} where
  functor := forget
  inverse := ofSimplicialObject
  unitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Iso.refl X.diagram))
    (by
      intro X Y f
      apply InducedCategory.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  counitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) (by
    intro X Y f
    simp [forget, ofSimplicialObject])
  functor_unitIso_comp X := by
    simp [forget, ofSimplicialObject]
    rfl

instance : forget.{u}.IsEquivalence :=
  equivalenceSimplicialObject.isEquivalence_functor

instance : ofSimplicialObject.{u}.IsEquivalence :=
  equivalenceSimplicialObject.isEquivalence_inverse

/-- The whole raw functor round trip retains its objects and maps. -/
@[simp]
theorem ofSimplicialObject_comp_forget :
    ofSimplicialObject.{u} ⋙ forget = 𝟭 (SimplicialObject SSet.{u}) := rfl

/-- The whole designated functor round trip is the identity. -/
@[simp]
theorem forget_comp_ofSimplicialObject :
    forget.{u} ⋙ ofSimplicialObject = 𝟭 SimplicialSpace.{u} := rfl

/-- Transfer every limit shape already available for raw simplicial spaces. -/
instance hasLimitsOfShape (J : Type v) [Category.{w} J]
    [HasLimitsOfShape J (SimplicialObject SSet.{u})] :
    HasLimitsOfShape J SimplicialSpace.{u} :=
  Adjunction.hasLimitsOfShape_of_equivalence forget

/-- Transfer every colimit shape already available for raw simplicial spaces. -/
instance hasColimitsOfShape (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J (SimplicialObject SSet.{u})] :
    HasColimitsOfShape J SimplicialSpace.{u} :=
  Adjunction.hasColimitsOfShape_of_equivalence forget

/-- Monicity is preserved and reflected by the native forgetful equivalence. -/
@[simp]
theorem mono_forget_map_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    Mono f.hom ↔ Mono f := by
  constructor
  · exact forget.mono_of_mono_map
  · intro h
    let _ : Mono f := h
    exact inferInstanceAs (Mono (forget.map f))

/-- Both components of the induced Arrow counit are actual identities. -/
theorem arrow_counit_components (f : Arrow (SimplicialObject SSet.{u})) :
    ((Functor.mapArrowEquivalence equivalenceSimplicialObject).counitIso.app f).hom.left =
        𝟙 f.left ∧
      ((Functor.mapArrowEquivalence equivalenceSimplicialObject).counitIso.app f).hom.right =
        𝟙 f.right :=
  ⟨rfl, rfl⟩

/-- The induced Arrow unit keeps identity underlying components. -/
theorem arrow_unit_components (f : Arrow SimplicialSpace.{u}) :
    (((Functor.mapArrowEquivalence equivalenceSimplicialObject).unitIso.app f).hom.left).hom =
        𝟙 f.left.diagram ∧
      (((Functor.mapArrowEquivalence equivalenceSimplicialObject).unitIso.app f).hom.right).hom =
        𝟙 f.right.diagram :=
  ⟨rfl, rfl⟩

end SimplicialSpace
