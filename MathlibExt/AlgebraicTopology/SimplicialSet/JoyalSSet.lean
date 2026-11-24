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
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# The designated simplicial category

The native induced category and ordinary forgetful equivalence retain
the underlying simplicial sets and maps. Model structures are separate
data on this designated carrier.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- A designated simplicial set contains an actual simplicial set. -/
@[ext]
structure JoyalSSet : Type (u + 1) where
  /-- The underlying simplicial set. -/
  toSSet : SSet.{u}

namespace JoyalSSet

/-- The native category induced by the underlying simplicial set. -/
instance category : Category.{u} JoyalSSet.{u} :=
  inferInstanceAs (Category.{u} (InducedCategory SSet.{u} JoyalSSet.toSSet))

/-- Forget the designation and retain the actual simplicial map. -/
@[simps! obj map]
def forget : JoyalSSet.{u} ⥤ SSet.{u} :=
  inducedFunctor JoyalSSet.toSSet

/-- Wrap simplicial sets and their maps in the designated category. -/
@[simps! obj map_hom]
def ofSSet : SSet.{u} ⥤ JoyalSSet.{u} where
  obj X := ⟨X⟩
  map f := InducedCategory.homMk f

/-- Designated morphisms identify with the original simplicial maps. -/
@[simps!]
def homEquiv {X Y : JoyalSSet.{u}} : (X ⟶ Y) ≃ (X.toSSet ⟶ Y.toSSet) :=
  InducedCategory.homEquiv

/-- The canonical equivalence between designated and ordinary simplicial sets. -/
def equivalenceSSet : JoyalSSet.{u} ≌ SSet.{u} where
  functor := forget
  inverse := ofSSet
  unitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Iso.refl X.toSSet))
    (by
      intro X Y f
      apply InducedCategory.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  counitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) (by
    intro X Y f
    simp [forget, ofSSet])
  functor_unitIso_comp X := by
    simp [forget, ofSSet]
    rfl

instance : forget.{u}.IsEquivalence :=
  equivalenceSSet.isEquivalence_functor

instance : ofSSet.{u}.IsEquivalence :=
  equivalenceSSet.isEquivalence_inverse

/-- Transfer every limit shape which exists for ordinary simplicial sets. -/
instance hasLimitsOfShape (J : Type v) [Category.{w} J]
    [HasLimitsOfShape J SSet.{u}] : HasLimitsOfShape J JoyalSSet.{u} :=
  Adjunction.hasLimitsOfShape_of_equivalence forget

/-- Transfer every colimit shape which exists for ordinary simplicial sets. -/
instance hasColimitsOfShape (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J SSet.{u}] : HasColimitsOfShape J JoyalSSet.{u} :=
  Adjunction.hasColimitsOfShape_of_equivalence forget

/-- Pull an arbitrary morphism property back along the actual forgetful functor. -/
def transportMorphismProperty (P : MorphismProperty SSet.{u}) :
    MorphismProperty JoyalSSet.{u} :=
  P.inverseImage forget

/-- Pull an arbitrary object property back along the actual forgetful functor. -/
def transportObjectProperty (P : ObjectProperty SSet.{u}) : ObjectProperty JoyalSSet.{u} :=
  P.inverseImage forget

@[simp]
lemma transportMorphismProperty_iff (P : MorphismProperty SSet.{u})
    {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    transportMorphismProperty P f ↔ P (forget.map f) := Iff.rfl

@[simp]
lemma transportObjectProperty_iff (P : ObjectProperty SSet.{u}) (X : JoyalSSet.{u}) :
    transportObjectProperty P X ↔ P X.toSSet := Iff.rfl

end JoyalSSet
