/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationFunctor

/-!
# The complete action and enriched functor equivalence

Both actual object functions, whole Hom maps and every morphism component
are recovered through the original closed adjunction. The unit and counit
are the unchanged identity component maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

/-- Currying retains the actual enriched functor and every whole naturality square. -/
def toWholeEnrichedFunctors : WholeRepresentation V C ⥤ WholeEnrichedFunctor V C where
  obj X := ⟨X.toEnrichedFunctor⟩
  map f := WholeEnrichedFunctor.Hom.ofAction f.app (fun x y => by
    change f.app x ▷ (x ⟶[V] y) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry _) =
      MonoidalClosed.uncurry (MonoidalClosed.curry _) ≫ f.app y
    rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
    exact f.comm x y)
  map_id X := by apply WholeEnrichedFunctor.hom_ext; intro x; rfl
  map_comp f g := by apply WholeEnrichedFunctor.hom_ext; intro x; rfl

/-- Uncurrying retains every original enriched functor map and morphism component. -/
def fromWholeEnrichedFunctors : WholeEnrichedFunctor V C ⥤ WholeRepresentation V C where
  obj F := ofEnrichedFunctor F.functor
  map f :=
    { app := f.app
      comm := f.comm }
  map_id F := by apply hom_ext; intro x; rfl
  map_comp f g := by apply hom_ext; intro x; rfl

/-- The complete action representation is recovered by its original identity components. -/
def enrichedUnitIsoApp (X : WholeRepresentation V C) :
    X ≅ fromWholeEnrichedFunctors.obj (toWholeEnrichedFunctors.obj X) where
  hom :=
    { app x := 𝟙 (X.obj x)
      comm x y := by
        change (𝟙 (X.obj x) ▷ (x ⟶[V] y)) ≫
          MonoidalClosed.uncurry (MonoidalClosed.curry (X.action x y)) = X.action x y ≫ 𝟙 _
        simp }
  inv :=
    { app x := 𝟙 (X.obj x)
      comm x y := by
        change (𝟙 (X.obj x) ▷ (x ⟶[V] y)) ≫ X.action x y =
          MonoidalClosed.uncurry (MonoidalClosed.curry (X.action x y)) ≫ 𝟙 _
        simp }
  hom_inv_id := by apply hom_ext; intro x; exact Category.id_comp _
  inv_hom_id := by apply hom_ext; intro x; exact Category.id_comp _

/-- Every whole enriched Hom map is recovered by the unchanged identity components. -/
def enrichedCounitIsoApp (F : WholeEnrichedFunctor V C) :
    toWholeEnrichedFunctors.obj (fromWholeEnrichedFunctors.obj F) ≅ F where
  hom := WholeEnrichedFunctor.Hom.ofAction (fun x => 𝟙 (F.functor.obj x)) (fun x y => by
    change (𝟙 (F.functor.obj x) ▷ (x ⟶[V] y)) ≫ MonoidalClosed.uncurry (F.functor.map x y) =
      MonoidalClosed.uncurry (MonoidalClosed.curry (MonoidalClosed.uncurry (F.functor.map x y)))
        ≫ 𝟙 _
    simp)
  inv := WholeEnrichedFunctor.Hom.ofAction (fun x => 𝟙 (F.functor.obj x)) (fun x y => by
    change (𝟙 (F.functor.obj x) ▷ (x ⟶[V] y)) ≫
      MonoidalClosed.uncurry (MonoidalClosed.curry (MonoidalClosed.uncurry (F.functor.map x y))) =
      MonoidalClosed.uncurry (F.functor.map x y) ≫ 𝟙 _
    simp)
  hom_inv_id := by apply WholeEnrichedFunctor.hom_ext; intro x; exact Category.id_comp _
  inv_hom_id := by apply WholeEnrichedFunctor.hom_ext; intro x; exact Category.id_comp _

/-- The unit is natural in every original whole transformation. -/
def enrichedUnitIso : 𝟭 (WholeRepresentation V C) ≅
    toWholeEnrichedFunctors ⋙ fromWholeEnrichedFunctors :=
  NatIso.ofComponents enrichedUnitIsoApp (fun f => by
    apply hom_ext
    intro x
    exact (Category.comp_id (f.app x)).trans (Category.id_comp (f.app x)).symm)

/-- The counit is natural in every complete enriched transformation. -/
def enrichedCounitIso : fromWholeEnrichedFunctors ⋙ toWholeEnrichedFunctors ≅
    𝟭 (WholeEnrichedFunctor V C) :=
  NatIso.ofComponents enrichedCounitIsoApp (fun f => by
    apply WholeEnrichedFunctor.hom_ext
    intro x
    exact (Category.comp_id (f.app x)).trans (Category.id_comp (f.app x)).symm)

/-- Whole action representations are equivalent to actual enriched functors with full naturality. -/
def enrichedEquivalence : WholeRepresentation V C ≌ WholeEnrichedFunctor V C where
  functor := toWholeEnrichedFunctors
  inverse := fromWholeEnrichedFunctors
  unitIso := enrichedUnitIso
  counitIso := enrichedCounitIso
  functor_unitIso_comp X := by
    apply WholeEnrichedFunctor.hom_ext
    intro x
    exact Category.id_comp _

/-- The forward functor retains the entire original object function. -/
theorem toWholeEnrichedFunctors_obj (X : WholeRepresentation V C) (x : C) :
    (toWholeEnrichedFunctors.obj X).functor.obj x = X.obj x := rfl

/-- The inverse functor retains the entire original object function. -/
theorem fromWholeEnrichedFunctors_obj (F : WholeEnrichedFunctor V C) (x : C) :
    (fromWholeEnrichedFunctors.obj F).obj x = F.functor.obj x := rfl

/-- Every whole morphism component is unchanged by the forward functor. -/
theorem toWholeEnrichedFunctors_map_app {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    (toWholeEnrichedFunctors.map f).app x = f.app x := rfl

/-- Every original enriched transformation component is unchanged by the inverse functor. -/
theorem fromWholeEnrichedFunctors_map_app {F G : WholeEnrichedFunctor V C} (f : F ⟶ G) (x : C) :
    (fromWholeEnrichedFunctors.map f).app x = f.app x := rfl

/-- The equivalence recovers the complete original action map. -/
theorem enrichedEquivalence_action (X : WholeRepresentation V C) (x y : C) :
    (enrichedEquivalence.inverse.obj (enrichedEquivalence.functor.obj X)).action x y =
      X.action x y := of_to_action X x y

/-- The equivalence recovers every whole original enriched Hom map. -/
theorem enrichedEquivalence_map (F : WholeEnrichedFunctor V C) (x y : C) :
    (enrichedEquivalence.functor.obj (enrichedEquivalence.inverse.obj F)).functor.map x y =
      F.functor.map x y := to_of_map F.functor x y

/-- Uncurrying after currying recovers the complete original action representation. -/
theorem of_to (X : WholeRepresentation V C) : ofEnrichedFunctor X.toEnrichedFunctor = X := by
  cases X
  dsimp only [ofEnrichedFunctor, toEnrichedFunctor]
  congr
  funext x y
  exact MonoidalClosed.uncurry_curry _

/-- Currying after uncurrying recovers the actual enriched functor, with all original Hom maps. -/
theorem to_of (F : EnrichedFunctor V C V) : (ofEnrichedFunctor F).toEnrichedFunctor = F := by
  refine EnrichedFunctor.ext V (F := (ofEnrichedFunctor F).toEnrichedFunctor) (G := F)
    (fun _ => rfl) ?_
  intro x y
  change MonoidalClosed.curry (MonoidalClosed.uncurry (F.map x y)) ≫ 𝟙 _ = F.map x y
  rw [Category.comp_id, MonoidalClosed.curry_uncurry]

/-- The actual unit map keeps every original value-category identity component. -/
theorem enrichedUnitIso_hom_app (X : WholeRepresentation V C) (x : C) :
    (enrichedUnitIso.hom.app X).app x = 𝟙 (X.obj x) := rfl

/-- The actual inverse unit map keeps every original value-category identity component. -/
theorem enrichedUnitIso_inv_app (X : WholeRepresentation V C) (x : C) :
    (enrichedUnitIso.inv.app X).app x = 𝟙 (X.obj x) := rfl

/-- The actual counit map keeps every original value-category identity component. -/
theorem enrichedCounitIso_hom_app (F : WholeEnrichedFunctor V C) (x : C) :
    (enrichedCounitIso.hom.app F).app x = 𝟙 (F.functor.obj x) := rfl

/-- The actual inverse counit map keeps every original value-category identity component. -/
theorem enrichedCounitIso_inv_app (F : WholeEnrichedFunctor V C) (x : C) :
    (enrichedCounitIso.inv.app F).app x = 𝟙 (F.functor.obj x) := rfl

end CategoryTheory.WholeRepresentation
