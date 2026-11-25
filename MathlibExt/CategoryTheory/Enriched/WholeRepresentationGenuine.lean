/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationEquivalence
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory

/-!
# Whole representations and the original genuine enriched functor category

The original category uses actual unit-graded enriched transformations.
The complete Hom action square gives and recovers that original grading.
Every object, entire enriched Hom map and ordinary component is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  [BraidedCategory V] {C : Type uC} [EnrichedCategory V C]

/-- The actual original unit-graded enriched functor determined by the whole representation. -/
abbrev genuineObject (X : WholeRepresentation V C) : EnrichedFunctorCat V C := ⟨X.toEnrichedFunctor⟩

/-- The actual original unit-graded map retains the entire action square. -/
def genuineMap {X Y : WholeRepresentation V C} (f : X ⟶ Y) : genuineObject X ⟶ genuineObject Y :=
  GradedNatTrans.unitOfComponents f.app (fun x y => by
    change MonoidalClosed.uncurry (MonoidalClosed.curry _) ≫ f.app y =
      (f.app x ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ MonoidalClosed.uncurry (MonoidalClosed.curry _)
    rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry, tensorHom_id]
    exact (f.comm x y).symm)

/-- The unit-graded map has all of the specified original ordinary components. -/
theorem genuineMap_component {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    EnrichedFunctorCat.component (genuineMap f) x = f.app x :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- Currying keeps the actual original functor and every genuine unit-graded map. -/
def toGenuineFunctors : WholeRepresentation V C ⥤ EnrichedFunctorCat V C where
  obj := genuineObject
  map := genuineMap
  map_id X := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    rw [genuineMap_component, EnrichedFunctorCat.component_id]
    rfl
  map_comp f g := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    rw [EnrichedFunctorCat.component_comp, genuineMap_component, genuineMap_component,
      genuineMap_component]
    rfl

/-- The full uncurried representation of the actual original enriched functor and transformation. -/
def fromGenuineFunctors : EnrichedFunctorCat V C ⥤ WholeRepresentation V C where
  obj F := ofEnrichedFunctor F.toEnrichedFunctor
  map f :=
    { app := EnrichedFunctorCat.component f
      comm x y := by
        change EnrichedFunctorCat.component f x ▷ (x ⟶[V] y) ≫
          MonoidalClosed.uncurry _ = MonoidalClosed.uncurry _ ≫ EnrichedFunctorCat.component f y
        simpa only [tensorHom_id] using (f.uncurriedNaturality x y).symm }
  map_id F := by
    apply hom_ext
    intro x
    exact EnrichedFunctorCat.component_id F x
  map_comp f g := by
    apply hom_ext
    intro x
    exact EnrichedFunctorCat.component_comp f g x

/-- The whole object function is retained in the actual original enriched category. -/
theorem toGenuineFunctors_obj (X : WholeRepresentation V C) (x : C) :
    (toGenuineFunctors.obj X).toEnrichedFunctor.obj x = X.obj x := rfl

/-- Every original enriched Hom map is the actual original action transpose. -/
theorem toGenuineFunctors_map (X : WholeRepresentation V C) (x y : C) :
    (toGenuineFunctors.obj X).toEnrichedFunctor.map x y = MonoidalClosed.curry (X.action x y) := rfl

/-- Every original component is retained by the genuine unit-graded transformation. -/
theorem toGenuineFunctors_map_component {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    EnrichedFunctorCat.component (toGenuineFunctors.map f) x = f.app x :=
  genuineMap_component f x

/-- The original component is retained by the complete uncurried representation. -/
theorem fromGenuineFunctors_map_app {F G : EnrichedFunctorCat V C} (f : F ⟶ G) (x : C) :
    (fromGenuineFunctors.map f).app x = EnrichedFunctorCat.component f x := rfl

/-- Identity components recover the complete original whole representation. -/
def genuineUnitIsoApp (X : WholeRepresentation V C) :
    X ≅ fromGenuineFunctors.obj (toGenuineFunctors.obj X) := enrichedUnitIsoApp X

/-- The counit is the actual original unit-graded identity-component map. -/
def genuineCounitHom (F : EnrichedFunctorCat V C) :
    toGenuineFunctors.obj (fromGenuineFunctors.obj F) ⟶ F :=
  GradedNatTrans.unitOfComponents (fun x => 𝟙 (F.toEnrichedFunctor.obj x)) (fun x y => by
    change MonoidalClosed.uncurry
        (MonoidalClosed.curry (MonoidalClosed.uncurry (F.toEnrichedFunctor.map x y))) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map x y)
    simp)

/-- The inverse counit retains the actual original unit-graded identity components. -/
def genuineCounitInv (F : EnrichedFunctorCat V C) :
    F ⟶ toGenuineFunctors.obj (fromGenuineFunctors.obj F) :=
  GradedNatTrans.unitOfComponents (fun x => 𝟙 (F.toEnrichedFunctor.obj x)) (fun x y => by
    change MonoidalClosed.uncurry (F.toEnrichedFunctor.map x y) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ MonoidalClosed.uncurry
        (MonoidalClosed.curry (MonoidalClosed.uncurry (F.toEnrichedFunctor.map x y)))
    simp)

/-- Every ordinary counit component is the original identity map. -/
theorem genuineCounitHom_component (F : EnrichedFunctorCat V C) (x : C) :
    EnrichedFunctorCat.component (genuineCounitHom F) x = 𝟙 (F.toEnrichedFunctor.obj x) :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- Every ordinary inverse counit component is the original identity map. -/
theorem genuineCounitInv_component (F : EnrichedFunctorCat V C) (x : C) :
    EnrichedFunctorCat.component (genuineCounitInv F) x = 𝟙 (F.toEnrichedFunctor.obj x) :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- Identity components recover the actual enriched functor and original unit-graded maps. -/
def genuineCounitIsoApp (F : EnrichedFunctorCat V C) :
    toGenuineFunctors.obj (fromGenuineFunctors.obj F) ≅ F where
  hom := genuineCounitHom F
  inv := genuineCounitInv F
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    rw [EnrichedFunctorCat.component_comp, genuineCounitHom_component, genuineCounitInv_component,
      EnrichedFunctorCat.component_id]
    exact Category.id_comp _
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    rw [EnrichedFunctorCat.component_comp, genuineCounitHom_component, genuineCounitInv_component,
      EnrichedFunctorCat.component_id]
    exact Category.id_comp _

/-- The unit retains all original identity components. -/
theorem genuineUnitIsoApp_hom_app (X : WholeRepresentation V C) (x : C) :
    (genuineUnitIsoApp X).hom.app x = 𝟙 (X.obj x) := rfl

/-- The counit retains all original ordinary identity components of the genuine transformation. -/
theorem genuineCounitIsoApp_hom_component (F : EnrichedFunctorCat V C) (x : C) :
    EnrichedFunctorCat.component (genuineCounitIsoApp F).hom x = 𝟙 (F.toEnrichedFunctor.obj x) :=
  genuineCounitHom_component F x

/-- The complete unit is natural in every original whole transformation. -/
def genuineUnitIso : 𝟭 (WholeRepresentation V C) ≅ toGenuineFunctors ⋙ fromGenuineFunctors :=
  NatIso.ofComponents genuineUnitIsoApp (fun f => by
    apply hom_ext
    intro x
    change f.app x ≫ 𝟙 _ = 𝟙 _ ≫ EnrichedFunctorCat.component (toGenuineFunctors.map f) x
    rw [toGenuineFunctors_map_component]
    exact (Category.comp_id (f.app x)).trans (Category.id_comp (f.app x)).symm)

/-- The complete counit is natural in every actual original unit-graded transformation. -/
def genuineCounitIso : fromGenuineFunctors ⋙ toGenuineFunctors ≅ 𝟭 (EnrichedFunctorCat V C) :=
  NatIso.ofComponents genuineCounitIsoApp (fun {F G} f => by
    apply EnrichedFunctorCat.hom_ext
    intro x
    change EnrichedFunctorCat.component
        (toGenuineFunctors.map (fromGenuineFunctors.map f) ≫ genuineCounitHom G) x =
      EnrichedFunctorCat.component (genuineCounitHom F ≫ f) x
    have hm : EnrichedFunctorCat.component
        (toGenuineFunctors.map (fromGenuineFunctors.map f)) x = EnrichedFunctorCat.component f x :=
      (toGenuineFunctors_map_component (fromGenuineFunctors.map f) x).trans
        (fromGenuineFunctors_map_app f x)
    have hl := (EnrichedFunctorCat.component_comp
        (toGenuineFunctors.map (fromGenuineFunctors.map f)) (genuineCounitHom G) x).trans
      ((congrArg₂ (fun a b => a ≫ b) hm (genuineCounitHom_component G x)).trans
        (Category.comp_id _))
    have hr := (EnrichedFunctorCat.component_comp (genuineCounitHom F) f x).trans
      ((congrArg (fun t => t ≫ EnrichedFunctorCat.component f x)
        (genuineCounitHom_component F x)).trans
        (Category.id_comp _))
    exact hl.trans hr.symm)

/-- The complete equivalence with the actual original enriched functor category. -/
def genuineEquivalence : WholeRepresentation V C ≌ EnrichedFunctorCat V C where
  functor := toGenuineFunctors
  inverse := fromGenuineFunctors
  unitIso := genuineUnitIso
  counitIso := genuineCounitIso
  functor_unitIso_comp X := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    change EnrichedFunctorCat.component
        (toGenuineFunctors.map (genuineUnitIsoApp X).hom
          ≫ genuineCounitHom (toGenuineFunctors.obj X)) x =
      EnrichedFunctorCat.component (𝟙 (toGenuineFunctors.obj X)) x
    have hu : EnrichedFunctorCat.component (toGenuineFunctors.map (genuineUnitIsoApp X).hom) x =
        𝟙 (X.obj x) := (toGenuineFunctors_map_component _ x).trans (genuineUnitIsoApp_hom_app X x)
    have hc : EnrichedFunctorCat.component (genuineCounitHom (toGenuineFunctors.obj X)) x =
        𝟙 (X.obj x) := genuineCounitHom_component _ x
    have hi : EnrichedFunctorCat.component (𝟙 (toGenuineFunctors.obj X)) x = 𝟙 (X.obj x) :=
      EnrichedFunctorCat.component_id _ _
    exact (EnrichedFunctorCat.component_comp _ _ x).trans
      ((congrArg₂ (fun a b => a ≫ b) hu hc).trans ((Category.id_comp _).trans hi.symm))

/-- The actual enriched functor is recovered with its complete original Hom maps. -/
theorem genuineEquivalence_toEnrichedFunctor (F : EnrichedFunctorCat V C) :
    (genuineEquivalence.functor.obj (genuineEquivalence.inverse.obj F)).toEnrichedFunctor =
      F.toEnrichedFunctor := to_of F.toEnrichedFunctor

/-- The entire original representation is recovered through the genuine category. -/
theorem genuineEquivalence_representation (X : WholeRepresentation V C) :
    genuineEquivalence.inverse.obj (genuineEquivalence.functor.obj X) = X := of_to X

end CategoryTheory.WholeRepresentation
