/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

/-- Restriction is literal composition of the actual enriched Hom maps. -/
abbrev restrictionObject (j : EnrichedFunctor V A B) (F : EnrichedFunctorCat V B) :
    EnrichedFunctorCat V A := ⟨j.comp V F.toEnrichedFunctor⟩

/-- The actual unit-graded components restrict along the supplied enriched index map. -/
def restrictionMap (j : EnrichedFunctor V A B) {F G : EnrichedFunctorCat V B}
    (t : F ⟶ G) : restrictionObject j F ⟶ restrictionObject j G :=
  GradedNatTrans.unitOfComponents
    (fun a => component t (j.obj a)) (by
      intro a b
      let X := F.toEnrichedFunctor.obj (j.obj a)
      let Y := G.toEnrichedFunctor.obj (j.obj a)
      let H := j.obj a ⟶[V] j.obj b
      let L := a ⟶[V] b
      let q : X ⟶ Y := component t (j.obj a)
      let q' := component t (j.obj b)
      let p : H ⟶ (ihom X).obj (F.toEnrichedFunctor.obj (j.obj b)) :=
        F.toEnrichedFunctor.map (j.obj a) (j.obj b)
      let r : H ⟶ (ihom Y).obj (G.toEnrichedFunctor.obj (j.obj b)) :=
        G.toEnrichedFunctor.map (j.obj a) (j.obj b)
      have h : MonoidalClosed.uncurry p ≫ q' =
          (q ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry r :=
        t.uncurriedNaturality (j.obj a) (j.obj b)
      have hPre := congrArg (fun f => (X ◁ j.map a b) ≫ f) h
      have hExchange :
          (F.toEnrichedFunctor.obj (j.obj a) ◁ j.map a b) ≫
            (component t (j.obj a) ⊗ₘ 𝟙 (j.obj a ⟶[V] j.obj b)) =
          (component t (j.obj a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
            (G.toEnrichedFunctor.obj (j.obj a) ◁ j.map a b) := by
        simpa only [id_tensorHom, tensorHom_id] using
          (whisker_exchange (component t (j.obj a)) (j.map a b))
      change MonoidalClosed.uncurry (j.map a b ≫ F.toEnrichedFunctor.map (j.obj a) (j.obj b)) ≫
          component t (j.obj b) =
        (component t (j.obj a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (j.map a b ≫ G.toEnrichedFunctor.map (j.obj a) (j.obj b))
      rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left]
      simp only [Category.assoc]
      change (X ◁ j.map a b) ≫ MonoidalClosed.uncurry p ≫ q' =
        (q ⊗ₘ 𝟙 L) ≫ (Y ◁ j.map a b) ≫ MonoidalClosed.uncurry r
      have hExchange' : (X ◁ j.map a b) ≫ (q ⊗ₘ 𝟙 H) =
          (q ⊗ₘ 𝟙 L) ≫ (Y ◁ j.map a b) := hExchange
      calc
        _ = (X ◁ j.map a b) ≫
            ((q ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry r) := hPre
        _ = ((q ⊗ₘ 𝟙 L) ≫ (Y ◁ j.map a b)) ≫
            MonoidalClosed.uncurry r :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ MonoidalClosed.uncurry r) hExchange')
        _ = _ := Category.assoc _ _ _)

/-- Restriction retains every entire original ordinary component. -/
theorem restrictionMap_component (j : EnrichedFunctor V A B) {F G : EnrichedFunctorCat V B}
    (t : F ⟶ G) (a : A) :
    component (restrictionMap j t) a = component t (j.obj a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- Precomposition along a genuine enriched index map is a functor on full transformations. -/
abbrev restriction (j : EnrichedFunctor V A B) :
    EnrichedFunctorCat V B ⥤ EnrichedFunctorCat V A where
  obj := restrictionObject j
  map := restrictionMap j
  map_id F := by
    apply hom_ext
    intro a
    have hRight : component (𝟙 (restrictionObject j F)) a =
        𝟙 (F.toEnrichedFunctor.obj (j.obj a)) :=
      component_id (restrictionObject j F) a
    exact ((restrictionMap_component j (𝟙 F) a).trans
      (component_id F (j.obj a))).trans hRight.symm
  map_comp t s := by
    apply hom_ext
    intro a
    have hLeft : component (restrictionMap j (t ≫ s)) a =
        component t (j.obj a) ≫ component s (j.obj a) :=
      (restrictionMap_component j (t ≫ s) a).trans (component_comp t s (j.obj a))
    have hRight : component (restrictionMap j t ≫ restrictionMap j s) a =
        component t (j.obj a) ≫ component s (j.obj a) :=
      (component_comp (restrictionMap j t) (restrictionMap j s) a).trans
        (congrArg₂ (fun f g => f ≫ g)
          (restrictionMap_component j t a) (restrictionMap_component j s a))
    exact hLeft.trans hRight.symm

/-- Restriction keeps the exact original enriched object. -/
theorem restriction_obj (j : EnrichedFunctor V A B) (F : EnrichedFunctorCat V B) (a : A) :
    ((restriction j).obj F).toEnrichedFunctor.obj a = F.toEnrichedFunctor.obj (j.obj a) := rfl

/-- Restriction keeps the exact full Hom map after precomposition. -/
theorem restriction_fullMap (j : EnrichedFunctor V A B) (F : EnrichedFunctorCat V B) (a b : A) :
    ((restriction j).obj F).toEnrichedFunctor.map a b =
      j.map a b ≫ F.toEnrichedFunctor.map (j.obj a) (j.obj b) := rfl

end CategoryTheory.EnrichedFunctorCat
