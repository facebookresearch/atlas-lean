/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence
public import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
public import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation

/-!
# The original full scalar cotensor unit

The scalar unit adjunct and chosen closed unit evaluation give both full enriched
Hom maps, both inverse identities and the whole natural comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.ScalarCotensorUnit

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- The actual original scalar unit is transposed through the full chosen
tensor/cotensor correspondence. -/
def unitMap (F : EnrichedFunctorCat V J) : F ⟶ cotensorObject (𝟙_ V) F :=
  ScalarLeibniz.adjunct (𝟙_ V) F F (scalarUnitIso F).hom

/-- Its entire component is the original chosen closed unit inverse. -/
theorem unitMap_component (F : EnrichedFunctorCat V J) (a : J) :
    component (unitMap F) a =
        (MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)).inv := by
  rw [unitMap, ScalarLeibniz.adjunct_component, scalarUnitIso_hom_component]
  change MonoidalClosed.curry (λ_ (F.toEnrichedFunctor.obj a)).hom =
    MonoidalClosed.unitNatIso.hom.app (F.toEnrichedFunctor.obj a)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry,
    CategoryTheory.EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry]

private theorem counit_fullHom (F : EnrichedFunctorCat V J) (a b : J) :
    MonoidalClosed.uncurry ((cotensorObject (𝟙_ V) F).toEnrichedFunctor.map a b) ≫
        (MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj b)).hom =
      ((MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  let ea := MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)
  let eb := MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj b)
  have h := (unitMap F).uncurriedNaturality a b
  change MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ component (unitMap F) b =
    (component (unitMap F) a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry ((cotensorObject (𝟙_ V) F).toEnrichedFunctor.map a b) at h
  rw [unitMap_component, unitMap_component, tensorHom_id] at h
  change MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ eb.inv =
    (ea.inv ▷ (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry ((cotensorObject (𝟙_ V) F).toEnrichedFunctor.map a b) at h
  rw [tensorHom_id]
  change MonoidalClosed.uncurry ((cotensorObject (𝟙_ V) F).toEnrichedFunctor.map a b) ≫ eb.hom =
    (ea.hom ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
  apply (cancel_epi (ea.inv ▷ (a ⟶[V] b))).mp
  have hPost := congrArg (fun z => z ≫ eb.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp] using hPost.symm

/-- The actual chosen closed unit evaluation defines the full enriched
cotensor counit map, with naturality on every Hom object. -/
@[no_expose]
def counitMap (F : EnrichedFunctorCat V J) : cotensorObject (𝟙_ V) F ⟶ F :=
  GradedNatTrans.unitOfComponents
    (fun a => (MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)).hom)
    (counit_fullHom F)

/-- Its component retains the entire original chosen closed unit evaluation. -/
theorem counitMap_component (F : EnrichedFunctorCat V J) (a : J) :
    component (counitMap F) a = (MonoidalClosed.unitIsoSelf (X := F.toEnrichedFunctor.obj a)).hom :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The full original scalar cotensor at the unit is naturally isomorphic
to the original spectrum, with both actual unit and evaluation maps. -/
def iso (F : EnrichedFunctorCat V J) : cotensorObject (𝟙_ V) F ≅ F where
  hom := counitMap F
  inv := unitMap F
  hom_inv_id := by
    apply hom_ext
    intro a
    rw [component_comp, counitMap_component, unitMap_component, component_id, Iso.hom_inv_id]
  inv_hom_id := by
    apply hom_ext
    intro a
    rw [component_comp, counitMap_component, unitMap_component, component_id, Iso.inv_hom_id]

/-- The entire original closed unit evaluation is natural in every full
native spectrum transformation. -/
theorem naturality {F G : EnrichedFunctorCat V J} (f : F ⟶ G) :
    cotensorMap (𝟙_ V) f ≫ (iso G).hom = (iso F).hom ≫ f := by
  apply hom_ext
  intro a
  change component (cotensorMap (𝟙_ V) f ≫ counitMap G) a =
    component (counitMap F ≫ f) a
  rw [component_comp, component_comp, cotensorMap_component,
    counitMap_component, counitMap_component]
  exact MonoidalClosed.unitNatIso.inv.naturality (component f a)

/-- The original pointwise unit comparison lifts to a whole functor iso. -/
def comparison : cotensor (𝟙_ V) ≅ 𝟭 (EnrichedFunctorCat V J) :=
  NatIso.ofComponents iso (fun f => naturality f)

/-- The full chosen comparison keeps the original left unitor and evaluation. -/
theorem comparison_hom_component (F : EnrichedFunctorCat V J) (a : J) :
    component (comparison.hom.app F) a =
      (λ_ ((ihom (𝟙_ V)).obj (F.toEnrichedFunctor.obj a))).inv ≫
        (ihom.ev (𝟙_ V)).app (F.toEnrichedFunctor.obj a) :=
  (counitMap_component F a).trans
    (MonoidalClosed.UnitEvaluation.forward (F.toEnrichedFunctor.obj a))

/-- The full inverse comparison keeps the original closed transpose of the unit. -/
theorem comparison_inv_component (F : EnrichedFunctorCat V J) (a : J) :
    component (comparison.inv.app F) a =
        MonoidalClosed.curry (λ_ (F.toEnrichedFunctor.obj a)).hom := by
  change component (unitMap F) a = _
  rw [unitMap, ScalarLeibniz.adjunct_component, scalarUnitIso_hom_component]

end CategoryTheory.EnrichedFunctorCat.ScalarCotensorUnit
