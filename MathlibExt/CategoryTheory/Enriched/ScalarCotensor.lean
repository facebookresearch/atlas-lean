/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition
public import MathlibExt.CategoryTheory.Enriched.GradeNaturality
public import MathlibExt.CategoryTheory.Enriched.GradedComponentActions

/-!
# Pointwise enriched cotensors and their graded Hom correspondence

The objects and full Hom maps are the original closed self-representable
composition. Genuine unit transformations define the functor, actual closed
pre-maps define coefficient variance, and the supplied center half-braidings
define the full graded correspondence. Both index universes remain independent.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uI uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- This is the original self-representable composition, with its literal object projection. -/
abbrev cotensor (M : V) (G : EnrichedFunctor V I V) :
    EnrichedFunctor V I V :=
  let R := G.comp V (EnrichedFunctor.covariantRepresentable V V M)
  { obj := fun a => (ihom M).obj (G.obj a)
    map := fun a b => R.map a b
    map_id := fun a => R.map_id a
    map_comp := fun a b c => R.map_comp a b c }


set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensor_eq (M : V) (G : EnrichedFunctor V I V) :
    cotensor M G =
      G.comp V (EnrichedFunctor.covariantRepresentable V V M) := rfl


set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensor_map (M : V) (G : EnrichedFunctor V I V) (a b : I) :
    (cotensor M G).map a b =
      G.map a b ≫ MonoidalClosed.curry (eComp V M (G.obj a) (G.obj b)) := rfl


set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensor_doubleUncurry
    (M : V) (G : EnrichedFunctor V I V) (a b : I) :
    MonoidalClosed.uncurry (A := M)
        (MonoidalClosed.uncurry ((cotensor M G).map a b)) =
      (α_ M ((ihom M).obj (G.obj a)) (a ⟶[V] b)).inv ≫
        ((ihom.ev M).app (G.obj a) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.map a b) := by
  rw [cotensor_map, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  rw [← id_tensorHom]
  change MonoidalClosed.uncurry
      ((𝟙 ((ihom M).obj (G.obj a)) ⊗ₘ G.map a b) ≫ eComp V M (G.obj a) (G.obj b)) = _
  rw [MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_id_eq_ev]


end CategoryTheory.EnrichedFunctor

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]

section CotensorComponents
variable {I : Type uI} [EnrichedCategory V I]
set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] in
/-- The pointwise cotensor regarded as an object of the enriched functor category. -/
abbrev cotensorObject (M : V) (G : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I :=
  ⟨EnrichedFunctor.cotensor M G.toEnrichedFunctor⟩


set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] in
theorem cotensorComponents_natural
    (M : V) (F G : EnrichedFunctor V I V)
    (q : ∀ a, M ⊗ F.obj a ⟶ G.obj a)
    (hq : ∀ a b,
      (α_ M (F.obj a) (a ⟶[V] b)).hom ≫
          (M ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
        (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b))
    (a b : I) :
    MonoidalClosed.uncurry (F.map a b) ≫ MonoidalClosed.curry (q b) =
      (MonoidalClosed.curry (q a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M G).map a b) := by
  apply MonoidalClosed.uncurry_injective (A := M)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left, EnrichedFunctor.cotensor_doubleUncurry,
    tensorHom_id]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  have h := congrArg (fun t => (α_ M (F.obj a) (a ⟶[V] b)).inv ≫ t) (hq a b)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Construct the genuine cotensor morphism from its full left-coefficient components. -/
@[no_expose]
def cotensorOfLeftComponents
    (M : V) (F G : EnrichedFunctorCat V I)
    (q : ∀ a, M ⊗ F.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a)
    (hq : ∀ a b,
      (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          (M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫ q b =
        (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b)) :
    F ⟶ cotensorObject M G :=
  GradedNatTrans.unitOfComponents (fun a => MonoidalClosed.curry (q a))
    (cotensorComponents_natural M F.toEnrichedFunctor G.toEnrichedFunctor q hq)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorOfLeftComponents_component
    (M : V) (F G : EnrichedFunctorCat V I)
    (q : ∀ a, M ⊗ F.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a)
    (hq : ∀ a b,
      (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          (M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫ q b =
        (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b))
    (a : I) :
    component (cotensorOfLeftComponents M F G q hq) a =
      MonoidalClosed.curry (q a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The component of a morphism to the pointwise cotensor, as an internal-Hom map. -/
abbrev cotensorComponent
    (M : V) {F G : EnrichedFunctorCat V I} (t : F ⟶ cotensorObject M G)
    (a : I) : F.toEnrichedFunctor.obj a ⟶ (ihom M).obj (G.toEnrichedFunctor.obj a) :=
  component t a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorComponent_naturality
    (M : V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject M G)
    (a b : I) :
    (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        (M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫
        MonoidalClosed.uncurry (cotensorComponent M t b) =
      (MonoidalClosed.uncurry (cotensorComponent M t a) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) := by
  have hn :
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫
          cotensorComponent M t b =
        (cotensorComponent M t a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M G.toEnrichedFunctor).map a b) :=
    t.uncurriedNaturality a b
  have hu := congrArg (MonoidalClosed.uncurry (A := M)) hn
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    EnrichedFunctor.cotensor_doubleUncurry, tensorHom_id,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    ← MonoidalClosed.uncurry_eq] at hu
  have h := congrArg (fun q => (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫ q) hu
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorOfLeftComponents_reconstruct
    (M : V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject M G) :
    cotensorOfLeftComponents M F G
      (fun a => MonoidalClosed.uncurry (cotensorComponent M t a))
      (cotensorComponent_naturality M F G t) = t := by
  apply hom_ext
  intro a
  rw [cotensorOfLeftComponents_component, MonoidalClosed.curry_uncurry]

end CotensorComponents


/-! Actual pointwise cotensor functor and coefficient maps. -/

section CotensorFunctoriality
variable {I : Type uI} [EnrichedCategory V I]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorMap_leftComponents_natural
    (M : V) {F G : EnrichedFunctorCat V I} (t : F ⟶ G) (a b : I) :
    (α_ M ((ihom M).obj (F.toEnrichedFunctor.obj a)) (a ⟶[V] b)).hom ≫
        (M ◁ MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M F.toEnrichedFunctor).map a b)) ≫
        ((ihom.ev M).app (F.toEnrichedFunctor.obj b) ≫ component t b) =
      (((ihom.ev M).app (F.toEnrichedFunctor.obj a) ≫ component t a) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) := by
  have he := congrArg
    (fun p => (α_ M ((ihom M).obj (F.toEnrichedFunctor.obj a)) (a ⟶[V] b)).hom ≫ p)
    (EnrichedFunctor.cotensor_doubleUncurry M F.toEnrichedFunctor a b)
  rw [MonoidalClosed.uncurry_eq] at he
  have hEval :
      (α_ M ((ihom M).obj (F.toEnrichedFunctor.obj a)) (a ⟶[V] b)).hom ≫
          (M ◁ MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M F.toEnrichedFunctor).map a b)) ≫
          (ihom.ev M).app (F.toEnrichedFunctor.obj b) =
        ((ihom.ev M).app (F.toEnrichedFunctor.obj a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he
  have ht := congrArg
    (fun p => ((ihom.ev M).app (F.toEnrichedFunctor.obj a) ▷ (a ⟶[V] b)) ≫ p)
    (t.uncurriedNaturality a b)
  calc
    _ = ((ihom.ev M).app (F.toEnrichedFunctor.obj a) ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ component t b := by
      simpa only [Category.assoc] using congrArg (fun p => p ≫ component t b) hEval
    _ = _ := by
      simpa only [Category.assoc, tensorHom_id, comp_whiskerRight] using ht

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The pointwise internal-Hom map is a genuine transformation on the full index Hom objects. -/
@[no_expose]
def cotensorMap (M : V) {F G : EnrichedFunctorCat V I} (t : F ⟶ G) :
    cotensorObject M F ⟶ cotensorObject M G :=
  cotensorOfLeftComponents M (cotensorObject M F) G
    (fun a => (ihom.ev M).app (F.toEnrichedFunctor.obj a) ≫ component t a)
    (cotensorMap_leftComponents_natural M t)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorMap_component_private
    (M : V) {F G : EnrichedFunctorCat V I} (t : F ⟶ G) (a : I) :
    component (cotensorMap M t) a = (ihom M).map (component t a) := by
  change component
    (cotensorOfLeftComponents M (cotensorObject M F) G
      (fun a => (ihom.ev M).app (F.toEnrichedFunctor.obj a) ≫ component t a)
      (cotensorMap_leftComponents_natural M t)) a = _
  rw [cotensorOfLeftComponents_component, MonoidalClosed.curry_natural_right]
  have hid : MonoidalClosed.curry ((ihom.ev M).app (F.toEnrichedFunctor.obj a)) =
      𝟙 ((ihom M).obj (F.toEnrichedFunctor.obj a)) :=
    (congrArg MonoidalClosed.curry
      (MonoidalClosed.uncurry_id_eq_ev M (F.toEnrichedFunctor.obj a)).symm).trans
        (MonoidalClosed.curry_uncurry (𝟙 ((ihom M).obj (F.toEnrichedFunctor.obj a))))
  exact (congrArg (fun p => p ≫ (ihom M).map (component t a)) hid).trans (Category.id_comp _)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Cotensor functor maps keep the actual original internal-Hom map. -/
theorem cotensorMap_component
    (M : V) {F G : EnrichedFunctorCat V I} (t : F ⟶ G) (a : I) :
    component (cotensorMap M t) a = (ihom M).map (component t a) :=
  cotensorMap_component_private M t a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The original self-representable gives the pointwise cotensor functor on genuine diagrams. -/
abbrev cotensor (M : V) : EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I where
  obj := cotensorObject M
  map := cotensorMap M
  map_id F := by
    apply hom_ext
    intro a
    exact ((cotensorMap_component M (𝟙 F) a).trans
      (congrArg (fun p => (ihom M).map p) (component_id F a))).trans
        (((ihom M).map_id (F.toEnrichedFunctor.obj a)).trans
          (component_id (cotensorObject M F) a).symm)
  map_comp t s := by
    apply hom_ext
    intro a
    have hL : component (cotensorMap M (t ≫ s)) a =
        (ihom M).map (component t a) ≫ (ihom M).map (component s a) :=
      ((cotensorMap_component M (t ≫ s) a).trans
        (congrArg (fun p => (ihom M).map p) (component_comp t s a))).trans
          ((ihom M).map_comp (component t a) (component s a))
    have hR : component (cotensorMap M t ≫ cotensorMap M s) a =
        (ihom M).map (component t a) ≫ (ihom M).map (component s a) :=
      (component_comp (cotensorMap M t) (cotensorMap M s) a).trans
        (congrArg₂ (fun p q => p ≫ q)
          (cotensorMap_component M t a) (cotensorMap_component M s a))
    exact hL.trans hR.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Coefficient maps come from genuine enriched Yoneda and the original restriction. -/
@[no_expose]
def cotensorScalarMap {M N : V} (u : M ⟶ N) (F : EnrichedFunctorCat V I) :
    cotensorObject N F ⟶ cotensorObject M F :=
  restrictionMap F.toEnrichedFunctor
    (GradedYoneda.extend N (GradedYoneda.representable M) (eHomEquiv V u) :
      (⟨GradedYoneda.representable N⟩ : EnrichedFunctorCat V V) ⟶
        ⟨GradedYoneda.representable M⟩)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorScalarMap_component_private
    {M N : V} (u : M ⟶ N) (F : EnrichedFunctorCat V I) (a : I) :
    component (cotensorScalarMap u F) a =
      (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) := by
  have hEval : GradedYoneda.component N (GradedYoneda.representable M)
      (eHomEquiv V u) (F.toEnrichedFunctor.obj a) =
        (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) := by
    dsimp only [GradedYoneda.component]
    rw [GradedYoneda.representable_uncurry, tensorHom_id]
    have h := MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight
      V u (F.toEnrichedFunctor.obj a)
    change (λ_ ((ihom N).obj (F.toEnrichedFunctor.obj a))).inv ≫
      eHomEquiv V u ▷ ((ihom N).obj (F.toEnrichedFunctor.obj a)) ≫
        eComp V M N (F.toEnrichedFunctor.obj a) = _ at h
    exact h
  exact (restrictionMap_component F.toEnrichedFunctor
    (GradedYoneda.extend N (GradedYoneda.representable M) (eHomEquiv V u) :
      (⟨GradedYoneda.representable N⟩ : EnrichedFunctorCat V V) ⟶
        ⟨GradedYoneda.representable M⟩) a).trans
      ((GradedYoneda.extend_component N (GradedYoneda.representable M)
        (eHomEquiv V u) (F.toEnrichedFunctor.obj a)).trans hEval)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Contravariant coefficient maps are exactly the existing closed precomposition maps. -/
theorem cotensorScalarMap_component
    {M N : V} (u : M ⟶ N) (F : EnrichedFunctorCat V I) (a : I) :
    component (cotensorScalarMap u F) a =
      (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) :=
  cotensorScalarMap_component_private u F a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorScalarMap_id (M : V) (F : EnrichedFunctorCat V I) :
    cotensorScalarMap (𝟙 M) F = 𝟙 (cotensorObject M F) := by
  apply hom_ext
  intro a
  exact (cotensorScalarMap_component (𝟙 M) F a).trans
    ((congrArg (fun p => p.app (F.toEnrichedFunctor.obj a))
      (MonoidalClosed.pre_id M)).trans (component_id (cotensorObject M F) a).symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorScalarMap_comp {M N P : V}
    (u : M ⟶ N) (v : N ⟶ P) (F : EnrichedFunctorCat V I) :
    cotensorScalarMap (u ≫ v) F = cotensorScalarMap v F ≫ cotensorScalarMap u F := by
  apply hom_ext
  intro a
  have hL : component (cotensorScalarMap (u ≫ v) F) a =
      (MonoidalClosed.pre v).app (F.toEnrichedFunctor.obj a) ≫
        (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) :=
    (cotensorScalarMap_component (u ≫ v) F a).trans
      (congrArg (fun p => p.app (F.toEnrichedFunctor.obj a)) (MonoidalClosed.pre_map u v))
  have hR : component (cotensorScalarMap v F ≫ cotensorScalarMap u F) a =
      (MonoidalClosed.pre v).app (F.toEnrichedFunctor.obj a) ≫
        (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) :=
    (component_comp (cotensorScalarMap v F) (cotensorScalarMap u F) a).trans
      (congrArg₂ (fun p q => p ≫ q)
        (cotensorScalarMap_component v F a) (cotensorScalarMap_component u F a))
  exact hL.trans hR.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Coefficient precomposition commutes with genuine diagram maps. -/
theorem cotensorScalarMap_naturality {M N : V} (u : M ⟶ N)
    {F G : EnrichedFunctorCat V I} (t : F ⟶ G) :
    cotensorMap N t ≫ cotensorScalarMap u G =
      cotensorScalarMap u F ≫ cotensorMap M t := by
  apply hom_ext
  intro a
  have hL := (component_comp (cotensorMap N t) (cotensorScalarMap u G) a).trans
    (congrArg₂ (fun p q => p ≫ q)
      (cotensorMap_component N t a) (cotensorScalarMap_component u G a))
  have hR := (component_comp (cotensorScalarMap u F) (cotensorMap M t) a).trans
    (congrArg₂ (fun p q => p ≫ q)
      (cotensorScalarMap_component u F a) (cotensorMap_component M t a))
  exact hL.trans (((MonoidalClosed.pre u).naturality (component t a)).trans hR.symm)

end CotensorFunctoriality


/-! Actual central grades and their pointwise cotensor Hom correspondence. -/

section GradedCotensorComponents
variable {I : Type uI} [EnrichedCategory V I]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Turn a Center-graded natural transformation into a morphism to the pointwise
cotensor by currying its grade-first components. -/
@[no_expose]
def gradedToCotensor
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    F ⟶ cotensorObject Γ.1 G :=
  cotensorOfLeftComponents Γ.1 F G
    (GradedNatTrans.gradeFirstComponent Γ t)
    (GradedNatTrans.gradeFirstComponent_naturality Γ t)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem gradedToCotensor_component
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (a : I) :
    component (gradedToCotensor Γ F G t) a =
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) :=
  cotensorOfLeftComponents_component _ _ _ _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Recover a Center-graded natural transformation from a morphism to the pointwise
cotensor by uncurrying and applying the inverse half-braiding. -/
@[no_expose]
def cotensorToGraded
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : F ⟶ cotensorObject Γ.1 G) :
    GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor :=
  GradedNatTrans.ofGradeFirstComponents Γ
    (fun a => MonoidalClosed.uncurry (cotensorComponent Γ.1 t a))
    (cotensorComponent_naturality Γ.1 F G t)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_app
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : F ⟶ cotensorObject Γ.1 G) (a : I) :
    (cotensorToGraded Γ F G t).app a =
      MonoidalClosed.curry ((Γ.2.β (F.toEnrichedFunctor.obj a)).inv ≫
        MonoidalClosed.uncurry (cotensorComponent Γ.1 t a)) :=
  GradedNatTrans.ofGradeFirstComponents_app _ _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_gradeFirst
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : F ⟶ cotensorObject Γ.1 G) (a : I) :
    GradedNatTrans.gradeFirstComponent Γ (cotensorToGraded Γ F G t) a =
      MonoidalClosed.uncurry (cotensorComponent Γ.1 t a) :=
  GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent _ _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_toCotensor
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    cotensorToGraded Γ F G (gradedToCotensor Γ F G t) = t := by
  apply GradedNatTrans.gradeFirstComponent_ext Γ
  intro a
  rw [cotensorToGraded_gradeFirst]
  have ht : cotensorComponent Γ.1 (gradedToCotensor Γ F G t) a =
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) :=
    gradedToCotensor_component Γ F G t a
  rw [ht, MonoidalClosed.uncurry_curry]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem gradedToCotensor_fromCotensor
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : F ⟶ cotensorObject Γ.1 G) :
    gradedToCotensor Γ F G (cotensorToGraded Γ F G t) = t := by
  apply hom_ext
  intro a
  rw [gradedToCotensor_component, cotensorToGraded_gradeFirst,
    MonoidalClosed.curry_uncurry]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The inverse correspondence between Center-graded natural transformations and
morphisms to the pointwise cotensor by the underlying grade object. -/
@[no_expose]
def gradedCotensorEquiv
    (Γ : Center V) (F G : EnrichedFunctorCat V I) :
    GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor ≃
      (F ⟶ cotensorObject Γ.1 G) where
  toFun := gradedToCotensor Γ F G
  invFun := cotensorToGraded Γ F G
  left_inv := cotensorToGraded_toCotensor Γ F G
  right_inv := gradedToCotensor_fromCotensor Γ F G

end GradedCotensorComponents

/-! Full input and coefficient naturalities of the genuine graded cotensor correspondence. -/

section CotensorGradedNaturality
variable {I : Type uI} [EnrichedCategory V I]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem gradedCotensorEquiv_apply_private
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedCotensorEquiv Γ F G t = gradedToCotensor Γ F G t := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem gradedCotensorEquiv_apply
    (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedCotensorEquiv Γ F G t = gradedToCotensor Γ F G t :=
  gradedCotensorEquiv_apply_private Γ F G t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem gradedCotensorEquiv_symm_apply_private
    (Γ : Center V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject Γ.1 G) :
    (gradedCotensorEquiv Γ F G).symm t = cotensorToGraded Γ F G t := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem gradedCotensorEquiv_symm_apply
    (Γ : Center V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject Γ.1 G) :
    (gradedCotensorEquiv Γ F G).symm t = cotensorToGraded Γ F G t :=
  gradedCotensorEquiv_symm_apply_private Γ F G t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensor_gradeFirst_precomp
    (Γ : Center V) {F G H : EnrichedFunctorCat V I} (p : F ⟶ G)
    (t : GradedNatTrans Γ G.toEnrichedFunctor H.toEnrichedFunctor) (a : I) :
    GradedNatTrans.gradeFirstComponent Γ (gradedPrecomp Γ p t) a =
      (Γ.1 ◁ component p a) ≫ GradedNatTrans.gradeFirstComponent Γ t a := by
  have h := congrArg
    (fun x => (Γ.2.β (F.toEnrichedFunctor.obj a)).hom ≫ MonoidalClosed.uncurry x)
    (gradedPrecomp_app Γ p t a)
  have hu := MonoidalClosed.uncurry_pre_app
    (C := V) (X := H.toEnrichedFunctor.obj a) (t.app a) (component p a)
  exact h.trans
    ((congrArg (fun x => (Γ.2.β (F.toEnrichedFunctor.obj a)).hom ≫ x) hu).trans
      (HalfBraiding.naturality_assoc Γ.2 (component p a) (MonoidalClosed.uncurry (t.app a))).symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Genuine source composition is the original source composition under cotensor currying. -/
theorem gradedToCotensor_precomp
    (Γ : Center V) {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedToCotensor Γ F' G (gradedPrecomp Γ p t) = p ≫ gradedToCotensor Γ F G t := by
  apply hom_ext
  intro a
  have hL : component (gradedToCotensor Γ F' G (gradedPrecomp Γ p t)) a =
      component p a ≫ MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) :=
    (gradedToCotensor_component Γ F' G (gradedPrecomp Γ p t) a).trans
      ((congrArg MonoidalClosed.curry (cotensor_gradeFirst_precomp Γ p t a)).trans
        (MonoidalClosed.curry_natural_left (component p a)
          (GradedNatTrans.gradeFirstComponent Γ t a)))
  have hR : component (p ≫ gradedToCotensor Γ F G t) a =
      component p a ≫ MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) :=
    (component_comp p (gradedToCotensor Γ F G t) a).trans
      (congrArg (fun x => component p a ≫ x) (gradedToCotensor_component Γ F G t a))
  exact hL.trans hR.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Genuine target composition is the actual pointwise cotensor functor map under currying. -/
theorem gradedToCotensor_postcomp
    (Γ : Center V) {F G H : EnrichedFunctorCat V I}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) :
    gradedToCotensor Γ F H (gradedPostcomp Γ t q) =
      gradedToCotensor Γ F G t ≫ cotensorMap Γ.1 q := by
  apply hom_ext
  intro a
  have hL : component (gradedToCotensor Γ F H (gradedPostcomp Γ t q)) a =
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) ≫
        (ihom Γ.1).map (component q a) :=
    (gradedToCotensor_component Γ F H (gradedPostcomp Γ t q) a).trans
      ((congrArg MonoidalClosed.curry (gradeFirstComponent_gradedPostcomp Γ t q a)).trans
        (MonoidalClosed.curry_natural_right
          (GradedNatTrans.gradeFirstComponent Γ t a) (component q a)))
  have hR : component (gradedToCotensor Γ F G t ≫ cotensorMap Γ.1 q) a =
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t a) ≫
        (ihom Γ.1).map (component q a) :=
    (component_comp (gradedToCotensor Γ F G t) (cotensorMap Γ.1 q) a).trans
      (congrArg₂ (fun x y => x ≫ y)
        (gradedToCotensor_component Γ F G t a) (cotensorMap_component Γ.1 q a))
  exact hL.trans hR.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_precomp
    (Γ : Center V) {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    (t : F ⟶ cotensorObject Γ.1 G) :
    cotensorToGraded Γ F' G (p ≫ t) = gradedPrecomp Γ p (cotensorToGraded Γ F G t) := by
  apply (gradedCotensorEquiv Γ F' G).injective
  rw [gradedCotensorEquiv_apply, gradedCotensorEquiv_apply,
    gradedToCotensor_fromCotensor, gradedToCotensor_precomp, gradedToCotensor_fromCotensor]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_postcomp
    (Γ : Center V) {F G H : EnrichedFunctorCat V I}
    (t : F ⟶ cotensorObject Γ.1 G) (q : G ⟶ H) :
    cotensorToGraded Γ F H (t ≫ cotensorMap Γ.1 q) =
      gradedPostcomp Γ (cotensorToGraded Γ F G t) q := by
  apply (gradedCotensorEquiv Γ F H).injective
  rw [gradedCotensorEquiv_apply, gradedCotensorEquiv_apply,
    gradedToCotensor_fromCotensor, gradedToCotensor_postcomp, gradedToCotensor_fromCotensor]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Every genuine morphism in the center corresponds to original closed coefficient
precomposition. -/
theorem gradedToCotensor_regrade
    {Γ Γ' : Center V} (u : Γ ⟶ Γ') (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedToCotensor Γ F G (GradedNatTrans.regrade u t) =
      gradedToCotensor Γ' F G t ≫ cotensorScalarMap u.f G := by
  apply hom_ext
  intro a
  have hL : component (gradedToCotensor Γ F G (GradedNatTrans.regrade u t)) a =
      MonoidalClosed.curry ((u.f ▷ F.toEnrichedFunctor.obj a) ≫
        GradedNatTrans.gradeFirstComponent Γ' t a) :=
    (gradedToCotensor_component Γ F G (GradedNatTrans.regrade u t) a).trans
      (congrArg MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent_regrade Γ u t a))
  have hPre := MonoidalClosed.curry_pre_app
    (C := V) (X := G.toEnrichedFunctor.obj a) u.f
      (GradedNatTrans.gradeFirstComponent Γ' t a)
  have hR : component (gradedToCotensor Γ' F G t ≫ cotensorScalarMap u.f G) a =
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ' t a) ≫
        (MonoidalClosed.pre u.f).app (G.toEnrichedFunctor.obj a) :=
    (component_comp (gradedToCotensor Γ' F G t) (cotensorScalarMap u.f G) a).trans
      (congrArg₂ (fun x y => x ≫ y)
        (gradedToCotensor_component Γ' F G t a) (cotensorScalarMap_component u.f G a))
  exact hL.trans (hPre.symm.trans hR.symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorToGraded_regrade
    {Γ Γ' : Center V} (u : Γ ⟶ Γ') (F G : EnrichedFunctorCat V I)
    (t : F ⟶ cotensorObject Γ'.1 G) :
    cotensorToGraded Γ F G (t ≫ cotensorScalarMap u.f G) =
      GradedNatTrans.regrade u (cotensorToGraded Γ' F G t) := by
  apply (gradedCotensorEquiv Γ F G).injective
  rw [gradedCotensorEquiv_apply, gradedCotensorEquiv_apply,
    gradedToCotensor_fromCotensor, gradedToCotensor_regrade, gradedToCotensor_fromCotensor]

end CotensorGradedNaturality


variable {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
section CotensorRestriction

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
@[no_expose]
private def cotensorRestrictionHom
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) :
    cotensorObject M (restrictionObject j Y) ⟶
      restrictionObject j (cotensorObject M Y) :=
  GradedNatTrans.unitOfComponents
    (fun a => 𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))) (by
      intro a a'
      change MonoidalClosed.uncurry
          ((j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) ≫
            MonoidalClosed.curry (eComp V M
              (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a')))) ≫
            𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a'))) =
        (𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
          MonoidalClosed.uncurry
          (j.map a a' ≫ (Y.toEnrichedFunctor.map (j.obj a) (j.obj a') ≫
            MonoidalClosed.curry (eComp V M
              (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a')))))
      simp only [id_tensorHom_id, Category.id_comp]
      exact (Category.comp_id (MonoidalClosed.uncurry
        ((j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) ≫
          MonoidalClosed.curry (eComp V M
            (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a')))))).trans
        (congrArg MonoidalClosed.uncurry (Category.assoc
        (j.map a a') (Y.toEnrichedFunctor.map (j.obj a) (j.obj a'))
        (MonoidalClosed.curry (eComp V M
          (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a')))))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorRestrictionHom_component
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionHom j M Y) a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
@[no_expose]
private def cotensorRestrictionInv
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) :
    restrictionObject j (cotensorObject M Y) ⟶
      cotensorObject M (restrictionObject j Y) :=
  GradedNatTrans.unitOfComponents
    (fun a => 𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))) (by
      intro a a'
      change MonoidalClosed.uncurry
          (j.map a a' ≫ (Y.toEnrichedFunctor.map (j.obj a) (j.obj a') ≫
            MonoidalClosed.curry (eComp V M
              (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a'))))) ≫
            𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a'))) =
        (𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
          MonoidalClosed.uncurry
          ((j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) ≫
            MonoidalClosed.curry (eComp V M
              (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a'))))
      simp only [id_tensorHom_id, Category.id_comp]
      exact (Category.comp_id (MonoidalClosed.uncurry
        (j.map a a' ≫ (Y.toEnrichedFunctor.map (j.obj a) (j.obj a') ≫
          MonoidalClosed.curry (eComp V M
            (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a'))))))).trans
        (congrArg MonoidalClosed.uncurry (Category.assoc
        (j.map a a') (Y.toEnrichedFunctor.map (j.obj a) (j.obj a'))
        (MonoidalClosed.curry (eComp V M
          (Y.toEnrichedFunctor.obj (j.obj a)) (Y.toEnrichedFunctor.obj (j.obj a')))))).symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorRestrictionInv_component
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionInv j M Y) a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Pointwise cotensor commutes with enriched restriction, with identity components
in both directions. -/
@[no_expose]
def cotensorRestrictionIso
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) :
    cotensorObject M (restrictionObject j Y) ≅
      restrictionObject j (cotensorObject M Y) where
  hom := cotensorRestrictionHom j M Y
  inv := cotensorRestrictionInv j M Y
  hom_inv_id := by
    apply hom_ext
    intro a
    rw [component_comp, cotensorRestrictionHom_component,
      cotensorRestrictionInv_component, component_id]
    change 𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) ≫
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))
    exact Category.comp_id _
  inv_hom_id := by
    apply hom_ext
    intro a
    rw [component_comp, cotensorRestrictionInv_component,
      cotensorRestrictionHom_component, component_id]
    change 𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) ≫
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))
    exact Category.comp_id _

end CotensorRestriction

/-! Cotensors and the original enriched restriction agree naturally in both inputs. -/

section CotensorRestrictionNaturality

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorRestrictionIso_hom_component_private
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionIso j M Y).hom a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  cotensorRestrictionHom_component j M Y a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorRestrictionIso_hom_component
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionIso j M Y).hom a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  cotensorRestrictionIso_hom_component_private j M Y a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem cotensorRestrictionIso_inv_component_private
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionIso j M Y).inv a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  cotensorRestrictionInv_component j M Y a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem cotensorRestrictionIso_inv_component
    (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionIso j M Y).inv a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  cotensorRestrictionIso_inv_component_private j M Y a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The identity-component comparison uses the same original restriction on genuine diagram maps. -/
theorem cotensorRestrictionIso_naturality
    (j : EnrichedFunctor V A B) (M : V) {F G : EnrichedFunctorCat V B} (t : F ⟶ G) :
    cotensorMap M (restrictionMap j t) ≫ (cotensorRestrictionIso j M G).hom =
      (cotensorRestrictionIso j M F).hom ≫ restrictionMap j (cotensorMap M t) := by
  apply hom_ext
  intro a
  rw [component_comp, component_comp, cotensorMap_component, restrictionMap_component,
    cotensorRestrictionIso_hom_component, cotensorRestrictionIso_hom_component,
    restrictionMap_component, cotensorMap_component]
  change (ihom M).map (component t (j.obj a)) ≫
      𝟙 ((ihom M).obj (G.toEnrichedFunctor.obj (j.obj a))) =
    𝟙 ((ihom M).obj (F.toEnrichedFunctor.obj (j.obj a))) ≫
      (ihom M).map (component t (j.obj a))
  exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The same comparison is natural in the actual contravariant coefficient map. -/
theorem cotensorRestrictionIso_scalar_naturality
    (j : EnrichedFunctor V A B) {M N : V} (u : M ⟶ N) (Y : EnrichedFunctorCat V B) :
    cotensorScalarMap u (restrictionObject j Y) ≫ (cotensorRestrictionIso j M Y).hom =
      (cotensorRestrictionIso j N Y).hom ≫ restrictionMap j (cotensorScalarMap u Y) := by
  apply hom_ext
  intro a
  rw [component_comp, component_comp, cotensorScalarMap_component,
    cotensorRestrictionIso_hom_component, cotensorRestrictionIso_hom_component,
    restrictionMap_component, cotensorScalarMap_component]
  change (MonoidalClosed.pre u).app (Y.toEnrichedFunctor.obj (j.obj a)) ≫
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) =
    𝟙 ((ihom N).obj (Y.toEnrichedFunctor.obj (j.obj a))) ≫
      (MonoidalClosed.pre u).app (Y.toEnrichedFunctor.obj (j.obj a))
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end CotensorRestrictionNaturality


end CategoryTheory.EnrichedFunctorCat
