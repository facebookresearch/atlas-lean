/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Right enriched Kan extension

For an enriched index map `j : A → B`, the right extension at `b` is the
weighted end of internal Hom from `B(b, j(a))` to the input diagram value `X(a)`.
The particular object products, relation products and equalizers construct its
full enriched B-action and its action on unit-graded transformations.

The universal weighted-end lift gives the natural Hom equivalence and the
adjunction between restriction and this right extension. The actual unit is
the lift of the restricted identity. The actual counit evaluates the original
end projection at the enriched identity. Their component formulas and both
triangle identities are proved for these same constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem rightKan_insert_identity (K E W : V) (e : 𝟙_ V ⟶ W) :
    (((ρ_ K).inv ≫ (K ◁ e)) ▷ E) ≫ (α_ K W E).hom =
      K ◁ ((λ_ E).inv ≫ (e ▷ E)) := by
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_middle, triangle_assoc_comp_right_inv_assoc,
    ← whiskerLeft_comp]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
omit [MonoidalClosed V] in
private theorem rightKan_identity_postcomp (j : EnrichedFunctor V A B) (a a' : A) :
    (ρ_ (a ⟶[V] a')).inv ≫
      ((a ⟶[V] a') ◁ eId V (j.obj a)) ≫
      (β_ (a ⟶[V] a') (j.obj a ⟶[V] j.obj a)).hom ≫
      ((j.obj a ⟶[V] j.obj a) ◁ j.map a a') ≫
      eComp V (j.obj a) (j.obj a) (j.obj a') = j.map a a' := by
  rw [BraidedCategory.braiding_naturality_right_assoc,
    rightUnitor_inv_braiding_assoc, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc]
  simp only [e_id_comp, Category.comp_id]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
omit [MonoidalClosed V] in
private theorem rightKan_eval_precomposition_id (b z : B) (E : V) :
    (λ_ ((b ⟶[V] z) ⊗ E)).inv ≫
      (eId V z ▷ ((b ⟶[V] z) ⊗ E)) ≫
      (α_ (z ⟶[V] z) (b ⟶[V] z) E).inv ≫
      (((β_ (z ⟶[V] z) (b ⟶[V] z)).hom ≫ eComp V b z z) ⊗ₘ 𝟙 E) =
        𝟙 ((b ⟶[V] z) ⊗ E) := by
  have hId := e_id_comp V (op z) (op b)
  change (λ_ (b ⟶[V] z)).inv ≫ (eId V z ▷ (b ⟶[V] z)) ≫
    eComp V (op z) (op z) (op b) = 𝟙 (b ⟶[V] z) at hId
  rw [eComp_op_eq] at hId
  rw [leftUnitor_tensor_inv]
  simp only [Category.assoc]
  rw [← associator_naturality_left_assoc, Iso.hom_inv_id_assoc]
  simp only [tensorHom_id]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight]
  simpa only [Category.assoc, id_whiskerRight] using
    congrArg (fun k => k ▷ E) hId

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanYoneda_condition (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (b : B) (a a' : A) :
    (α_ (a ⟶[V] a') (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
      ((a ⟶[V] a') ◁
        ((β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a)))) ≫
      (β_ (a ⟶[V] a') (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
      MonoidalClosed.uncurry
        (j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) =
    (((β_ (a ⟶[V] a') (b ⟶[V] j.obj a)).hom ≫
        ((b ⟶[V] j.obj a) ◁ j.map a a') ≫
        eComp V b (j.obj a) (j.obj a')) ⊗ₘ 𝟙 (Y.toEnrichedFunctor.obj b)) ≫
      (β_ (b ⟶[V] j.obj a') (Y.toEnrichedFunctor.obj b)).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a')) := by
  have h := Enriched.weightedEnd.yonedaAction_condition
    b Y.toEnrichedFunctor (j.obj a) (j.obj a')
  have h' := congrArg
    (fun k => ((j.map a a' ▷ (b ⟶[V] j.obj a)) ▷ Y.toEnrichedFunctor.obj b) ≫ k) h
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    BraidedCategory.braiding_naturality_left_assoc] at h'
  rw [tensorHom_id, ← comp_whiskerRight_assoc] at h'
  rw [BraidedCategory.braiding_naturality_left_assoc (j.map a a')
    (b ⟶[V] j.obj a) (eComp V b (j.obj a) (j.obj a'))] at h'
  simpa only [Category.assoc, tensorHom_id, MonoidalClosed.uncurry_natural_left] using h'

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- A supplied restricted transformation defines the actual parameterized
internal-Hom family used by the right-Kan universal lift. -/
def rightKanTransposeComponent (j : EnrichedFunctor V A B)
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b : B) (a : A) :
    Y.toEnrichedFunctor.obj b ⟶
      (ihom (b ⟶[V] j.obj a)).obj
        (X.toEnrichedFunctor.obj a) :=
  MonoidalClosed.curry <|
    (β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a)) ≫ component f a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanTransposeFamily_condition (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (X : EnrichedFunctorCat V A)
    (q : ∀ a, Y.toEnrichedFunctor.obj (j.obj a) ⟶ X.toEnrichedFunctor.obj a)
    (hq : ∀ a a', MonoidalClosed.uncurry
        (j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) ≫ q a' =
      (q a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a'))
    (b : B) (a a' : A) :
    MonoidalClosed.curry
      ((α_ (a ⟶[V] a') (b ⟶[V] j.obj a)
          (Y.toEnrichedFunctor.obj b)).hom ≫
        ((a ⟶[V] a') ◁
          ((b ⟶[V] j.obj a) ◁
            MonoidalClosed.curry
              ((β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
                MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a)) ≫ q a))) ≫
        ((a ⟶[V] a') ◁
          (ihom.ev (b ⟶[V] j.obj a)).app
            (X.toEnrichedFunctor.obj a)) ≫
        (β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a')) =
    MonoidalClosed.curry
      ((((β_ (a ⟶[V] a') (b ⟶[V] j.obj a)).hom ≫
          MonoidalClosed.uncurry (j.map a a' ≫
            MonoidalClosed.curry (eComp V b (j.obj a) (j.obj a')))) ⊗ₘ
            𝟙 (Y.toEnrichedFunctor.obj b)) ≫
        ((b ⟶[V] j.obj a') ◁
          MonoidalClosed.curry
            ((β_ (b ⟶[V] j.obj a') (Y.toEnrichedFunctor.obj b)).hom ≫
              MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a')) ≫ q a')) ≫
        (ihom.ev (b ⟶[V] j.obj a')).app
          (X.toEnrichedFunctor.obj a')) := by
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_curry]
  rw [← whiskerLeft_comp_assoc, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc (a ⟶[V] a') (q a)]
  have hn := hq a a'
  rw [tensorHom_id] at hn
  rw [← hn]
  have h := congrArg (fun k => k ≫ q a')
    (rightKanYoneda_condition j Y b a a')
  simpa only [Category.assoc, whiskerLeft_comp, tensorHom_id,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] using h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKan_identity_evaluation (Y : EnrichedFunctor V B V) (b : B) :
    (λ_ (Y.obj b)).inv ≫
      (eId V b ▷ Y.obj b) ≫
      (β_ (b ⟶[V] b) (Y.obj b)).hom ≫
      MonoidalClosed.uncurry (Y.map b b) = 𝟙 (Y.obj b) := by
  have hu := congrArg (MonoidalClosed.uncurry (A := Y.obj b)) (Y.map_id b)
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at hu
  rw [BraidedCategory.braiding_naturality_left_assoc (eId V b) (Y.obj b),
    leftUnitor_inv_braiding_assoc, hu]
  simp only [Iso.inv_hom_id]

variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasProduct (Enriched.weightedEnd.objects
      (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasProduct (Enriched.weightedEnd.relations
      (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasEqualizer
      (Enriched.weightedEnd.leftMap
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedEnd.rightMap
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The existing full enriched right-Kan object, in the genuine functor category. -/
abbrev rightKanObject (X : EnrichedFunctorCat V A) : EnrichedFunctorCat V B :=
  ⟨Enriched.weightedEnd.rightKanEndFunctor j X.toEnrichedFunctor⟩

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Genuine diagram variance gives the actual component on right-end objects. -/
def rightKanMapComponent {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) (b : B) :
    Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b ⟶
      Enriched.weightedEnd.rightKanEndObject j Y.toEnrichedFunctor b :=
  Enriched.weightedEnd.mapDiagram
    (Enriched.weightedEnd.rightKanWeight j b)
    X.toEnrichedFunctor Y.toEnrichedFunctor f

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanMapComponent_π {X Y : EnrichedFunctorCat V A}
    (f : X ⟶ Y) (b : B) (a : A) :
    rightKanMapComponent j f b ≫ Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) Y.toEnrichedFunctor a =
      Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a ≫
        (ihom ((Enriched.weightedEnd.rightKanWeight j b).obj a)).map
          (component f a) :=
  Enriched.weightedEnd.mapDiagram_π
    (Enriched.weightedEnd.rightKanWeight j b)
    X.toEnrichedFunctor Y.toEnrichedFunctor f a

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanMapComponent_id (X : EnrichedFunctorCat V A) (b : B) :
    rightKanMapComponent j (𝟙 X) b =
      𝟙 ((rightKanObject j X).toEnrichedFunctor.obj b) :=
  Enriched.weightedEnd.mapDiagram_id
    (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanMapComponent_comp {X Y Z : EnrichedFunctorCat V A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (b : B) :
    rightKanMapComponent j (f ≫ g) b =
      rightKanMapComponent j f b ≫ rightKanMapComponent j g b :=
  (Enriched.weightedEnd.mapDiagram_comp
    (Enriched.weightedEnd.rightKanWeight j b)
    X.toEnrichedFunctor Y.toEnrichedFunctor Z.toEnrichedFunctor f g).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanActionComponent_naturality
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) (b c : B) (a : A) :
    Enriched.weightedEnd.rightKanActionComponent j X.toEnrichedFunctor b c a ≫
        (ihom ((Enriched.weightedEnd.rightKanWeight j c).obj a)).map (component f a) =
      ((b ⟶[V] c) ◁ rightKanMapComponent j f b) ≫
        Enriched.weightedEnd.rightKanActionComponent j Y.toEnrichedFunctor b c a := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left]
  rw [Enriched.weightedEnd.rightKanActionComponent_uncurry_eq,
    Enriched.weightedEnd.rightKanActionComponent_uncurry_eq]
  rw [associator_inv_naturality_right_assoc]
  simp only [tensorHom_id]
  have hProjection := rightKanMapComponent_π j f b a
  dsimp only [Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable] at hProjection
  dsimp only [Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    hProjection, whiskerLeft_comp]
  simp only [Category.assoc, ihom.ev_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanEndAction_naturality
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) (b c : B) :
    Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b c ≫
        rightKanMapComponent j f c =
      ((b ⟶[V] c) ◁ rightKanMapComponent j f b) ≫
        Enriched.weightedEnd.rightKanEndAction j Y.toEnrichedFunctor b c := by
  apply Enriched.weightedEnd.hom_ext
    (Enriched.weightedEnd.rightKanWeight j c) Y.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [rightKanMapComponent_π,
    Enriched.weightedEnd.rightKanEndAction_π_assoc,
    Enriched.weightedEnd.rightKanEndAction_π,
    rightKanActionComponent_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Diagram components retain naturality on the entire target Hom object. -/
theorem rightKanMapComponent_naturality
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) (b c : B) :
    MonoidalClosed.uncurry ((rightKanObject j X).toEnrichedFunctor.map b c) ≫
        rightKanMapComponent j f c =
      (rightKanMapComponent j f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry ((rightKanObject j Y).toEnrichedFunctor.map b c) := by
  change MonoidalClosed.uncurry
      (Enriched.weightedEnd.rightKanEndMap j X.toEnrichedFunctor b c) ≫
        rightKanMapComponent j f c =
      (rightKanMapComponent j f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry
          (Enriched.weightedEnd.rightKanEndMap j Y.toEnrichedFunctor b c)
  rw [Enriched.weightedEnd.rightKanEndMap_uncurry,
    Enriched.weightedEnd.rightKanEndMap_uncurry]
  have hCross := BraidedCategory.braiding_inv_naturality_left
    (rightKanMapComponent j f b) (b ⟶[V] c)
  calc
    _ = (β_ (b ⟶[V] c)
          (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b)).inv ≫
        ((b ⟶[V] c) ◁ rightKanMapComponent j f b) ≫
        Enriched.weightedEnd.rightKanEndAction j Y.toEnrichedFunctor b c := by
      simpa only [Category.assoc] using congrArg
        (fun k => (β_ (b ⟶[V] c)
          (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b)).inv ≫ k)
        (rightKanEndAction_naturality j f b c)
    _ = _ := by
      simpa only [Category.assoc, tensorHom_id] using congrArg
        (fun k => k ≫ Enriched.weightedEnd.rightKanEndAction j Y.toEnrichedFunctor b c)
        hCross.symm

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The extension map is a genuine unit-graded transformation, not a point map. -/
def rightKanMap {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    rightKanObject j X ⟶ rightKanObject j Y :=
  GradedNatTrans.unitOfComponents
    (fun b => rightKanMapComponent j f b)
    (fun b c => rightKanMapComponent_naturality j f b c)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanMap_component {X Y : EnrichedFunctorCat V A}
    (f : X ⟶ Y) (b : B) :
    component (rightKanMap j f) b = rightKanMapComponent j f b :=
  GradedNatTrans.unitOfComponents_component _ _ b

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual end and its whole-Hom maps extend functorially on full transformations. -/
def rightKan : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V B where
  obj := rightKanObject j
  map := fun f => rightKanMap j f
  map_id X := by
    apply hom_ext
    intro b
    rw [rightKanMap_component, rightKanMapComponent_id, component_id]
  map_comp f g := by
    apply hom_ext
    intro b
    rw [rightKanMap_component, component_comp, rightKanMap_component,
      rightKanMap_component, rightKanMapComponent_comp]
    rfl

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Evaluate the actual right-end projection at the original enriched identity. -/
def rightKanCounitComponent (X : EnrichedFunctorCat V A) (a : A) :
    Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a) ⟶
      X.toEnrichedFunctor.obj a :=
  let W := Enriched.weightedEnd.rightKanWeight j (j.obj a)
  let E := Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a)
  let e : 𝟙_ V ⟶ W.obj a := eId V (j.obj a)
  (λ_ E).inv ≫ (e ▷ E) ≫
    MonoidalClosed.uncurry (Enriched.weightedEnd.π W X.toEnrichedFunctor a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The identity evaluation is natural in the entire input transformation. -/
theorem rightKanCounitComponent_diagram_naturality
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) (a : A) :
    rightKanMapComponent j f (j.obj a) ≫ rightKanCounitComponent j Y a =
      rightKanCounitComponent j X a ≫ component f a := by
  dsimp only [rightKanCounitComponent]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    ← MonoidalClosed.uncurry_natural_left, rightKanMapComponent_π,
    MonoidalClosed.uncurry_natural_right]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Acting on the entire target Hom and evaluating the counit recovers the
original end projection, before any generalized point is chosen. -/
theorem rightKanEndAction_counit (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b (j.obj a) ≫
        rightKanCounitComponent j X a =
      MonoidalClosed.uncurry (Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a) := by
  dsimp only [rightKanCounitComponent]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    ← MonoidalClosed.uncurry_natural_left,
    Enriched.weightedEnd.rightKanEndAction_π,
    Enriched.weightedEnd.rightKanActionComponent_uncurry_eq]
  have h := congrArg (fun k => k ≫ MonoidalClosed.uncurry (Enriched.weightedEnd.π
      (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a))
      (rightKan_eval_precomposition_id b (j.obj a)
        (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b))
  dsimp only [Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable] at h ⊢
  simpa only [Category.assoc, Category.id_comp, MonoidalClosed.uncurry_eq] using h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanCounitComponent_action_naturality
    (X : EnrichedFunctorCat V A) (a a' : A) :
    (j.map a a' ▷ Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a)) ≫
        Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor (j.obj a) (j.obj a') ≫
        rightKanCounitComponent j X a' =
      ((a ⟶[V] a') ◁ rightKanCounitComponent j X a) ≫
        (β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') := by
  rw [rightKanEndAction_counit]
  have h := congrArg MonoidalClosed.uncurry
    (Enriched.weightedEnd.condition
      (Enriched.weightedEnd.rightKanWeight j (j.obj a)) X.toEnrichedFunctor a a')
  simp only [MonoidalClosed.uncurry_curry] at h
  have h' := congrArg
    (fun k => (((ρ_ (a ⟶[V] a')).inv ≫
      ((a ⟶[V] a') ◁ eId V (j.obj a))) ▷
        Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a)) ≫ k) h
  dsimp only [Enriched.weightedEnd.rightKanEndObject,
    Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable] at h'
  conv_lhs at h' =>
    slice 1 2
    rw [rightKan_insert_identity]
  simp only [Category.assoc] at h'
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc] at h'
  simp only [Category.assoc] at h'
  rw [← MonoidalClosed.uncurry_eq] at h'
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    tensorHom_id] at h'
  rw [← comp_whiskerRight_assoc] at h'
  simp only [Category.assoc] at h'
  rw [rightKan_identity_postcomp] at h'
  dsimp only [rightKanCounitComponent]
  dsimp only [Enriched.weightedEnd.rightKanEndObject,
    Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable]
  simpa only [Category.assoc, MonoidalClosed.uncurry_eq] using h'.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The counit respects every original enriched A-Hom object. -/
theorem rightKanCounitComponent_naturality
    (X : EnrichedFunctorCat V A) (a a' : A) :
    MonoidalClosed.uncurry
        ((restrictionObject j (rightKanObject j X)).toEnrichedFunctor.map a a') ≫
        rightKanCounitComponent j X a' =
      (rightKanCounitComponent j X a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') := by
  change MonoidalClosed.uncurry
      (j.map a a' ≫ Enriched.weightedEnd.rightKanEndMap j X.toEnrichedFunctor
        (j.obj a) (j.obj a')) ≫ rightKanCounitComponent j X a' = _
  rw [MonoidalClosed.uncurry_natural_left,
    Enriched.weightedEnd.rightKanEndMap_uncurry]
  rw [BraidedCategory.braiding_inv_naturality_right_assoc]
  simp only [Category.assoc]
  rw [rightKanCounitComponent_action_naturality]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    Iso.inv_hom_id_assoc]
  simp only [tensorHom_id]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual enriched counit transformation is built from its full-Hom law. -/
def rightKanCounit (X : EnrichedFunctorCat V A) :
    restrictionObject j (rightKanObject j X) ⟶ X :=
  GradedNatTrans.unitOfComponents
    (fun a => rightKanCounitComponent j X a)
    (fun a a' => rightKanCounitComponent_naturality j X a a')

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanCounit_component (X : EnrichedFunctorCat V A) (a : A) :
    component (rightKanCounit j X) a = rightKanCounitComponent j X a :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The universal lift uses the full A-Hom relation of the supplied
restricted transformation and only the original weighted-end limits. -/
@[no_expose]
def rightKanTransposeMapComponent
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b : B) :
    Y.toEnrichedFunctor.obj b ⟶
      Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b := by
  refine Enriched.weightedEnd.lift
    (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor
    (rightKanTransposeComponent j f b) ?_
  intro a a'
  exact rightKanTransposeFamily_condition j Y X (fun a => component f a)
    (fun a a' => f.uncurriedNaturality a a') b a a'

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanTransposeMapComponent_π
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b : B) (a : A) :
    rightKanTransposeMapComponent j f b ≫ Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a =
      rightKanTransposeComponent j f b a :=
  Enriched.weightedEnd.lift_π
    (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor _ _ a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
private theorem rightKanTransposeMapComponent_action_naturality
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b c : B) :
    ((b ⟶[V] c) ◁ rightKanTransposeMapComponent j f b) ≫
        Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b c =
      (β_ (b ⟶[V] c) (Y.toEnrichedFunctor.obj b)).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) ≫
        rightKanTransposeMapComponent j f c := by
  apply Enriched.weightedEnd.hom_ext
    (Enriched.weightedEnd.rightKanWeight j c) X.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [Enriched.weightedEnd.rightKanEndAction_π, rightKanTransposeMapComponent_π]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    Enriched.weightedEnd.rightKanActionComponent_uncurry_eq]
  have hp := rightKanTransposeMapComponent_π j f b a
  dsimp only [Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable] at hp ⊢
  rw [associator_inv_naturality_right_assoc, tensorHom_id,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, hp]
  rw [← MonoidalClosed.uncurry_eq]
  dsimp only [rightKanTransposeComponent]
  rw [MonoidalClosed.uncurry_natural_left]
  simp only [MonoidalClosed.uncurry_curry]
  have h := Enriched.weightedEnd.yonedaAction_condition
    b Y.toEnrichedFunctor c (j.obj a)
  have h' := congrArg
    (fun k => (α_ (c ⟶[V] j.obj a) (b ⟶[V] c)
      (Y.toEnrichedFunctor.obj b)).inv ≫ k ≫ component f a) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
    tensorHom_id] using h'.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The inverse universal lift is natural on the entire B-Hom object. -/
theorem rightKanTransposeMapComponent_naturality
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b c : B) :
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) ≫
        rightKanTransposeMapComponent j f c =
      (rightKanTransposeMapComponent j f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry ((rightKanObject j X).toEnrichedFunctor.map b c) := by
  change MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) ≫
      rightKanTransposeMapComponent j f c =
    (rightKanTransposeMapComponent j f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry (Enriched.weightedEnd.rightKanEndMap j X.toEnrichedFunctor b c)
  rw [Enriched.weightedEnd.rightKanEndMap_uncurry]
  have h := congrArg
    (fun k => (β_ (b ⟶[V] c) (Y.toEnrichedFunctor.obj b)).inv ≫ k)
    (rightKanTransposeMapComponent_action_naturality j f b c)
  calc
    _ = (β_ (b ⟶[V] c) (Y.toEnrichedFunctor.obj b)).inv ≫
        ((b ⟶[V] c) ◁ rightKanTransposeMapComponent j f b) ≫
        Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b c := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
    _ = _ := by
      rw [← BraidedCategory.braiding_inv_naturality_left_assoc]
      simp only [tensorHom_id]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The inverse universal map is a genuine unit-graded transformation. -/
def rightKanTranspose
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) : Y ⟶ rightKanObject j X :=
  GradedNatTrans.unitOfComponents
    (fun b => rightKanTransposeMapComponent j f b)
    (fun b c => rightKanTransposeMapComponent_naturality j f b c)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanTranspose_component
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (b : B) :
    component (rightKanTranspose j f) b = rightKanTransposeMapComponent j f b :=
  GradedNatTrans.unitOfComponents_component _ _ b

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The forward Hom map restricts the genuine transformation and composes
with the actual enriched counit. -/
def rightKanHomToRestricted
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : Y ⟶ rightKanObject j X) : restrictionObject j Y ⟶ X :=
  restrictionMap j f ≫ rightKanCounit j X

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
theorem rightKanHomToRestricted_component
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : Y ⟶ rightKanObject j X) (a : A) :
    component (rightKanHomToRestricted j f) a =
      component f (j.obj a) ≫ rightKanCounitComponent j X a := by
  rw [rightKanHomToRestricted, component_comp, restrictionMap_component,
    rightKanCounit_component]
  rfl

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual counit is natural in full input transformations. -/
theorem rightKanCounit_naturality
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    restrictionMap j (rightKanMap j f) ≫ rightKanCounit j Y =
      rightKanCounit j X ≫ f := by
  apply hom_ext
  intro a
  rw [component_comp, restrictionMap_component, rightKanMap_component,
    rightKanCounit_component, component_comp, rightKanCounit_component]
  exact rightKanCounitComponent_diagram_naturality j f a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Identity evaluation of the inverse universal lift recovers the original
restricted transformation component. -/
theorem rightKanTransposeMapComponent_counit
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (a : A) :
    rightKanTransposeMapComponent j f (j.obj a) ≫ rightKanCounitComponent j X a =
      component f a := by
  dsimp only [rightKanCounitComponent]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    ← MonoidalClosed.uncurry_natural_left, rightKanTransposeMapComponent_π]
  dsimp only [rightKanTransposeComponent]
  rw [MonoidalClosed.uncurry_curry]
  have h := congrArg (fun k => k ≫ component f a)
    (rightKan_identity_evaluation Y.toEnrichedFunctor (j.obj a))
  dsimp only [Enriched.weightedEnd.rightKanWeight, EnrichedFunctor.comp,
    EnrichedFunctor.covariantRepresentable]
  simpa only [Category.assoc, Category.id_comp] using h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- One inverse equation of the actual universal Hom correspondence. -/
theorem rightKanHomToRestricted_transpose
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) :
    rightKanHomToRestricted j (rightKanTranspose j f) = f := by
  apply hom_ext
  intro a
  rw [rightKanHomToRestricted_component, rightKanTranspose_component]
  exact rightKanTransposeMapComponent_counit j f a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Full B-Hom naturality and the counit/action characteristic reconstruct
the original transformation, not just its identity values. -/
theorem rightKanTranspose_homToRestricted
    {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : Y ⟶ rightKanObject j X) :
    rightKanTranspose j (rightKanHomToRestricted j f) = f := by
  apply hom_ext
  intro b
  rw [rightKanTranspose_component]
  apply Enriched.weightedEnd.hom_ext
    (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor
  intro a
  rw [rightKanTransposeMapComponent_π]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  dsimp only [rightKanTransposeComponent]
  rw [MonoidalClosed.uncurry_curry, rightKanHomToRestricted_component]
  have hn := f.uncurriedNaturality b (j.obj a)
  change MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a)) ≫
      component f (j.obj a) =
    (component f b ⊗ₘ 𝟙 (b ⟶[V] j.obj a)) ≫
      MonoidalClosed.uncurry
        (Enriched.weightedEnd.rightKanEndMap j X.toEnrichedFunctor b (j.obj a)) at hn
  rw [Enriched.weightedEnd.rightKanEndMap_uncurry] at hn
  have h := congrArg
    (fun k => (β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫ k ≫
      rightKanCounitComponent j X a) hn
  calc
    _ = (β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
        (component f b ▷ (b ⟶[V] j.obj a)) ≫
        (β_ (b ⟶[V] j.obj a)
          (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b)).inv ≫
        Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b (j.obj a) ≫
        rightKanCounitComponent j X a := by
      simpa only [Category.assoc, tensorHom_id] using h
    _ = ((b ⟶[V] j.obj a) ◁ component f b) ≫
        Enriched.weightedEnd.rightKanEndAction j X.toEnrichedFunctor b (j.obj a) ≫
        rightKanCounitComponent j X a := by
      have hb := BraidedCategory.braiding_naturality_right
        (b ⟶[V] j.obj a) (component f b)
      change ((b ⟶[V] j.obj a) ◁ component f b) ≫
          (β_ (b ⟶[V] j.obj a)
            (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b)).hom =
        (β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
          (component f b ▷ (b ⟶[V] j.obj a)) at hb
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← hb]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [rightKanEndAction_counit]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual universal Hom equivalence for the full enriched right Kan
extension uses the original restriction and weighted-end constructions. -/
def rightKanHomEquiv (Y : EnrichedFunctorCat V B) (X : EnrichedFunctorCat V A) :
    (restrictionObject j Y ⟶ X) ≃ (Y ⟶ rightKanObject j X) where
  toFun := rightKanTranspose j
  invFun := rightKanHomToRestricted j
  left_inv := rightKanHomToRestricted_transpose j
  right_inv := rightKanTranspose_homToRestricted j

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The inverse Hom map is natural under original source transformations. -/
theorem rightKanHomToRestricted_naturality_left
    {Y' Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : Y' ⟶ Y) (g : Y ⟶ rightKanObject j X) :
    rightKanHomToRestricted j (f ≫ g) =
      restrictionMap j f ≫ rightKanHomToRestricted j g := by
  apply hom_ext
  intro a
  rw [rightKanHomToRestricted_component, component_comp, component_comp,
    restrictionMap_component, rightKanHomToRestricted_component]
  exact Category.assoc (component f (j.obj a)) (component g (j.obj a))
    (rightKanCounitComponent j X a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The universal lift is natural under original target transformations. -/
theorem rightKanTranspose_naturality_right
    {Y : EnrichedFunctorCat V B} {X X' : EnrichedFunctorCat V A}
    (f : restrictionObject j Y ⟶ X) (g : X ⟶ X') :
    rightKanTranspose j (f ≫ g) = rightKanTranspose j f ≫ rightKanMap j g := by
  apply hom_ext
  intro b
  rw [rightKanTranspose_component, component_comp, rightKanTranspose_component,
    rightKanMap_component]
  apply Enriched.weightedEnd.hom_ext
    (Enriched.weightedEnd.rightKanWeight j b) X'.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [rightKanTransposeMapComponent_π, rightKanMapComponent_π]
  change rightKanTransposeComponent j (f ≫ g) b a =
    rightKanTransposeMapComponent j f b ≫
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
        X.toEnrichedFunctor a ≫
      (ihom (b ⟶[V] j.obj a)).map (component g a)
  have hp := rightKanTransposeMapComponent_π j f b a
  change rightKanTransposeMapComponent j f b ≫
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
        X.toEnrichedFunctor a = rightKanTransposeComponent j f b a at hp
  rw [← Category.assoc, hp]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right]
  dsimp only [rightKanTransposeComponent]
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry, component_comp]
  simp only [Category.assoc]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- Restriction is left adjoint to the actual enriched weighted-end extension.
The input contains only the particular right-Kan end families. -/
def rightKanAdjunction : restriction j ⊣ rightKan j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rightKanHomEquiv j
      homEquiv_naturality_left_symm := fun f g =>
        rightKanHomToRestricted_naturality_left j f g
      homEquiv_naturality_right := fun f g =>
        rightKanTranspose_naturality_right j f g }

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The adjunction uses the proved full-transformation Hom equivalence. -/
theorem rightKanAdjunction_homEquiv
    (Y : EnrichedFunctorCat V B) (X : EnrichedFunctorCat V A) :
    (rightKanAdjunction j).homEquiv Y X = rightKanHomEquiv j Y X := by
  simp only [rightKanAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual adjunction unit is the universal lift of the restricted identity. -/
theorem rightKanAdjunction_unit_app (Y : EnrichedFunctorCat V B) :
    (rightKanAdjunction j).unit.app Y =
      rightKanTranspose j (𝟙 (restrictionObject j Y)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual adjunction counit is the original enriched identity evaluation. -/
theorem rightKanAdjunction_counit_app (X : EnrichedFunctorCat V A) :
    (rightKanAdjunction j).counit.app X = rightKanCounit j X := by
  change rightKanHomToRestricted j (𝟙 (rightKanObject j X)) = rightKanCounit j X
  apply hom_ext
  intro a
  rw [rightKanHomToRestricted_component, component_id, rightKanCounit_component]
  exact Category.id_comp (rightKanCounitComponent j X a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual unit retains the entire B-Hom object on each weighted-end projection. -/
theorem rightKanAdjunction_unit_component_π
    (Y : EnrichedFunctorCat V B) (b : B) (a : A) :
    component ((rightKanAdjunction j).unit.app Y) b ≫
        Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
          (restrictionObject j Y).toEnrichedFunctor a =
      MonoidalClosed.curry
        ((β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a))) := by
  change component (rightKanTranspose j (𝟙 (restrictionObject j Y))) b ≫
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
        (restrictionObject j Y).toEnrichedFunctor a = _
  rw [rightKanTranspose_component, rightKanTransposeMapComponent_π]
  dsimp only [rightKanTransposeComponent]
  change MonoidalClosed.curry
      ((β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a)) ≫
        (component (𝟙 (restrictionObject j Y)) a :
          Y.toEnrichedFunctor.obj (j.obj a) ⟶ Y.toEnrichedFunctor.obj (j.obj a))) = _
  have hi : (component (𝟙 (restrictionObject j Y)) a :
      Y.toEnrichedFunctor.obj (j.obj a) ⟶ Y.toEnrichedFunctor.obj (j.obj a)) =
      𝟙 (Y.toEnrichedFunctor.obj (j.obj a)) := component_id (restrictionObject j Y) a
  rw [hi, Category.comp_id]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual adjunction counit component agrees with the end evaluation map. -/
theorem rightKanAdjunction_counit_component
    (X : EnrichedFunctorCat V A) (a : A) :
    component ((rightKanAdjunction j).counit.app X) a =
      rightKanCounitComponent j X a := by
  exact (congrArg
    (fun f : restrictionObject j (rightKanObject j X) ⟶ X => component f a)
    (rightKanAdjunction_counit_app j X)).trans (rightKanCounit_component j X a)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The counit evaluates the original projection at the enriched identity. -/
theorem rightKanCounitComponent_eq (X : EnrichedFunctorCat V A) (a : A) :
    rightKanCounitComponent j X a =
      (λ_ (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a))).inv ≫
        (eId V (j.obj a) ▷
          Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a)) ≫
        MonoidalClosed.uncurry (Enriched.weightedEnd.π
          (Enriched.weightedEnd.rightKanWeight j (j.obj a)) X.toEnrichedFunctor a) := rfl

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The universal lift is natural under original source transformations. -/
theorem rightKanTranspose_naturality_left
    {Y' Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : Y' ⟶ Y) (g : restrictionObject j Y ⟶ X) :
    rightKanTranspose j (restrictionMap j f ≫ g) =
      f ≫ rightKanTranspose j g := by
  have h := (rightKanAdjunction j).homEquiv_naturality_left f g
  rw [rightKanAdjunction_homEquiv, rightKanAdjunction_homEquiv] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The inverse Hom map is natural under original target transformations. -/
theorem rightKanHomToRestricted_naturality_right
    {Y : EnrichedFunctorCat V B} {X X' : EnrichedFunctorCat V A}
    (f : Y ⟶ rightKanObject j X) (g : X ⟶ X') :
    rightKanHomToRestricted j (f ≫ rightKanMap j g) =
      rightKanHomToRestricted j f ≫ g := by
  have h := (rightKanAdjunction j).homEquiv_naturality_right_symm f g
  rw [rightKanAdjunction_homEquiv, rightKanAdjunction_homEquiv] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual unit is natural in every full input transformation. -/
theorem rightKanUnit_naturality
    {Y Y' : EnrichedFunctorCat V B} (f : Y ⟶ Y') :
    f ≫ rightKanTranspose j (𝟙 (restrictionObject j Y')) =
      rightKanTranspose j (𝟙 (restrictionObject j Y)) ≫
        rightKanMap j (restrictionMap j f) := by
  have h := (rightKanAdjunction j).unit.naturality f
  change f ≫ (rightKanAdjunction j).unit.app Y' =
    (rightKanAdjunction j).unit.app Y ≫ rightKanMap j (restrictionMap j f) at h
  rw [rightKanAdjunction_unit_app, rightKanAdjunction_unit_app] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The restriction-unit followed by the actual counit is the restricted identity. -/
theorem rightKan_left_triangle (Y : EnrichedFunctorCat V B) :
    restrictionMap j (rightKanTranspose j (𝟙 (restrictionObject j Y))) ≫
        rightKanCounit j (restrictionObject j Y) = 𝟙 (restrictionObject j Y) :=
  rightKanHomToRestricted_transpose j (𝟙 (restrictionObject j Y))

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
/-- The actual unit followed by right extension of the actual counit is the identity. -/
theorem rightKan_right_triangle (X : EnrichedFunctorCat V A) :
    rightKanTranspose j (𝟙 (restrictionObject j (rightKanObject j X))) ≫
        rightKanMap j (rightKanCounit j X) = 𝟙 (rightKanObject j X) := by
  have h := (rightKanAdjunction j).right_triangle_components X
  rw [rightKanAdjunction_unit_app, rightKanAdjunction_counit_app] at h
  exact h

end CategoryTheory.EnrichedFunctorCat
