/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The actual arbitrary-coefficient free mapping comparison

The forward map evaluates the particular weighted end at the actual free
unit. The inverse uses the original full Hom action after the explicit
coefficient/parameter shuffle. Only this free-weighted end's products and
equalizer are required. No ordinary source, separator or model data occurs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uI uV vV

open CategoryTheory MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.FreeWeightedEnd

section Shuffle

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

private def shuffle (A H T : V) : (A ⊗ H) ⊗ T ⟶ (A ⊗ T) ⊗ H :=
  (α_ A H T).hom ≫ (A ◁ (β_ H T).hom) ≫ (α_ A T H).inv

@[reassoc]
private theorem shuffle_nat_h (A T : V) {P R : V} (h : P ⟶ R) :
    ((A ◁ h) ▷ T) ≫ shuffle A R T =
      shuffle A P T ≫ ((A ⊗ T) ◁ h) := by
  dsimp only [shuffle]
  simp only [Category.assoc]
  rw [associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, braiding_naturality_left, whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_right]

@[reassoc]
private theorem shuffle_nat_t (A H : V) {T T' : V} (f : T ⟶ T') :
    ((A ⊗ H) ◁ f) ≫ shuffle A H T' =
      shuffle A H T ≫ ((A ◁ f) ▷ H) := by
  dsimp only [shuffle]
  simp only [Category.assoc]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, braiding_naturality_right, whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_middle]

@[reassoc]
private theorem shuffle_unit_source (A T : V) :
    ((ρ_ A).inv ▷ T) ≫ shuffle A (𝟙_ V) T = (ρ_ (A ⊗ T)).inv := by
  simp only [shuffle, braiding_tensorUnit_left]
  monoidal_coherence

@[reassoc]
private theorem shuffle_negative_prefix (A H T : V) :
    ((β_ H A).inv ▷ T) ≫ (α_ H A T).hom ≫ (β_ H (A ⊗ T)).hom =
      shuffle A H T := by
  have hCancel : ((β_ H A).inv ▷ T) ≫ ((β_ H A).hom ▷ T) =
      𝟙 ((A ⊗ H) ⊗ T) := by
    rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  calc
    _ = ((β_ H A).inv ▷ T) ≫ ((β_ H A).hom ▷ T) ≫ shuffle A H T := by
      rw [braiding_tensor_right_hom]
      simp only [shuffle, Iso.hom_inv_id_assoc]
    _ = 𝟙 ((A ⊗ H) ⊗ T) ≫ shuffle A H T := by
      rw [← Category.assoc, hCancel]
    _ = shuffle A H T := Category.id_comp _

@[reassoc]
private theorem shuffle_split (A P Q T : V) :
    (α_ Q (A ⊗ P) T).hom ≫ (β_ Q ((A ⊗ P) ⊗ T)).hom ≫
      (shuffle A P T ▷ Q) ≫ (α_ (A ⊗ T) P Q).hom =
    ((β_ Q (A ⊗ P)).hom ▷ T) ≫ ((α_ A P Q).hom ▷ T) ≫
      shuffle A (P ⊗ Q) T := by
  simp only [shuffle, braiding_tensor_right_hom, braiding_tensor_left_hom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

end Shuffle

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {I : Type uI} [EnrichedCategory V I]

private theorem actualFreeUnit (a : I) (A : V) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A =
      (ρ_ A).inv ≫ (A ◁ eId V a) := by
  have h := (EnrichedFunctorCat.Free.adjunction (V := V) a).homEquiv_id A
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv] at h
  change (ρ_ A).inv ≫ (A ◁ eId V a) ≫
      EnrichedFunctorCat.component (𝟙 (EnrichedFunctorCat.Free.object a A)) a =
        (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A at h
  rw [EnrichedFunctorCat.component_id, Category.comp_id] at h
  exact h.symm

private theorem freeUnit_action (a : I) (A : V) (b : I) :
    (((ρ_ A).inv ≫ (A ◁ eId V a)) ▷ (a ⟶[V] b)) ≫
      EnrichedFunctorCat.Free.action a A a b = 𝟙 (A ⊗ (a ⟶[V] b)) := by
  have h := EnrichedFunctorCat.Free.reconstruct_component a A
    (EnrichedFunctorCat.Free.object a A) (𝟙 _) b
  simpa only [EnrichedFunctorCat.component_id,
    EnrichedFunctorCat.Free.extensionComponent, EnrichedFunctorCat.Free.evaluate,
    Category.comp_id, tensorHom_id, EnrichedFunctorCat.Free.object_uncurry_map,
    MonoidalClosed.uncurry_curry] using h.symm

private def parameterExtension (a : I) (A T : V) (X : EnrichedFunctor V I V)
    (q : A ⊗ T ⟶ X.obj a) (b : I) :
    (A ⊗ (a ⟶[V] b)) ⊗ T ⟶ X.obj b :=
  shuffle A (a ⟶[V] b) T ≫ (q ▷ (a ⟶[V] b)) ≫
    MonoidalClosed.uncurry (X.map a b)

private theorem parameterExtension_natural (a : I) (A T : V)
    (X : EnrichedFunctor V I V) (q : A ⊗ T ⟶ X.obj a) (b c : I) :
    (α_ (b ⟶[V] c) (A ⊗ (a ⟶[V] b)) T).hom ≫
        ((b ⟶[V] c) ◁ parameterExtension a A T X q b) ≫
        (β_ (b ⟶[V] c) (X.obj b)).hom ≫ MonoidalClosed.uncurry (X.map b c) =
      (((β_ (b ⟶[V] c) (A ⊗ (a ⟶[V] b))).hom ≫
        EnrichedFunctorCat.Free.action a A b c) ▷ T) ≫
        parameterExtension a A T X q c := by
  let P := a ⟶[V] b
  let Q := b ⟶[V] c
  let R := a ⟶[V] c
  let μ : P ⊗ Q ⟶ R := eComp V a b c
  have hBraid : (Q ◁ parameterExtension a A T X q b) ≫
      (β_ Q (X.obj b)).hom =
        (β_ Q ((A ⊗ P) ⊗ T)).hom ≫ (parameterExtension a A T X q b ▷ Q) :=
    braiding_naturality_right Q (parameterExtension a A T X q b)
  have hComp : (X.obj a ◁ μ) ≫ MonoidalClosed.uncurry (X.map a c) =
      (α_ (X.obj a) P Q).inv ≫
        (MonoidalClosed.uncurry (X.map a b) ▷ Q) ≫
        MonoidalClosed.uncurry (X.map b c) := by
    have h := congrArg MonoidalClosed.uncurry (X.map_comp a b c)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp] at h
    exact h
  have hCompForward : (MonoidalClosed.uncurry (X.map a b) ▷ Q) ≫
      MonoidalClosed.uncurry (X.map b c) =
        (α_ (X.obj a) P Q).hom ≫ (X.obj a ◁ μ) ≫
        MonoidalClosed.uncurry (X.map a c) := by
    have h := congrArg (fun z => (α_ (X.obj a) P Q).hom ≫ z) hComp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm
  calc
    _ = (α_ Q (A ⊗ P) T).hom ≫ (β_ Q ((A ⊗ P) ⊗ T)).hom ≫
        (parameterExtension a A T X q b ▷ Q) ≫
        MonoidalClosed.uncurry (X.map b c) := by
      simpa only [Category.assoc] using congrArg
        (fun z => (α_ Q (A ⊗ P) T).hom ≫ z ≫
          MonoidalClosed.uncurry (X.map b c)) hBraid
    _ = _ := by
      dsimp only [parameterExtension]
      simp only [comp_whiskerRight, Category.assoc]
      rw [hCompForward, associator_naturality_left_assoc, shuffle_split_assoc]
      rw [← whisker_exchange_assoc, ← shuffle_nat_h_assoc]
      simp only [EnrichedFunctorCat.Free.action, comp_whiskerRight, Category.assoc]
      rfl

private theorem parameterExtension_nat_parameter (a : I) (A : V)
    {T T' : V} (f : T ⟶ T') (X : EnrichedFunctor V I V)
    (q : A ⊗ T' ⟶ X.obj a) (b : I) :
    ((A ⊗ (a ⟶[V] b)) ◁ f) ≫ parameterExtension a A T' X q b =
      parameterExtension a A T X ((A ◁ f) ≫ q) b := by
  dsimp only [parameterExtension]
  rw [shuffle_nat_t_assoc, ← comp_whiskerRight_assoc]

private def inverseFamily (a : I) (A : V) (X : EnrichedFunctor V I V) (b : I) :
    (ihom A).obj (X.obj a) ⟶
      (ihom ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj b)).obj (X.obj b) :=
  MonoidalClosed.curry (parameterExtension a A ((ihom A).obj (X.obj a)) X
    ((ihom.ev A).app (X.obj a)) b)

private theorem inverseFamily_condition (a : I) (A : V) (X : EnrichedFunctor V I V)
    (b c : I) :
    MonoidalClosed.curry
      ((α_ (b ⟶[V] c) ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj b)
          ((ihom A).obj (X.obj a))).hom ≫
        ((b ⟶[V] c) ◁
          (((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj b) ◁ inverseFamily a A X b))
            ≫
        ((b ⟶[V] c) ◁
          (ihom.ev ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj b)).app (X.obj b)) ≫
        (β_ (b ⟶[V] c) (X.obj b)).hom ≫ MonoidalClosed.uncurry (X.map b c)) =
      MonoidalClosed.curry
        ((((β_ (b ⟶[V] c) ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj b)).hom ≫
          MonoidalClosed.uncurry ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.map b c))
            ⊗ₘ
          𝟙 ((ihom A).obj (X.obj a))) ≫
          (((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj c) ◁ inverseFamily a A X c) ≫
          (ihom.ev ((EnrichedFunctorCat.Free.object a A).toEnrichedFunctor.obj c)).app (X.obj c))
            := by
  dsimp only [inverseFamily]
  apply congrArg MonoidalClosed.curry
  have hEval (b : I) :
      ((A ⊗ (a ⟶[V] b)) ◁
        MonoidalClosed.curry (parameterExtension a A ((ihom A).obj (X.obj a)) X
          ((ihom.ev A).app (X.obj a)) b)) ≫
          (ihom.ev (A ⊗ (a ⟶[V] b))).app (X.obj b) =
            parameterExtension a A ((ihom A).obj (X.obj a)) X
              ((ihom.ev A).app (X.obj a)) b := by
    change MonoidalClosed.uncurry (MonoidalClosed.curry _) = _
    exact MonoidalClosed.uncurry_curry _
  rw [← whiskerLeft_comp_assoc, hEval, hEval,
    EnrichedFunctorCat.Free.object_uncurry_map]
  simpa only [EnrichedFunctorCat.Free.object_obj, tensorHom_id] using
    parameterExtension_natural a A ((ihom A).obj (X.obj a)) X
      ((ihom.ev A).app (X.obj a)) b c

variable (a : I) (A : V) (X : EnrichedFunctor V I V)
  [HasProduct (weightedEnd.objects
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]
  [HasProduct (weightedEnd.relations
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]
  [HasEqualizer
    (weightedEnd.leftMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)
    (weightedEnd.rightMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)]

/-- Evaluate the actual free-weighted end at the original free/evaluation unit. -/
@[no_expose]
def forward : weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X ⟶
    (ihom A).obj (X.obj a) :=
  weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X a ≫
    (MonoidalClosed.pre
      ((EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A)).app (X.obj a)

private theorem forward_eq_private :
    forward a A X =
      weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X a ≫
        (MonoidalClosed.pre
          ((EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A)).app (X.obj a) :=
  rfl

/-- The original projection and original constructed free unit are the complete forward map. -/
theorem forward_eq :
    forward a A X =
      weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X a ≫
        (MonoidalClosed.pre
          ((EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A)).app (X.obj a) :=
  forward_eq_private a A X

/-- Extend the actual evaluation family through this one free-weighted end. -/
@[no_expose]
def inverse : (ihom A).obj (X.obj a) ⟶
    weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X :=
  weightedEnd.lift (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X
    (inverseFamily a A X) (inverseFamily_condition a A X)

set_option backward.isDefEq.respectTransparency false in
private theorem inverse_π_private (b : I) :
    inverse a A X ≫
        weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X b =
      MonoidalClosed.curry
        ((α_ A (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom ≫
          (A ◁ (β_ (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom) ≫
          (α_ A ((ihom A).obj (X.obj a)) (a ⟶[V] b)).inv ≫
          ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (X.map a b)) := by
  have h := weightedEnd.lift_π
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X
      (inverseFamily a A X) (inverseFamily_condition a A X) b
  have hFamily : inverseFamily a A X b =
      MonoidalClosed.curry
        ((α_ A (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom ≫
          (A ◁ (β_ (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom) ≫
          (α_ A ((ihom A).obj (X.obj a)) (a ⟶[V] b)).inv ≫
          ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (X.map a b)) := by
    simp only [inverseFamily, parameterExtension, shuffle, Category.assoc]
  exact h.trans hFamily

/-- Every inverse projection is the actual shuffle, evaluation and full Hom action. -/
@[reassoc]
theorem inverse_π (b : I) :
    inverse a A X ≫
        weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X b =
      MonoidalClosed.curry
        ((α_ A (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom ≫
          (A ◁ (β_ (a ⟶[V] b) ((ihom A).obj (X.obj a))).hom) ≫
          (α_ A ((ihom A).obj (X.obj a)) (a ⟶[V] b)).inv ≫
          ((ihom.ev A).app (X.obj a) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (X.map a b)) :=
  inverse_π_private a A X b

set_option backward.isDefEq.respectTransparency false in
private theorem inverse_forward_private :
    inverse a A X ≫ forward a A X = 𝟙 ((ihom A).obj (X.obj a)) := by
  let T := (ihom A).obj (X.obj a)
  let η : A ⟶ A ⊗ (a ⟶[V] a) :=
    (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A
  let q : A ⊗ T ⟶ X.obj a := (ihom.ev A).app (X.obj a)
  have hUnit : (X.obj a ◁ eId V a) ≫ MonoidalClosed.uncurry (X.map a a) =
      (ρ_ (X.obj a)).hom := by
    have h := congrArg MonoidalClosed.uncurry (X.map_id a)
    simpa only [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
      MonoidalClosed.uncurry_curry] using h
  have hExpression : inverse a A X ≫ forward a A X =
      MonoidalClosed.curry (parameterExtension a A T X q a) ≫
        (MonoidalClosed.pre η).app (X.obj a) := by
    rw [forward_eq, ← Category.assoc, inverse_π]
    simp only [parameterExtension, shuffle, T, q, η, Category.assoc]
  apply MonoidalClosed.uncurry_injective
  rw [hExpression, MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry]
  simp only [MonoidalClosed.uncurry_eq, whiskerLeft_id, Category.id_comp]
  change (η ▷ T) ≫ parameterExtension a A T X q a = q
  rw [show η = (ρ_ A).inv ≫ (A ◁ eId V a) from actualFreeUnit a A]
  simp only [parameterExtension, comp_whiskerRight, Category.assoc]
  rw [shuffle_nat_h_assoc, shuffle_unit_source_assoc, whisker_exchange_assoc,
    hUnit, rightUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Actual evaluation followed by extension recovers the original coefficient internal Hom. -/
theorem inverse_forward :
    inverse a A X ≫ forward a A X = 𝟙 ((ihom A).obj (X.obj a)) :=
  inverse_forward_private a A X

set_option backward.isDefEq.respectTransparency false in
private theorem extension_forward_projection_private (b : I) :
    parameterExtension a A
        (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)
        X (MonoidalClosed.uncurry (forward a A X)) b =
      MonoidalClosed.uncurry
        (weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X b) := by
  let W := (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
  let E := weightedEnd W X
  let H := a ⟶[V] b
  let η : A ⟶ W.obj a := (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A
  let ua : W.obj a ⊗ E ⟶ X.obj a := MonoidalClosed.uncurry (weightedEnd.π W X a)
  let ub : W.obj b ⊗ E ⟶ X.obj b := MonoidalClosed.uncurry (weightedEnd.π W X b)
  let p : (A ⊗ H) ⊗ E ⟶ (H ⊗ W.obj a) ⊗ E :=
    (((β_ H A).inv ≫ (H ◁ η)) ▷ E)
  have hForward : MonoidalClosed.uncurry (forward a A X) = (η ▷ E) ≫ ua := by
    rw [forward_eq]
    exact MonoidalClosed.uncurry_pre_app (X.obj a) (weightedEnd.π W X a) η
  have hEnd :
      (α_ H (W.obj a) E).hom ≫ (H ◁ ua) ≫ (β_ H (X.obj a)).hom ≫
          MonoidalClosed.uncurry (X.map a b) =
        (((β_ H (W.obj a)).hom ≫ MonoidalClosed.uncurry (W.map a b)) ▷ E) ≫ ub := by
    have h := congrArg MonoidalClosed.uncurry (weightedEnd.condition W X a b)
    simp only [MonoidalClosed.uncurry_curry] at h
    simpa only [← whiskerLeft_comp_assoc, ← MonoidalClosed.uncurry_eq, tensorHom_id] using h
  have hAction : (η ▷ H) ≫ MonoidalClosed.uncurry (W.map a b) =
      𝟙 (A ⊗ H) := by
    rw [show η = (ρ_ A).inv ≫ (A ◁ eId V a) from actualFreeUnit a A]
    simpa only [W, EnrichedFunctorCat.Free.object_uncurry_map,
      MonoidalClosed.uncurry_curry] using freeUnit_action a A b
  have hPreRight : p ≫
      (((β_ H (W.obj a)).hom ≫ MonoidalClosed.uncurry (W.map a b)) ▷ E) =
        𝟙 ((A ⊗ H) ⊗ E) := by
    dsimp only [p]
    rw [← comp_whiskerRight]
    have hBefore : (((β_ H A).inv ≫ (H ◁ η)) ≫
        ((β_ H (W.obj a)).hom ≫ MonoidalClosed.uncurry (W.map a b))) =
          𝟙 (A ⊗ H) := by
      simp only [Category.assoc]
      rw [braiding_naturality_right_assoc, Iso.inv_hom_id_assoc]
      exact hAction
    rw [hBefore, id_whiskerRight]
  have hPreLeft : p ≫
      ((α_ H (W.obj a) E).hom ≫ (H ◁ ua) ≫ (β_ H (X.obj a)).hom ≫
        MonoidalClosed.uncurry (X.map a b)) =
      parameterExtension a A E X ((η ▷ E) ≫ ua) b := by
    dsimp only [p, parameterExtension]
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
      braiding_naturality_right_assoc, shuffle_negative_prefix_assoc]
    simp only [comp_whiskerRight, Category.assoc]
    rfl
  rw [hForward]
  change parameterExtension a A E X ((η ▷ E) ≫ ua) b = ub
  calc
    _ = p ≫
        ((α_ H (W.obj a) E).hom ≫ (H ◁ ua) ≫ (β_ H (X.obj a)).hom ≫
          MonoidalClosed.uncurry (X.map a b)) := hPreLeft.symm
    _ = p ≫
        ((((β_ H (W.obj a)).hom ≫ MonoidalClosed.uncurry (W.map a b)) ▷ E) ≫ ub) :=
      congrArg (fun z => p ≫ z) hEnd
    _ = (p ≫
        (((β_ H (W.obj a)).hom ≫ MonoidalClosed.uncurry (W.map a b)) ▷ E)) ≫ ub :=
      (Category.assoc _ _ _).symm
    _ = ub := by rw [hPreRight, Category.id_comp]

/-- The full end relation reconstructs every original projection from free evaluation. -/
theorem extension_forward_π (b : I) :
    (α_ A (a ⟶[V] b)
        (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)).hom ≫
      (A ◁ (β_ (a ⟶[V] b)
        (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)).hom) ≫
      (α_ A (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X)
        (a ⟶[V] b)).inv ≫
      (MonoidalClosed.uncurry (forward a A X) ▷ (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (X.map a b) =
    MonoidalClosed.uncurry
      (weightedEnd.π (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X b) := by
  simpa only [parameterExtension, shuffle, Category.assoc] using
    extension_forward_projection_private a A X b

set_option backward.isDefEq.respectTransparency false in
private theorem forward_inverse_private :
    forward a A X ≫ inverse a A X =
      𝟙 (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X) := by
  let W := (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
  let E := weightedEnd W X
  let T := (ihom A).obj (X.obj a)
  let q : A ⊗ T ⟶ X.obj a := (ihom.ev A).app (X.obj a)
  apply weightedEnd.hom_ext W X
  intro b
  have hInv : inverse a A X ≫ weightedEnd.π W X b = inverseFamily a A X b :=
    weightedEnd.lift_π W X (inverseFamily a A X) (inverseFamily_condition a A X) b
  rw [Category.assoc, hInv, Category.id_comp]
  change forward a A X ≫ MonoidalClosed.curry (parameterExtension a A T X q b) =
    weightedEnd.π W X b
  rw [← MonoidalClosed.curry_natural_left]
  have hParam := parameterExtension_nat_parameter a A (forward a A X) X q b
  have hUncurry : (A ◁ forward a A X) ≫ q = MonoidalClosed.uncurry (forward a A X) :=
    (MonoidalClosed.uncurry_eq _).symm
  rw [hParam, hUncurry, extension_forward_projection_private, MonoidalClosed.curry_uncurry]

/-- Evaluation and full Hom extension are inverse on the actual free-weighted end. -/
theorem forward_inverse :
    forward a A X ≫ inverse a A X =
      𝟙 (weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X) :=
  forward_inverse_private a A X

/-- The actual arbitrary-coefficient free mapping-object isomorphism. -/
@[no_expose]
def iso : weightedEnd (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X ≅
    (ihom A).obj (X.obj a) where
  hom := forward a A X
  inv := inverse a A X
  hom_inv_id := forward_inverse a A X
  inv_hom_id := inverse_forward a A X

private theorem iso_hom_private : (iso a A X).hom = forward a A X := rfl
private theorem iso_inv_private : (iso a A X).inv = inverse a A X := rfl

/-- The actual isomorphism's forward map is the original free-unit evaluation. -/
theorem iso_hom : (iso a A X).hom = forward a A X := iso_hom_private a A X

/-- The actual isomorphism's inverse is the constructed full Hom extension. -/
theorem iso_inv : (iso a A X).inv = inverse a A X := iso_inv_private a A X

section TargetNaturality

variable (Y : EnrichedFunctor V I V)
  [HasProduct (weightedEnd.objects
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor Y)]
  [HasProduct (weightedEnd.relations
    (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor Y)]
  [HasEqualizer
    (weightedEnd.leftMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor Y)
    (weightedEnd.rightMap (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor Y)]

set_option backward.isDefEq.respectTransparency false in
private theorem forward_naturality_target_private
    (f : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) X Y) :
    weightedEnd.mapDiagram (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X Y f ≫
        forward a A Y =
      forward a A X ≫ (ihom A).map ((eHomEquiv V).symm (f.app a)) := by
  let W := (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
  let η : A ⟶ W.obj a := (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A
  let q : X.obj a ⟶ Y.obj a := (eHomEquiv V).symm (f.app a)
  have hPre := (MonoidalClosed.pre η).naturality q
  rw [forward_eq a A Y, ← Category.assoc, weightedEnd.mapDiagram_π,
    forward_eq a A X]
  simpa only [Category.assoc] using congrArg
    (fun z => weightedEnd.π W X a ≫ z) hPre

/-- Genuine target maps preserve the complete free mapping comparison. -/
theorem forward_naturality_target
    (f : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) X Y) :
    weightedEnd.mapDiagram (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor X Y f ≫
        forward a A Y =
      forward a A X ≫ (ihom A).map ((eHomEquiv V).symm (f.app a)) :=
  forward_naturality_target_private a A X Y f

end TargetNaturality

section CoefficientNaturality

variable (B : V)
  [HasProduct (weightedEnd.objects
    (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X)]
  [HasProduct (weightedEnd.relations
    (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X)]
  [HasEqualizer
    (weightedEnd.leftMap (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X)
    (weightedEnd.rightMap (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X)]

set_option backward.isDefEq.respectTransparency false in
private theorem forward_naturality_coefficient_private (h : A ⟶ B) :
    weightedEnd.mapWeight (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X
        (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
        ((EnrichedFunctorCat.Free.functor (V := V) a).map h) ≫ forward a A X =
      forward a B X ≫ (MonoidalClosed.pre h).app (X.obj a) := by
  let WA := (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
  let WB := (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor
  let ηA : A ⟶ WA.obj a := (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app A
  let ηB : B ⟶ WB.obj a := (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app B
  let g := (EnrichedFunctorCat.Free.functor (V := V) a).map h
  let ga : WA.obj a ⟶ WB.obj a := (eHomEquiv V).symm (g.app a)
  have hUnit : h ≫ ηB = ηA ≫ ga := by
    have hu := (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.naturality h
    simpa only [Functor.id_map, Functor.comp_map, EnrichedFunctorCat.evaluation_map] using hu
  have hPre : (MonoidalClosed.pre ga).app (X.obj a) ≫
      (MonoidalClosed.pre ηA).app (X.obj a) =
        (MonoidalClosed.pre ηB).app (X.obj a) ≫
          (MonoidalClosed.pre h).app (X.obj a) := by
    calc
      _ = (MonoidalClosed.pre (ηA ≫ ga)).app (X.obj a) :=
        (NatTrans.congr_app (MonoidalClosed.pre_map ηA ga) (X.obj a)).symm
      _ = (MonoidalClosed.pre (h ≫ ηB)).app (X.obj a) :=
        congrArg (fun z : A ⟶ WB.obj a => (MonoidalClosed.pre z).app (X.obj a)) hUnit.symm
      _ = _ := NatTrans.congr_app (MonoidalClosed.pre_map h ηB) (X.obj a)
  rw [forward_eq a A X, ← Category.assoc, weightedEnd.mapWeight_π,
    forward_eq a B X]
  simpa only [Category.assoc] using congrArg
    (fun z => weightedEnd.π WB X a ≫ z) hPre

/-- Original coefficient maps act contravariantly through the same free comparison. -/
theorem forward_naturality_coefficient (h : A ⟶ B) :
    weightedEnd.mapWeight (EnrichedFunctorCat.Free.object a B).toEnrichedFunctor X
        (EnrichedFunctorCat.Free.object a A).toEnrichedFunctor
        ((EnrichedFunctorCat.Free.functor (V := V) a).map h) ≫ forward a A X =
      forward a B X ≫ (MonoidalClosed.pre h).app (X.obj a) :=
  forward_naturality_coefficient_private a A X B h

end CoefficientNaturality

end CategoryTheory.Enriched.FreeWeightedEnd
