/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.FunctorOpposite
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend
public import MathlibExt.CategoryTheory.Enriched.GradedComposition
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition

/-!
# Enriched left Kan extensions

The left extension along an enriched functor is constructed from the weighted
coends of its pulled-back contravariant representables. Full enriched Hom maps
give the diagram action. The unit-graded adjunction includes both Hom inverses,
the unit, counit, and triangle identities. Center-graded transformations give
the graded Hom correspondence and its naturalities, using pointwise cotensors.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The pulled-back contravariant representable for the left extension. -/
abbrev leftKanWeight (j : EnrichedFunctor V A B) (b : B) :
    EnrichedFunctor V Aᵒᵖ V :=
  let W := (EnrichedFunctor.opposite j).comp V
    (EnrichedFunctor.contravariantRepresentable V B b)
  { obj := fun a => j.obj a.unop ⟶[V] b
    map := fun a a' => W.map a a'
    map_id := fun a => W.map_id a
    map_comp := fun a a' a'' => W.map_comp a a' a'' }

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanWeight_eq (j : EnrichedFunctor V A B) (b : B) :
    leftKanWeight j b =
      (EnrichedFunctor.opposite j).comp V
        (EnrichedFunctor.contravariantRepresentable V B b) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanWeight_obj (j : EnrichedFunctor V A B) (b : B) (a : A) :
    (leftKanWeight j b).obj (op a) = (j.obj a ⟶[V] b) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private abbrev leftKanPostBase (b c z : B) :
    (b ⟶[V] c) ⊗ (z ⟶[V] b) ⟶ (z ⟶[V] c) :=
  eComp V (op c) (op b) (op z)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPostBase_eq (b c z : B) :
    leftKanPostBase (V := V) b c z =
      (β_ (b ⟶[V] c) (z ⟶[V] b)).hom ≫ eComp V z b c :=
  eComp_op_eq V (op z) (op b) (op c)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private abbrev leftKanPreBase (j : EnrichedFunctor V A B)
    (b : B) (a a' : A) :
    (j.obj a' ⟶[V] b) ⊗ (a ⟶[V] a') ⟶ (j.obj a ⟶[V] b) :=
  ((j.obj a' ⟶[V] b) ◁ j.map a a') ≫
    eComp V (op b) (op (j.obj a')) (op (j.obj a))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanWeight_map_uncurry
    (j : EnrichedFunctor V A B) (b : B) (a a' : A) :
    MonoidalClosed.uncurry ((leftKanWeight j b).map (op a') (op a)) =
      leftKanPreBase j b a a' := by
  change MonoidalClosed.uncurry
      (j.map a a' ≫ MonoidalClosed.curry
        ((β_ (j.obj a' ⟶[V] b) (j.obj a ⟶[V] j.obj a')).hom ≫
          eComp V (j.obj a) (j.obj a') b)) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPostBase_id (b z : B) :
    (eId V b ▷ (z ⟶[V] b)) ≫ leftKanPostBase (V := V) b b z =
      (λ_ (z ⟶[V] b)).hom := by
  have hId := e_id_comp V (op b) (op z)
  change (λ_ (z ⟶[V] b)).inv ≫
    (eId V b ▷ (z ⟶[V] b)) ≫ leftKanPostBase (V := V) b b z =
      𝟙 (z ⟶[V] b) at hId
  apply (cancel_epi (λ_ (z ⟶[V] b)).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id] using hId

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPostBase_comp (b c d z : B) :
    (α_ (c ⟶[V] d) (b ⟶[V] c) (z ⟶[V] b)).inv ≫
        (leftKanPostBase (V := V) c d b ▷ (z ⟶[V] b)) ≫
        leftKanPostBase (V := V) b d z =
      ((c ⟶[V] d) ◁ leftKanPostBase (V := V) b c z) ≫
        leftKanPostBase (V := V) c d z :=
  e_assoc V (op d) (op c) (op b) (op z)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPostBase_weight_natural
    (j : EnrichedFunctor V A B) (b c : B) (a a' : A) :
    ((b ⟶[V] c) ◁ leftKanPreBase j b a a') ≫
        leftKanPostBase (V := V) b c (j.obj a) =
      (α_ (b ⟶[V] c) (j.obj a' ⟶[V] b) (a ⟶[V] a')).inv ≫
        (leftKanPostBase (V := V) b c (j.obj a') ▷ (a ⟶[V] a')) ≫
        leftKanPreBase j c a a' := by
  have h := e_assoc V (op c) (op b) (op (j.obj a')) (op (j.obj a))
  change
    (α_ (b ⟶[V] c) (j.obj a' ⟶[V] b) (j.obj a ⟶[V] j.obj a')).inv ≫
      (leftKanPostBase (V := V) b c (j.obj a') ▷ (j.obj a ⟶[V] j.obj a')) ≫
      eComp V (op c) (op (j.obj a')) (op (j.obj a)) =
    ((b ⟶[V] c) ◁ eComp V (op b) (op (j.obj a')) (op (j.obj a))) ≫
      leftKanPostBase (V := V) b c (j.obj a) at h
  have h' := congrArg
    (fun q => ((b ⟶[V] c) ◁
      ((j.obj a' ⟶[V] b) ◁ j.map a a')) ≫ q) h
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc] at h'
  simpa only [leftKanPostBase, leftKanPreBase,
    MonoidalCategory.whiskerLeft_comp, Category.assoc] using h'.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPreBase_identity_insert
    (j : EnrichedFunctor V A B) (a a' : A) :
    (λ_ (a ⟶[V] a')).inv ≫
        (eId V (j.obj a') ▷ (a ⟶[V] a')) ≫
        leftKanPreBase j (j.obj a') a a' = j.map a a' := by
  have hId := e_id_comp V (op (j.obj a')) (op (j.obj a))
  change (λ_ (j.obj a ⟶[V] j.obj a')).inv ≫
      (eId V (j.obj a') ▷ (j.obj a ⟶[V] j.obj a')) ≫
      eComp V (op (j.obj a')) (op (j.obj a')) (op (j.obj a)) =
    𝟙 (j.obj a ⟶[V] j.obj a') at hId
  dsimp only [leftKanPreBase]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simpa only [Category.assoc, Category.comp_id] using
    congrArg (fun q => j.map a a' ≫ q) hId

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [MonoidalClosed V] in
private theorem leftKanPostBase_identity_insert (b z : B) :
    (ρ_ (z ⟶[V] b)).inv ≫
        ((z ⟶[V] b) ◁ eId V z) ≫
        leftKanPostBase (V := V) z b z =
      𝟙 (z ⟶[V] b) :=
  e_comp_id V (op b) (op z)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorWeightSquare
    {H W W' P C C' X : V}
    (rho : W' ⊗ P ⟶ W) (rho' : C' ⊗ P ⟶ C)
    (sigma : H ⊗ W ⟶ C) (sigma' : H ⊗ W' ⟶ C')
    (h : H ◁ rho ≫ sigma =
      (α_ H W' P).inv ≫ (sigma' ▷ P) ≫ rho') :
    (H ◁ ((α_ W' P X).inv ≫ (rho ▷ X))) ≫
        (α_ H W X).inv ≫ (sigma ▷ X) =
      (α_ H W' (P ⊗ X)).inv ≫ (sigma' ▷ (P ⊗ X)) ≫
        (α_ C' P X).inv ≫ (rho' ▷ X) := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, h]
  simp only [comp_whiskerRight]
  rw [pentagon_inv_assoc, ← associator_inv_naturality_left_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorDiagramSquare
    {H W C X Y : V} (f : X ⟶ Y) (sigma : H ⊗ W ⟶ C) :
    (H ◁ (W ◁ f)) ≫ (α_ H W Y).inv ≫ (sigma ▷ Y) =
      (α_ H W X).inv ≫ (sigma ▷ X) ≫ (C ◁ f) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorActionIdentity
    {H W X : V} (e : 𝟙_ V ⟶ H) (sigma : H ⊗ W ⟶ W)
    (h : (e ▷ W) ≫ sigma = (λ_ W).hom) :
    (e ▷ (W ⊗ X)) ≫ (α_ H W X).inv ≫ (sigma ▷ X) =
      (λ_ (W ⊗ X)).hom := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, h]
  exact (leftUnitor_tensor_hom W X).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorActionComposition
    {K H J W W' W'' X : V}
    (r : K ⊗ H ⟶ J)
    (sigma : H ⊗ W ⟶ W') (sigma' : K ⊗ W' ⟶ W'')
    (sigma'' : J ⊗ W ⟶ W'')
    (h : (α_ K H W).inv ≫ (r ▷ W) ≫ sigma'' =
      (K ◁ sigma) ≫ sigma') :
    (α_ K H (W ⊗ X)).hom ≫
        (K ◁ ((α_ H W X).inv ≫ (sigma ▷ X))) ≫
        (α_ K W' X).inv ≫ (sigma' ▷ X) =
      (r ▷ (W ⊗ X)) ≫ (α_ J W X).inv ≫ (sigma'' ▷ X) := by
  have h' := congrArg (fun q => (α_ K H W).hom ≫ q) h
  have hc : (α_ K H W).hom ≫ (K ◁ sigma) ≫ sigma' =
      (r ▷ W) ≫ sigma'' := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'.symm
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    pentagon_hom_inv_inv_inv_hom_assoc, associator_inv_naturality_left_assoc]
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun q => (α_ (K ⊗ H) W X).inv ≫ (q ▷ X)) hc

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorPostIdentityInsert
    {H W X : V} (e : 𝟙_ V ⟶ W) (sigma : H ⊗ W ⟶ H)
    (h : (ρ_ H).inv ≫ (H ◁ e) ≫ sigma = 𝟙 H) :
    (H ◁ ((λ_ X).inv ≫ (e ▷ X))) ≫
        (α_ H W X).inv ≫ (sigma ▷ X) = 𝟙 (H ⊗ X) := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← triangle_assoc_comp_right_inv_assoc, Iso.hom_inv_id_assoc]
  simpa only [comp_whiskerRight, id_whiskerRight, Category.assoc] using
    congrArg (fun q => q ▷ X) h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorPreIdentityInsert
    {P Q W X : V} (e : 𝟙_ V ⟶ W) (rho : W ⊗ P ⟶ Q) (f : P ⟶ Q)
    (h : (λ_ P).inv ≫ (e ▷ P) ≫ rho = f) :
    (λ_ (P ⊗ X)).inv ≫ (e ▷ (P ⊗ X)) ≫
        (α_ W P X).inv ≫ (rho ▷ X) = f ▷ X := by
  rw [leftUnitor_tensor_inv, associator_inv_naturality_left_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun q => q ▷ X) h

section CoendTensorExtensionality

variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
  [HasCoproduct (Enriched.weightedCoend.relations W F)]
  [HasCoproduct (Enriched.weightedCoend.objects W F)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W F)
    (Enriched.weightedCoend.rightMap W F)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanCoendTensor_hom_ext
    {K Z : V} {f g : K ⊗ Enriched.weightedCoend W F ⟶ Z}
    (h : ∀ a : A, (K ◁ Enriched.weightedCoend.ι W F a) ≫ f =
      (K ◁ Enriched.weightedCoend.ι W F a) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply Enriched.weightedCoend.hom_ext W F
  intro a
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  exact congrArg MonoidalClosed.curry (h a)

end CoendTensorExtensionality


/-!
Verified unit-graded action component, appended inside the namespace of
formalization-ready-leaves.lean, before its final namespace end.
The fragment constructs Lan's actual coend B-Hom action from the proved
opposite-composition and exact tensor-square leaves. It does not use the
co-Yoneda blueprint prerequisite.
-/

section LeftKanCoendAction

variable (j : EnrichedFunctor V A B) (X : EnrichedFunctor V A V)
  [∀ b : B, HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X)]
  [∀ b : B, HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X)]
  [∀ b : B, HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X)
    (Enriched.weightedCoend.rightMap (leftKanWeight j b) X)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The literal particular weighted coend at the supplied target object. -/
abbrev leftKanCoendObject (b : B) : V :=
  Enriched.weightedCoend (leftKanWeight j b) X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The complete Hom-graded generator action. -/
@[no_expose]
def leftKanCoendActionComponent (b c : B) (a : A) :
    (b ⟶[V] c) ⊗ ((j.obj a ⟶[V] b) ⊗ X.obj a) ⟶
      leftKanCoendObject j X c :=
  (α_ (b ⟶[V] c) (j.obj a ⟶[V] b) (X.obj a)).inv ≫
    (leftKanPostBase (V := V) b c (j.obj a) ▷ X.obj a) ≫
      Enriched.weightedCoend.ι (leftKanWeight j c) X a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendActionComponent_eq (b c : B) (a : A) :
    leftKanCoendActionComponent j X b c a =
      (α_ (b ⟶[V] c) (j.obj a ⟶[V] b) (X.obj a)).inv ≫
        (((β_ (b ⟶[V] c) (j.obj a ⟶[V] b)).hom ≫
          eComp V (j.obj a) b c) ▷ X.obj a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j c) X a := by
  unfold leftKanCoendActionComponent
  rw [leftKanPostBase_eq]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanCoendActionComponent_condition
    (b c : B) (a a' : A) :
    ((b ⟶[V] c) ◁
      ((α_ ((leftKanWeight j b).obj (op a')) (a ⟶[V] a') (X.obj a)).inv ≫
        (MonoidalClosed.uncurry ((leftKanWeight j b).map (op a') (op a)) ⊗ₘ
          𝟙 (X.obj a)))) ≫ leftKanCoendActionComponent j X b c a =
      ((b ⟶[V] c) ◁
        (((leftKanWeight j b).obj (op a')) ◁
          ((β_ (a ⟶[V] a') (X.obj a)).hom ≫
            MonoidalClosed.uncurry (X.map a a')))) ≫
        leftKanCoendActionComponent j X b c a' := by
  let H : V := b ⟶[V] c
  let W' : V := j.obj a' ⟶[V] b
  let C' : V := j.obj a' ⟶[V] c
  let P : V := a ⟶[V] a'
  let Xa : V := X.obj a
  let ax : P ⊗ Xa ⟶ X.obj a' :=
    (β_ P Xa).hom ≫ MonoidalClosed.uncurry (X.map a a')
  let r : H ⊗ (W' ⊗ (P ⊗ Xa)) ⟶ C' ⊗ (P ⊗ Xa) :=
    (α_ H W' (P ⊗ Xa)).inv ≫
      (leftKanPostBase (V := V) b c (j.obj a') ▷ (P ⊗ Xa))
  have hw := leftKanTensorWeightSquare
    (X := Xa) (leftKanPreBase j b a a') (leftKanPreBase j c a a')
    (leftKanPostBase (V := V) b c (j.obj a))
    (leftKanPostBase (V := V) b c (j.obj a'))
    (leftKanPostBase_weight_natural j b c a a')
  have hd := leftKanTensorDiagramSquare ax
    (leftKanPostBase (V := V) b c (j.obj a'))
  have hc := Enriched.weightedCoend.condition (leftKanWeight j c) X a a'
  rw [leftKanWeight_map_uncurry, tensorHom_id] at hc
  rw [leftKanWeight_map_uncurry, tensorHom_id]
  change (H ◁ ((α_ W' P Xa).inv ≫
      (leftKanPreBase j b a a' ▷ Xa))) ≫
      leftKanCoendActionComponent j X b c a =
    (H ◁ (W' ◁ ax)) ≫ leftKanCoendActionComponent j X b c a'
  calc
    _ = r ≫
        ((α_ C' P Xa).inv ≫ (leftKanPreBase j c a a' ▷ Xa)) ≫
        Enriched.weightedCoend.ι (leftKanWeight j c) X a := by
      simpa only [r, H, W', C', P, Xa, leftKanCoendActionComponent,
        Category.assoc] using
        congrArg (fun q => q ≫ Enriched.weightedCoend.ι (leftKanWeight j c) X a) hw
    _ = r ≫ (C' ◁ ax) ≫ Enriched.weightedCoend.ι (leftKanWeight j c) X a' := by
      simpa only [C', P, Xa, ax, leftKanWeight_obj, Category.assoc] using
        congrArg (fun q => r ≫ q) hc
    _ = _ := by
      simpa only [r, H, W', C', P, Xa, ax, leftKanCoendActionComponent,
        Category.assoc] using
        (congrArg (fun q =>
          q ≫ Enriched.weightedCoend.ι (leftKanWeight j c) X a') hd).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Descend the Hom-graded action by the original weighted coend. -/
@[no_expose]
def leftKanCoendAction (b c : B) :
    (b ⟶[V] c) ⊗ leftKanCoendObject j X b ⟶ leftKanCoendObject j X c :=
  MonoidalClosed.uncurry <|
    Enriched.weightedCoend.desc (leftKanWeight j b) X
      (fun a => MonoidalClosed.curry (leftKanCoendActionComponent j X b c a)) (by
        intro a a'
        rw [← MonoidalClosed.curry_natural_left,
          ← MonoidalClosed.curry_natural_left]
        exact congrArg MonoidalClosed.curry
          (leftKanCoendActionComponent_condition j X b c a a'))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The complete B-Hom action retains every original coend generator. -/
@[reassoc]
theorem leftKanCoendAction_ι (b c : B) (a : A) :
    ((b ⟶[V] c) ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X a) ≫
      leftKanCoendAction j X b c =
        leftKanCoendActionComponent j X b c a := by
  unfold leftKanCoendAction
  rw [← MonoidalClosed.uncurry_natural_left,
    Enriched.weightedCoend.ι_desc, MonoidalClosed.uncurry_curry]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanCoendAction_id (b : B) :
    (eId V b ▷ leftKanCoendObject j X b) ≫ leftKanCoendAction j X b b =
      (λ_ (leftKanCoendObject j X b)).hom := by
  apply leftKanCoendTensor_hom_ext (leftKanWeight j b) X
  intro a
  rw [whisker_exchange_assoc, leftKanCoendAction_ι]
  have hId := leftKanTensorActionIdentity (X := X.obj a) (eId V b)
    (leftKanPostBase (V := V) b b (j.obj a))
    (leftKanPostBase_id (V := V) b (j.obj a))
  have hUnit := (leftUnitor_naturality
    (Enriched.weightedCoend.ι (leftKanWeight j b) X a))
  rw [hUnit]
  simpa only [leftKanCoendActionComponent, Category.assoc] using
    congrArg (fun q => q ≫ Enriched.weightedCoend.ι (leftKanWeight j b) X a) hId

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanCoendAction_comp_op (b c d : B) :
    (leftKanPostBase (V := V) c d b ▷ leftKanCoendObject j X b) ≫
        leftKanCoendAction j X b d =
      (α_ (c ⟶[V] d) (b ⟶[V] c) (leftKanCoendObject j X b)).hom ≫
        ((c ⟶[V] d) ◁ leftKanCoendAction j X b c) ≫
        leftKanCoendAction j X c d := by
  apply leftKanCoendTensor_hom_ext (leftKanWeight j b) X
  intro a
  rw [whisker_exchange_assoc, leftKanCoendAction_ι,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    leftKanCoendAction_ι]
  simp only [leftKanCoendActionComponent, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [leftKanCoendAction_ι]
  have hBase := leftKanPostBase_comp (V := V) b c d (j.obj a)
  have hTensor := leftKanTensorActionComposition (X := X.obj a)
    (leftKanPostBase (V := V) c d b)
    (leftKanPostBase (V := V) b c (j.obj a))
    (leftKanPostBase (V := V) c d (j.obj a))
    (leftKanPostBase (V := V) b d (j.obj a)) hBase
  simpa only [leftKanCoendActionComponent,
    MonoidalCategory.whiskerLeft_comp, Category.assoc] using
    (congrArg (fun q =>
      q ≫ Enriched.weightedCoend.ι (leftKanWeight j d) X a) hTensor).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanCoendAction_comp (b c d : B) :
    (eComp V b c d ▷ leftKanCoendObject j X b) ≫
        leftKanCoendAction j X b d =
      ((β_ (c ⟶[V] d) (b ⟶[V] c)).inv ▷ leftKanCoendObject j X b) ≫
        (α_ (c ⟶[V] d) (b ⟶[V] c) (leftKanCoendObject j X b)).hom ≫
        ((c ⟶[V] d) ◁ leftKanCoendAction j X b c) ≫
        leftKanCoendAction j X c d := by
  have hOp := leftKanCoendAction_comp_op j X b c d
  rw [leftKanPostBase_eq, comp_whiskerRight] at hOp
  have h := congrArg
    (fun q => ((β_ (c ⟶[V] d) (b ⟶[V] c)).inv ▷
      leftKanCoendObject j X b) ≫ q) hOp
  simp only [Category.assoc] at h
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp] at h
  exact h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The actual enriched map is the inverse-braided transpose of the action. -/
def leftKanCoendMap (b c : B) :
    (b ⟶[V] c) ⟶
      (ihom (leftKanCoendObject j X b)).obj (leftKanCoendObject j X c) :=
  MonoidalClosed.curry <|
    (β_ (b ⟶[V] c) (leftKanCoendObject j X b)).inv ≫
      leftKanCoendAction j X b c

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendMap_uncurry (b c : B) :
    MonoidalClosed.uncurry (leftKanCoendMap j X b c) =
      (β_ (b ⟶[V] c) (leftKanCoendObject j X b)).inv ≫
        leftKanCoendAction j X b c := by
  unfold leftKanCoendMap
  rw [MonoidalClosed.uncurry_curry]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendMap_id (b : B) :
    eId V b ≫ leftKanCoendMap j X b b =
      eId V (leftKanCoendObject j X b) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, leftKanCoendMap_uncurry,
    MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
    MonoidalClosed.uncurry_curry]
  rw [braiding_inv_naturality_right_assoc, leftKanCoendAction_id]
  rw [← braiding_rightUnitor]
  simp

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendMap_comp (b c d : B) :
    eComp V b c d ≫ leftKanCoendMap j X b d =
      (leftKanCoendMap j X b c ⊗ₘ leftKanCoendMap j X c d) ≫
        eComp V (leftKanCoendObject j X b)
          (leftKanCoendObject j X c) (leftKanCoendObject j X d) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, leftKanCoendMap_uncurry,
    MonoidalClosed.uncurry_eComp, leftKanCoendMap_uncurry, leftKanCoendMap_uncurry]
  rw [braiding_inv_naturality_right_assoc, leftKanCoendAction_comp]
  simp only [comp_whiskerRight, Category.assoc]
  rw [braiding_inv_naturality_left_assoc]
  rw [braiding_tensor_left_inv, braiding_tensor_right_inv]
  simp only [Category.assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The weighted-coend values with their complete B-Hom maps form the enriched Lan. -/
def leftKanCoendFunctor : EnrichedFunctor V B V where
  obj := leftKanCoendObject j X
  map := leftKanCoendMap j X
  map_id := leftKanCoendMap_id j X
  map_comp := leftKanCoendMap_comp j X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendFunctor_obj (b : B) :
    (leftKanCoendFunctor j X).obj b = leftKanCoendObject j X b := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanCoendFunctor_map (b c : B) :
    (leftKanCoendFunctor j X).map b c = leftKanCoendMap j X b c := rfl

end LeftKanCoendAction


/-!
Verified unit-graded diagram/unit component in the same namespace.
This gives Lan's actual unit-graded diagram functor, identity insertion,
full A-Hom naturality of the unit and the whole B-Hom generator identity.
No use of the pending co-Yoneda characteristic is made.
-/

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanIdentityTensor_natural
    {P Q W : V} (e : 𝟙_ V ⟶ W) (f : P ⟶ Q) :
    (λ_ P).inv ≫ (e ▷ P) ≫ (W ◁ f) =
      f ≫ (λ_ Q).inv ≫ (e ▷ Q) := by
  rw [← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

section LeftKanDiagram

variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The full coend enriched functor, in the category of genuine transformations. -/
abbrev leftKanObject (X : EnrichedFunctorCat V A) : EnrichedFunctorCat V B :=
  ⟨leftKanCoendFunctor j X.toEnrichedFunctor⟩

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Actual diagram variance on the original weighted coend. -/
def leftKanMapComponent {X X' : EnrichedFunctorCat V A}
    (t : X ⟶ X') (b : B) :
    leftKanCoendObject j X.toEnrichedFunctor b ⟶
      leftKanCoendObject j X'.toEnrichedFunctor b :=
  Enriched.weightedCoend.mapDiagramGraded (leftKanWeight j b) t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
@[reassoc]
theorem leftKanMapComponent_ι {X X' : EnrichedFunctorCat V A}
    (t : X ⟶ X') (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a ≫
        leftKanMapComponent j t b =
      (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component t a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j b) X'.toEnrichedFunctor a :=
  Enriched.weightedCoend.mapDiagramGraded_ι (leftKanWeight j b) t a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanMapComponent_id (X : EnrichedFunctorCat V A) (b : B) :
    leftKanMapComponent j (𝟙 X) b =
      𝟙 (leftKanCoendObject j X.toEnrichedFunctor b) :=
  Enriched.weightedCoend.mapDiagramGraded_id (leftKanWeight j b) X.toEnrichedFunctor

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanMapComponent_comp {X X' X'' : EnrichedFunctorCat V A}
    (t : X ⟶ X') (s : X' ⟶ X'') (b : B) :
    leftKanMapComponent j (t ≫ s) b =
      leftKanMapComponent j t b ≫ leftKanMapComponent j s b :=
  Enriched.weightedCoend.mapDiagramGraded_comp (leftKanWeight j b) t s

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanMapComponent_action_natural
    {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') (b c : B) :
    leftKanCoendAction j X.toEnrichedFunctor b c ≫ leftKanMapComponent j t c =
      ((b ⟶[V] c) ◁ leftKanMapComponent j t b) ≫
        leftKanCoendAction j X'.toEnrichedFunctor b c := by
  apply leftKanCoendTensor_hom_ext (leftKanWeight j b) X.toEnrichedFunctor
  intro a
  have hCore :
      leftKanCoendActionComponent j X.toEnrichedFunctor b c a ≫
          leftKanMapComponent j t c =
        ((b ⟶[V] c) ◁ (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component t a)) ≫
          leftKanCoendActionComponent j X'.toEnrichedFunctor b c a := by
    unfold leftKanCoendActionComponent
    simp only [Category.assoc]
    rw [leftKanMapComponent_ι]
    have ht := leftKanTensorDiagramSquare (component t a)
      (leftKanPostBase (V := V) b c (j.obj a))
    simpa only [id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc] using
      (congrArg (fun q => q ≫ Enriched.weightedCoend.ι
        (leftKanWeight j c) X'.toEnrichedFunctor a) ht).symm
  calc
    _ = leftKanCoendActionComponent j X.toEnrichedFunctor b c a ≫
        leftKanMapComponent j t c := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ leftKanMapComponent j t c)
          (leftKanCoendAction_ι j X.toEnrichedFunctor b c a)
    _ = ((b ⟶[V] c) ◁ (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component t a)) ≫
        leftKanCoendActionComponent j X'.toEnrichedFunctor b c a := hCore
    _ = _ := by
      have hm := leftKanMapComponent_ι j t b a
      have he := congrArg (fun q =>
        ((b ⟶[V] c) ◁ q) ≫ leftKanCoendAction j X'.toEnrichedFunctor b c) hm
      rw [← leftKanCoendAction_ι]
      simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using he.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanMapComponent_natural
    {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') (b c : B) :
    MonoidalClosed.uncurry ((leftKanObject j X).toEnrichedFunctor.map b c) ≫
        leftKanMapComponent j t c =
      (leftKanMapComponent j t b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry ((leftKanObject j X').toEnrichedFunctor.map b c) := by
  change MonoidalClosed.uncurry (leftKanCoendMap j X.toEnrichedFunctor b c) ≫
      leftKanMapComponent j t c =
    (leftKanMapComponent j t b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry (leftKanCoendMap j X'.toEnrichedFunctor b c)
  rw [leftKanCoendMap_uncurry, leftKanCoendMap_uncurry, tensorHom_id,
    Category.assoc, leftKanMapComponent_action_natural,
    ← braiding_inv_naturality_left_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The whole diagram map is a genuine unit-graded enriched transformation. -/
@[no_expose]
def leftKanMap {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') :
    leftKanObject j X ⟶ leftKanObject j X' :=
  GradedNatTrans.unitOfComponents (fun b => leftKanMapComponent j t b)
    (fun b c => leftKanMapComponent_natural j t b c)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanMap_component {X X' : EnrichedFunctorCat V A}
    (t : X ⟶ X') (b : B) :
    component (leftKanMap j t) b = leftKanMapComponent j t b :=
  GradedNatTrans.unitOfComponents_component _ _ b

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The actual left extension is a functor on full unit-graded transformations. -/
abbrev leftKan : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V B where
  obj := leftKanObject j
  map := fun t => leftKanMap j t
  map_id X := by
    apply hom_ext
    intro b
    exact ((leftKanMap_component j (𝟙 X) b).trans
      (leftKanMapComponent_id j X b)).trans (component_id (leftKanObject j X) b).symm
  map_comp t s := by
    apply hom_ext
    intro b
    have hLeft := (leftKanMap_component j (t ≫ s) b).trans
      (leftKanMapComponent_comp j t s b)
    have hRight := (component_comp (leftKanMap j t) (leftKanMap j s) b).trans
      (congrArg₂ (fun f g => f ≫ g)
        (leftKanMap_component j t b) (leftKanMap_component j s b))
    exact hLeft.trans hRight.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKan_obj (X : EnrichedFunctorCat V A) (b : B) :
    ((leftKan j).obj X).toEnrichedFunctor.obj b =
      Enriched.weightedCoend (leftKanWeight j b) X.toEnrichedFunctor := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKan_fullMap (X : EnrichedFunctorCat V A) (b c : B) :
    ((leftKan j).obj X).toEnrichedFunctor.map b c =
      leftKanCoendMap j X.toEnrichedFunctor b c := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Insert the original enriched identity into its exact coend generator. -/
def leftKanUnitComponent (X : EnrichedFunctorCat V A) (a : A) :
    X.toEnrichedFunctor.obj a ⟶
      leftKanCoendObject j X.toEnrichedFunctor (j.obj a) :=
  (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
    (eId V (j.obj a) ▷ X.toEnrichedFunctor.obj a) ≫
      Enriched.weightedCoend.ι (leftKanWeight j (j.obj a)) X.toEnrichedFunctor a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The complete B-Hom action on the inserted unit is the original generator. -/
@[reassoc]
theorem leftKanUnitComponent_action
    (X : EnrichedFunctorCat V A) (a : A) (b : B) :
    ((j.obj a ⟶[V] b) ◁ leftKanUnitComponent j X a) ≫
        leftKanCoendAction j X.toEnrichedFunctor (j.obj a) b =
      Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a := by
  unfold leftKanUnitComponent
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [leftKanCoendAction_ι]
  have h := leftKanTensorPostIdentityInsert (X := X.toEnrichedFunctor.obj a)
    (eId V (j.obj a)) (leftKanPostBase (V := V) (j.obj a) b (j.obj a))
    (leftKanPostBase_identity_insert (V := V) b (j.obj a))
  simpa only [leftKanCoendActionComponent, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Category.id_comp] using
    congrArg (fun q => q ≫
      Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanUnitComponent_source_relation
    (X : EnrichedFunctorCat V A) (a a' : A) :
    (j.map a a' ▷ X.toEnrichedFunctor.obj a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a =
      (β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') ≫
        leftKanUnitComponent j X a' := by
  let P : V := a ⟶[V] a'
  let Xa : V := X.toEnrichedFunctor.obj a
  let ax : P ⊗ Xa ⟶ X.toEnrichedFunctor.obj a' :=
    (β_ P Xa).hom ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a')
  let ins : P ⊗ Xa ⟶ (j.obj a' ⟶[V] j.obj a') ⊗ (P ⊗ Xa) :=
    (λ_ (P ⊗ Xa)).inv ≫ (eId V (j.obj a') ▷ (P ⊗ Xa))
  have hc := Enriched.weightedCoend.condition
    (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a a'
  rw [leftKanWeight_map_uncurry, tensorHom_id] at hc
  have hcp := congrArg (fun q => ins ≫ q) hc
  have hw := leftKanTensorPreIdentityInsert (X := Xa) (eId V (j.obj a'))
    (leftKanPreBase j (j.obj a') a a') (j.map a a')
    (leftKanPreBase_identity_insert j a a')
  have hd := leftKanIdentityTensor_natural (eId V (j.obj a')) ax
  calc
    _ = ins ≫
        ((α_ (j.obj a' ⟶[V] j.obj a') P Xa).inv ≫
          (leftKanPreBase j (j.obj a') a a' ▷ Xa)) ≫
        Enriched.weightedCoend.ι (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a := by
      simpa only [ins, P, Xa, Category.assoc] using
        (congrArg (fun q => q ≫ Enriched.weightedCoend.ι
          (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a) hw).symm
    _ = ins ≫ ((j.obj a' ⟶[V] j.obj a') ◁ ax) ≫
        Enriched.weightedCoend.ι (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a' := by
      simpa only [P, Xa, ax, leftKanWeight_obj, Category.assoc] using hcp
    _ = _ := by
      simpa only [ins, P, Xa, ax, leftKanUnitComponent, Category.assoc] using
        congrArg (fun q => q ≫ Enriched.weightedCoend.ι
          (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a') hd

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanUnitComponent_natural
    (X : EnrichedFunctorCat V A) (a a' : A) :
    MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') ≫
        leftKanUnitComponent j X a' =
      (leftKanUnitComponent j X a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
        MonoidalClosed.uncurry
          ((restrictionObject j (leftKanObject j X)).toEnrichedFunctor.map a a') := by
  let P : V := a ⟶[V] a'
  let Xa : V := X.toEnrichedFunctor.obj a
  let ax : P ⊗ Xa ⟶ X.toEnrichedFunctor.obj a' :=
    (β_ P Xa).hom ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a')
  have hLeft : ax ≫ leftKanUnitComponent j X a' =
      (P ◁ leftKanUnitComponent j X a) ≫
        (j.map a a' ▷ leftKanCoendObject j X.toEnrichedFunctor (j.obj a)) ≫
        leftKanCoendAction j X.toEnrichedFunctor (j.obj a) (j.obj a') := by
    calc
      _ = (j.map a a' ▷ Xa) ≫ Enriched.weightedCoend.ι
          (leftKanWeight j (j.obj a')) X.toEnrichedFunctor a := by
        simpa only [P, Xa, ax, Category.assoc] using
          (leftKanUnitComponent_source_relation j X a a').symm
      _ = _ := by
        rw [whisker_exchange_assoc, leftKanUnitComponent_action]
  change MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') ≫
      leftKanUnitComponent j X a' =
    (leftKanUnitComponent j X a ⊗ₘ 𝟙 P) ≫
      MonoidalClosed.uncurry
        (j.map a a' ≫ leftKanCoendMap j X.toEnrichedFunctor (j.obj a) (j.obj a'))
  rw [tensorHom_id, MonoidalClosed.uncurry_natural_left, leftKanCoendMap_uncurry]
  rw [braiding_inv_naturality_right_assoc, braiding_inv_naturality_left_assoc,
    ← hLeft]
  simp only [P, Xa, ax, Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The identity insertions form a full genuine enriched unit transformation. -/
@[no_expose]
def leftKanUnit (X : EnrichedFunctorCat V A) :
    X ⟶ restrictionObject j (leftKanObject j X) :=
  GradedNatTrans.unitOfComponents (leftKanUnitComponent j X)
    (leftKanUnitComponent_natural j X)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanUnit_component (X : EnrichedFunctorCat V A) (a : A) :
    component (leftKanUnit j X) a = leftKanUnitComponent j X a :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanUnit_natural {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') :
    t ≫ leftKanUnit j X' =
      leftKanUnit j X ≫ restrictionMap j (leftKanMap j t) := by
  apply hom_ext
  intro a
  rw [component_comp, component_comp, leftKanUnit_component, leftKanUnit_component,
    restrictionMap_component, leftKanMap_component]
  change component t a ≫ leftKanUnitComponent j X' a =
    leftKanUnitComponent j X a ≫ leftKanMapComponent j t (j.obj a)
  have hm := leftKanMapComponent_ι j t (j.obj a) a
  have hp := congrArg (fun q =>
    ((λ_ (X.toEnrichedFunctor.obj a)).inv ≫
      (eId V (j.obj a) ▷ X.toEnrichedFunctor.obj a)) ≫ q) hm
  simp only [id_tensorHom, Category.assoc] at hp
  have hn := congrArg (fun q => q ≫ Enriched.weightedCoend.ι
    (leftKanWeight j (j.obj a)) X'.toEnrichedFunctor a)
      (leftKanIdentityTensor_natural (eId V (j.obj a)) (component t a))
  simp only [Category.assoc] at hn
  simpa only [leftKanUnitComponent, Category.assoc] using (hp.trans hn).symm

end LeftKanDiagram


/-!
Private Hom-correspondence fragment. The primary installed and this lane
reloaded the fully proved co-Yoneda dependency before this implementation.
Append after the action/diagram/unit fragments in the same namespace.
-/

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private def leftKanRestrictedComponent
    (j : EnrichedFunctor V A B) {X : EnrichedFunctorCat V A}
    {Y : EnrichedFunctorCat V B} (f : X ⟶ restrictionObject j Y) (a : A) :
    X.toEnrichedFunctor.obj a ⟶ Y.toEnrichedFunctor.obj (j.obj a) :=
  component f a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private abbrev leftKanTargetAction (Y : EnrichedFunctorCat V B) (b c : B) :
    (b ⟶[V] c) ⊗ Y.toEnrichedFunctor.obj b ⟶ Y.toEnrichedFunctor.obj c :=
  (β_ (b ⟶[V] c) (Y.toEnrichedFunctor.obj b)).hom ≫
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftKanTensorPairSquare
    {W P Q X Y U : V} (p : P ⟶ Q) (f : X ⟶ Y) (r : W ⊗ Q ⟶ U) :
    (W ◁ (p ⊗ₘ f)) ≫ (α_ W Q Y).inv ≫ (r ▷ Y) =
      (α_ W P X).inv ≫ ((W ◁ p ≫ r) ▷ X) ≫ (U ◁ f) := by
  rw [tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictedAction_natural
    (j : EnrichedFunctor V A B) {X : EnrichedFunctorCat V A}
    {Y : EnrichedFunctorCat V B} (f : X ⟶ restrictionObject j Y) (a a' : A) :
    (β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') ≫ leftKanRestrictedComponent j f a' =
      ((a ⟶[V] a') ◁ leftKanRestrictedComponent j f a) ≫
        (j.map a a' ▷ Y.toEnrichedFunctor.obj (j.obj a)) ≫
        leftKanTargetAction Y (j.obj a) (j.obj a') := by
  have hn : MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') ≫
      leftKanRestrictedComponent j f a' =
    (leftKanRestrictedComponent j f a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
      MonoidalClosed.uncurry
        (j.map a a' ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) :=
    f.uncurriedNaturality a a'
  have h := congrArg (fun q =>
    (β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫ q) hn
  rw [tensorHom_id, MonoidalClosed.uncurry_natural_left] at h
  rw [← braiding_naturality_right_assoc, ← braiding_naturality_left_assoc] at h
  exact h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The original whole-Hom generator family for the inverse Hom correspondence. -/
@[no_expose]
def leftKanTransposeCocone (j : EnrichedFunctor V A B)
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) (a : A) :
    (j.obj a ⟶[V] b) ⊗ X.toEnrichedFunctor.obj a ⟶ Y.toEnrichedFunctor.obj b :=
  (𝟙 (j.obj a ⟶[V] b) ⊗ₘ leftKanRestrictedComponent j f a) ≫
    (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransposeCocone_eq_private (j : EnrichedFunctor V A B)
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) (a : A) :
    leftKanTransposeCocone j X Y f b a =
      (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanTransposeCocone_eq (j : EnrichedFunctor V A B)
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) (a : A) :
    leftKanTransposeCocone j X Y f b a =
      (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
  leftKanTransposeCocone_eq_private j X Y f b a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransposeCocone_condition
    (j : EnrichedFunctor V A B) (X : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V B) (f : X ⟶ restrictionObject j Y)
    (b : B) (a a' : A) :
    (α_ (j.obj a' ⟶[V] b) (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).inv ≫
        (leftKanPreBase j b a a' ▷ X.toEnrichedFunctor.obj a) ≫
        leftKanTransposeCocone j X Y f b a =
      ((j.obj a' ⟶[V] b) ◁
        ((β_ (a ⟶[V] a') (X.toEnrichedFunctor.obj a)).hom ≫
          MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a'))) ≫
        leftKanTransposeCocone j X Y f b a' := by
  let W' : V := j.obj a' ⟶[V] b
  let P : V := a ⟶[V] a'
  let H : V := j.obj a ⟶[V] j.obj a'
  let Ya : V := Y.toEnrichedFunctor.obj (j.obj a)
  let rB : W' ⊗ H ⟶ (j.obj a ⟶[V] b) :=
    (β_ W' H).hom ≫ eComp V (j.obj a) (j.obj a') b
  let pre : W' ⊗ (P ⊗ X.toEnrichedFunctor.obj a) ⟶ W' ⊗ (H ⊗ Ya) :=
    W' ◁ (j.map a a' ⊗ₘ leftKanRestrictedComponent j f a)
  have hPre : W' ◁ j.map a a' ≫ rB = leftKanPreBase j b a a' := rfl
  have ht := leftKanTensorPairSquare (j.map a a') (leftKanRestrictedComponent j f a) rB
  rw [hPre] at ht
  have hy :
      (α_ W' H Ya).inv ≫ (rB ▷ Ya) ≫ leftKanTargetAction Y (j.obj a) b =
        (W' ◁ leftKanTargetAction Y (j.obj a) (j.obj a')) ≫
          leftKanTargetAction Y (j.obj a') b := by
    simpa only [W', H, Ya, rB, leftKanTargetAction, tensorHom_id, Category.assoc] using
      Enriched.weightedCoend.coyonedaCondition Y.toEnrichedFunctor b (j.obj a) (j.obj a')
  have hf := congrArg (fun q =>
    (W' ◁ q) ≫ leftKanTargetAction Y (j.obj a') b)
      (leftKanRestrictedAction_natural j f a a')
  have hTensor := tensorHom_def' (j.map a a') (leftKanRestrictedComponent j f a)
  calc
    _ = pre ≫ (α_ W' H Ya).inv ≫ (rB ▷ Ya) ≫
        leftKanTargetAction Y (j.obj a) b := by
      simpa only [pre, W', P, H, Ya, leftKanTransposeCocone, leftKanTargetAction,
        id_tensorHom, Category.assoc] using
        (congrArg (fun q => q ≫ leftKanTargetAction Y (j.obj a) b) ht).symm
    _ = pre ≫ (W' ◁ leftKanTargetAction Y (j.obj a) (j.obj a')) ≫
        leftKanTargetAction Y (j.obj a') b := by
      simpa only [Category.assoc] using congrArg (fun q => pre ≫ q) hy
    _ = _ := by
      simpa only [pre, W', P, H, Ya, leftKanTransposeCocone, leftKanTargetAction,
        hTensor, id_tensorHom, MonoidalCategory.whiskerLeft_comp,
        Category.assoc] using hf.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransposeCocone_output_natural
    (j : EnrichedFunctor V A B) (X : EnrichedFunctorCat V A)
    (Y : EnrichedFunctorCat V B) (f : X ⟶ restrictionObject j Y)
    (b c : B) (a : A) :
    (α_ (b ⟶[V] c) (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        (leftKanPostBase (V := V) b c (j.obj a) ▷ X.toEnrichedFunctor.obj a) ≫
        leftKanTransposeCocone j X Y f c a =
      ((b ⟶[V] c) ◁ leftKanTransposeCocone j X Y f b a) ≫
        leftKanTargetAction Y b c := by
  let H : V := b ⟶[V] c
  let W : V := j.obj a ⟶[V] b
  let Ya : V := Y.toEnrichedFunctor.obj (j.obj a)
  let pre : H ⊗ (W ⊗ X.toEnrichedFunctor.obj a) ⟶ H ⊗ (W ⊗ Ya) :=
    H ◁ (W ◁ leftKanRestrictedComponent j f a)
  have ht := leftKanTensorDiagramSquare (leftKanRestrictedComponent j f a)
    (leftKanPostBase (V := V) b c (j.obj a))
  have hy :
      (α_ H W Ya).inv ≫
          (leftKanPostBase (V := V) b c (j.obj a) ▷ Ya) ≫
          leftKanTargetAction Y (j.obj a) c =
        (H ◁ leftKanTargetAction Y (j.obj a) b) ≫ leftKanTargetAction Y b c := by
    rw [leftKanPostBase_eq]
    simpa only [H, W, Ya, leftKanTargetAction, tensorHom_id, Category.assoc] using
      Enriched.weightedCoend.coyonedaCondition Y.toEnrichedFunctor c (j.obj a) b
  calc
    _ = pre ≫ (α_ H W Ya).inv ≫
        (leftKanPostBase (V := V) b c (j.obj a) ▷ Ya) ≫
        leftKanTargetAction Y (j.obj a) c := by
      simpa only [pre, H, W, Ya, leftKanTransposeCocone, leftKanTargetAction,
        id_tensorHom, Category.assoc] using
        (congrArg (fun q => q ≫ leftKanTargetAction Y (j.obj a) c) ht).symm
    _ = pre ≫ (H ◁ leftKanTargetAction Y (j.obj a) b) ≫
        leftKanTargetAction Y b c := by
      simpa only [Category.assoc] using congrArg (fun q => pre ≫ q) hy
    _ = _ := by
      simp only [pre, H, W, Ya, leftKanTransposeCocone, leftKanTargetAction,
        id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTargetAction_identity (Y : EnrichedFunctorCat V B) (b : B) :
    (λ_ (Y.toEnrichedFunctor.obj b)).inv ≫
        (eId V b ▷ Y.toEnrichedFunctor.obj b) ≫ leftKanTargetAction Y b b =
      𝟙 (Y.toEnrichedFunctor.obj b) := by
  have hu := congrArg (MonoidalClosed.uncurry (A := Y.toEnrichedFunctor.obj b))
    (Y.toEnrichedFunctor.map_id b)
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
    MonoidalClosed.uncurry_curry] at hu
  unfold leftKanTargetAction
  rw [braiding_naturality_left_assoc (eId V b) (Y.toEnrichedFunctor.obj b),
    leftUnitor_inv_braiding_assoc, hu]
  simp only [Iso.inv_hom_id]

section LeftKanHom

variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Descend the full original generator family of a restricted transformation. -/
@[no_expose]
def leftKanTransposeMapComponent
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) :
    leftKanCoendObject j X.toEnrichedFunctor b ⟶ Y.toEnrichedFunctor.obj b :=
  Enriched.weightedCoend.desc (leftKanWeight j b) X.toEnrichedFunctor
    (leftKanTransposeCocone j X Y f b) (by
      intro a a'
      rw [leftKanWeight_map_uncurry, tensorHom_id]
      simpa only [Category.assoc] using
        leftKanTransposeCocone_condition j X Y f b a a')

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
@[reassoc]
theorem leftKanTransposeMapComponent_ι
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a ≫
        leftKanTransposeMapComponent j X Y f b =
      leftKanTransposeCocone j X Y f b a := by
  unfold leftKanTransposeMapComponent
  rw [Enriched.weightedCoend.ι_desc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransposeMapComponent_action_natural
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b c : B) :
    leftKanCoendAction j X.toEnrichedFunctor b c ≫
        leftKanTransposeMapComponent j X Y f c =
      ((b ⟶[V] c) ◁ leftKanTransposeMapComponent j X Y f b) ≫
        leftKanTargetAction Y b c := by
  apply leftKanCoendTensor_hom_ext (leftKanWeight j b) X.toEnrichedFunctor
  intro a
  rw [leftKanCoendAction_ι_assoc]
  unfold leftKanCoendActionComponent
  simp only [Category.assoc]
  rw [leftKanTransposeMapComponent_ι]
  rw [← whiskerLeft_comp_assoc, leftKanTransposeMapComponent_ι]
  exact leftKanTransposeCocone_output_natural j X Y f b c a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransposeMapComponent_natural
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b c : B) :
    MonoidalClosed.uncurry ((leftKanObject j X).toEnrichedFunctor.map b c) ≫
        leftKanTransposeMapComponent j X Y f c =
      (leftKanTransposeMapComponent j X Y f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) := by
  change MonoidalClosed.uncurry (leftKanCoendMap j X.toEnrichedFunctor b c) ≫
      leftKanTransposeMapComponent j X Y f c =
    (leftKanTransposeMapComponent j X Y f b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c)
  rw [leftKanCoendMap_uncurry, tensorHom_id, Category.assoc,
    leftKanTransposeMapComponent_action_natural]
  unfold leftKanTargetAction
  rw [← braiding_inv_naturality_left_assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The inverse correspondence retains full B-Hom naturality. -/
@[no_expose]
def leftKanTransposeMap
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) : leftKanObject j X ⟶ Y :=
  GradedNatTrans.unitOfComponents (leftKanTransposeMapComponent j X Y f)
    (leftKanTransposeMapComponent_natural j X Y f)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanTransposeMap_component
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) :
    component (leftKanTransposeMap j X Y f) b =
      leftKanTransposeMapComponent j X Y f b :=
  GradedNatTrans.unitOfComponents_component _ _ b

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The original unit followed by literal enriched restriction is the forward map. -/
def leftKanHomToRestriction
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) : X ⟶ restrictionObject j Y :=
  leftKanUnit j X ≫ (restriction j).map alpha

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomToRestriction_component
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) (a : A) :
    component (leftKanHomToRestriction j X Y alpha) a =
      leftKanUnitComponent j X a ≫ component alpha (j.obj a) := by
  unfold leftKanHomToRestriction
  exact (component_comp (leftKanUnit j X) ((restriction j).map alpha) a).trans
    (congrArg₂ (fun f g => f ≫ g)
      (leftKanUnit_component j X a) (restrictionMap_component j alpha a))

end LeftKanHom


/-! The complete unit-graded universal property and its actual adjunction. -/

section LeftKanUniversal

variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private def leftKanTargetComponent {X : EnrichedFunctorCat V A}
    {Y : EnrichedFunctorCat V B} (alpha : leftKanObject j X ⟶ Y) (b : B) :
    leftKanCoendObject j X.toEnrichedFunctor b ⟶ Y.toEnrichedFunctor.obj b :=
  component alpha b

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTransformation_action_natural
    {X : EnrichedFunctorCat V A} {Y : EnrichedFunctorCat V B}
    (alpha : leftKanObject j X ⟶ Y) (b c : B) :
    leftKanCoendAction j X.toEnrichedFunctor b c ≫ leftKanTargetComponent j alpha c =
      ((b ⟶[V] c) ◁ leftKanTargetComponent j alpha b) ≫ leftKanTargetAction Y b c := by
  have hn :
      MonoidalClosed.uncurry (leftKanCoendMap j X.toEnrichedFunctor b c) ≫
          leftKanTargetComponent j alpha c =
        (leftKanTargetComponent j alpha b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) :=
    alpha.uncurriedNaturality b c
  have h := congrArg (fun q =>
    (β_ (b ⟶[V] c) (leftKanCoendObject j X.toEnrichedFunctor b)).hom ≫ q) hn
  rw [leftKanCoendMap_uncurry, tensorHom_id] at h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  rw [← braiding_naturality_right_assoc] at h
  exact h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanUnit_transpose_evaluation
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (a : A) :
    leftKanUnitComponent j X a ≫ leftKanTransposeMapComponent j X Y f (j.obj a) =
      leftKanRestrictedComponent j f a := by
  unfold leftKanUnitComponent
  simp only [Category.assoc]
  rw [leftKanTransposeMapComponent_ι]
  have hn := congrArg (fun q => q ≫ leftKanTargetAction Y (j.obj a) (j.obj a))
    (leftKanIdentityTensor_natural (eId V (j.obj a))
      (leftKanRestrictedComponent j f a))
  have ht := leftKanTargetAction_identity Y (j.obj a)
  calc
    _ = leftKanRestrictedComponent j f a ≫
        ((λ_ (Y.toEnrichedFunctor.obj (j.obj a))).inv ≫
          (eId V (j.obj a) ▷ Y.toEnrichedFunctor.obj (j.obj a)) ≫
          leftKanTargetAction Y (j.obj a) (j.obj a)) := by
      simpa only [leftKanTransposeCocone, leftKanTargetAction,
        id_tensorHom, Category.assoc] using hn
    _ = _ := by rw [ht, Category.comp_id]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanHomToRestriction_transpose_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    leftKanHomToRestriction j X Y (leftKanTransposeMap j X Y f) = f := by
  apply hom_ext
  intro a
  rw [leftKanHomToRestriction_component, leftKanTransposeMap_component]
  exact leftKanUnit_transpose_evaluation j X Y f a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Original identity insertion followed by the inverse descent recovers the supplied map. -/
theorem leftKanHomToRestriction_transpose
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    leftKanHomToRestriction j X Y (leftKanTransposeMap j X Y f) = f :=
  leftKanHomToRestriction_transpose_private j X Y f

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanTranspose_homToRestriction_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) :
    leftKanTransposeMap j X Y (leftKanHomToRestriction j X Y alpha) = alpha := by
  apply hom_ext
  intro b
  rw [leftKanTransposeMap_component]
  change leftKanTransposeMapComponent j X Y (leftKanHomToRestriction j X Y alpha) b =
    leftKanTargetComponent j alpha b
  apply Enriched.weightedCoend.hom_ext (leftKanWeight j b) X.toEnrichedFunctor
  intro a
  rw [leftKanTransposeMapComponent_ι]
  have hq :
      leftKanRestrictedComponent j (leftKanHomToRestriction j X Y alpha) a =
        leftKanUnitComponent j X a ≫ leftKanTargetComponent j alpha (j.obj a) :=
    leftKanHomToRestriction_component j X Y alpha a
  unfold leftKanTransposeCocone
  rw [hq]
  simp only [id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← leftKanTransformation_action_natural j alpha (j.obj a) b,
    leftKanUnitComponent_action_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Full B-Hom naturality and the original generator identity reconstruct every transformation. -/
theorem leftKanTranspose_homToRestriction
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) :
    leftKanTransposeMap j X Y (leftKanHomToRestriction j X Y alpha) = alpha :=
  leftKanTranspose_homToRestriction_private j X Y alpha

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The forward correspondence respects actual source transformations. -/
theorem leftKanHomToRestriction_precomp
    {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (t : X' ⟶ X) (alpha : leftKanObject j X ⟶ Y) :
    leftKanHomToRestriction j X' Y ((leftKan j).map t ≫ alpha) =
      t ≫ leftKanHomToRestriction j X Y alpha := by
  unfold leftKanHomToRestriction
  have hm := (restriction j).map_comp ((leftKan j).map t) alpha
  have hu : leftKanUnit j X' ≫ (restriction j).map ((leftKan j).map t) =
      t ≫ leftKanUnit j X :=
    (leftKanUnit_natural j t).symm
  calc
    _ = leftKanUnit j X' ≫
        ((restriction j).map ((leftKan j).map t) ≫ (restriction j).map alpha) :=
      congrArg (fun q => leftKanUnit j X' ≫ q) hm
    _ = (leftKanUnit j X' ≫ (restriction j).map ((leftKan j).map t)) ≫
        (restriction j).map alpha := (Category.assoc _ _ _).symm
    _ = (t ≫ leftKanUnit j X) ≫ (restriction j).map alpha :=
      congrArg (fun q => q ≫ (restriction j).map alpha) hu
    _ = _ := Category.assoc _ _ _

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The forward correspondence respects actual target transformations. -/
theorem leftKanHomToRestriction_postcomp
    (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (alpha : leftKanObject j X ⟶ Y) (s : Y ⟶ Y') :
    leftKanHomToRestriction j X Y' (alpha ≫ s) =
      leftKanHomToRestriction j X Y alpha ≫ (restriction j).map s := by
  unfold leftKanHomToRestriction
  calc
    _ = leftKanUnit j X ≫ ((restriction j).map alpha ≫ (restriction j).map s) :=
      congrArg (fun q => leftKanUnit j X ≫ q) ((restriction j).map_comp alpha s)
    _ = _ := (Category.assoc _ _ _).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The complete ordinary Hom correspondence between genuine enriched transformations. -/
@[no_expose]
def leftKanHomEquiv (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) :
    (leftKanObject j X ⟶ Y) ≃ (X ⟶ restrictionObject j Y) where
  toFun := leftKanHomToRestriction j X Y
  invFun := leftKanTransposeMap j X Y
  left_inv := leftKanTranspose_homToRestriction j X Y
  right_inv := leftKanHomToRestriction_transpose j X Y

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanHomEquiv_apply_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) :
    leftKanHomEquiv j X Y alpha = leftKanHomToRestriction j X Y alpha := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_apply
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (alpha : leftKanObject j X ⟶ Y) :
    leftKanHomEquiv j X Y alpha = leftKanHomToRestriction j X Y alpha :=
  leftKanHomEquiv_apply_private j X Y alpha

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanHomEquiv_symm_apply_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    (leftKanHomEquiv j X Y).symm f = leftKanTransposeMap j X Y f := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_symm_apply
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    (leftKanHomEquiv j X Y).symm f = leftKanTransposeMap j X Y f :=
  leftKanHomEquiv_symm_apply_private j X Y f

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_naturality_left
    {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (t : X' ⟶ X) (alpha : leftKanObject j X ⟶ Y) :
    leftKanHomEquiv j X' Y ((leftKan j).map t ≫ alpha) =
      t ≫ leftKanHomEquiv j X Y alpha := by
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply]
  exact leftKanHomToRestriction_precomp j Y t alpha

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_naturality_right
    (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (alpha : leftKanObject j X ⟶ Y) (s : Y ⟶ Y') :
    leftKanHomEquiv j X Y' (alpha ≫ s) =
      leftKanHomEquiv j X Y alpha ≫ (restriction j).map s := by
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply]
  exact leftKanHomToRestriction_postcomp j X alpha s

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_naturality_left_symm
    {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (t : X' ⟶ X) (f : X ⟶ restrictionObject j Y) :
    (leftKanHomEquiv j X' Y).symm (t ≫ f) =
      (leftKan j).map t ≫ (leftKanHomEquiv j X Y).symm f := by
  apply (leftKanHomEquiv j X' Y).injective
  rw [Equiv.apply_symm_apply, leftKanHomEquiv_naturality_left, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_naturality_right_symm
    (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (f : X ⟶ restrictionObject j Y) (s : Y ⟶ Y') :
    (leftKanHomEquiv j X Y').symm (f ≫ (restriction j).map s) =
      (leftKanHomEquiv j X Y).symm f ≫ s := by
  apply (leftKanHomEquiv j X Y').injective
  rw [Equiv.apply_symm_apply, leftKanHomEquiv_naturality_right, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The actual left Kan/restriction adjunction is constructed from its proved Hom correspondence. -/
@[no_expose]
def leftKanRestrictionAdjunction : leftKan j ⊣ restriction j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := leftKanHomEquiv j
      homEquiv_naturality_left_symm := fun t f =>
        leftKanHomEquiv_naturality_left_symm j _ t f
      homEquiv_naturality_right := fun alpha s =>
        leftKanHomEquiv_naturality_right j _ alpha s }

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictionAdjunction_homEquiv_private :
    (leftKanRestrictionAdjunction j).homEquiv = leftKanHomEquiv j :=
  Adjunction.mkOfHomEquiv_homEquiv _

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanRestrictionAdjunction_homEquiv :
    (leftKanRestrictionAdjunction j).homEquiv = leftKanHomEquiv j :=
  leftKanRestrictionAdjunction_homEquiv_private j

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictionAdjunction_unit_private (X : EnrichedFunctorCat V A) :
    (leftKanRestrictionAdjunction j).unit.app X = leftKanUnit j X := by
  have h := (leftKanRestrictionAdjunction j).homEquiv_unit
    (X := X) (Y := (leftKan j).obj X) (f := 𝟙 ((leftKan j).obj X))
  rw [leftKanRestrictionAdjunction_homEquiv, leftKanHomEquiv_apply] at h
  unfold leftKanHomToRestriction at h
  rw [(restriction j).map_id ((leftKan j).obj X)] at h
  let eta : X ⟶ restrictionObject j (leftKanObject j X) :=
    (leftKanRestrictionAdjunction j).unit.app X
  change leftKanUnit j X ≫ 𝟙 (restrictionObject j (leftKanObject j X)) =
    eta ≫ 𝟙 (restrictionObject j (leftKanObject j X)) at h
  simp only [Category.comp_id] at h
  exact h.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The real adjunction unit is exactly the original enriched identity insertion. -/
theorem leftKanRestrictionAdjunction_unit (X : EnrichedFunctorCat V A) :
    (leftKanRestrictionAdjunction j).unit.app X = leftKanUnit j X :=
  leftKanRestrictionAdjunction_unit_private j X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictionAdjunction_counit_private (Y : EnrichedFunctorCat V B) :
    (leftKanRestrictionAdjunction j).counit.app Y =
      leftKanTransposeMap j ((restriction j).obj Y) Y (𝟙 ((restriction j).obj Y)) := by
  have h := (leftKanRestrictionAdjunction j).homEquiv_counit
    (X := (restriction j).obj Y) (Y := Y) (g := 𝟙 ((restriction j).obj Y))
  rw [leftKanRestrictionAdjunction_homEquiv, leftKanHomEquiv_symm_apply] at h
  rw [(leftKan j).map_id ((restriction j).obj Y), Category.id_comp] at h
  exact h.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The real adjunction counit is the full original generator contraction. -/
theorem leftKanRestrictionAdjunction_counit (Y : EnrichedFunctorCat V B) :
    (leftKanRestrictionAdjunction j).counit.app Y =
      leftKanTransposeMap j ((restriction j).obj Y) Y (𝟙 ((restriction j).obj Y)) :=
  leftKanRestrictionAdjunction_counit_private j Y

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictionAdjunction_unit_component_private
    (X : EnrichedFunctorCat V A) (a : A) :
    component ((leftKanRestrictionAdjunction j).unit.app X) a =
      (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
        (eId V (j.obj a) ▷ X.toEnrichedFunctor.obj a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j (j.obj a)) X.toEnrichedFunctor a := by
  let eta : X ⟶ restrictionObject j (leftKanObject j X) :=
    (leftKanRestrictionAdjunction j).unit.app X
  have hEta : eta = leftKanUnit j X := leftKanRestrictionAdjunction_unit j X
  change component eta a = _
  rw [hEta, leftKanUnit_component]
  rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanRestrictionAdjunction_unit_component
    (X : EnrichedFunctorCat V A) (a : A) :
    component ((leftKanRestrictionAdjunction j).unit.app X) a =
      (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
        (eId V (j.obj a) ▷ X.toEnrichedFunctor.obj a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j (j.obj a)) X.toEnrichedFunctor a :=
  leftKanRestrictionAdjunction_unit_component_private j X a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanRestrictionAdjunction_counit_ι_private
    (Y : EnrichedFunctorCat V B) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) ((restriction j).obj Y).toEnrichedFunctor a ≫
        component ((leftKanRestrictionAdjunction j).counit.app Y) b =
      (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) := by
  let epsilon : leftKanObject j ((restriction j).obj Y) ⟶ Y :=
    (leftKanRestrictionAdjunction j).counit.app Y
  have hEpsilon : epsilon =
      leftKanTransposeMap j ((restriction j).obj Y) Y (𝟙 ((restriction j).obj Y)) :=
    leftKanRestrictionAdjunction_counit j Y
  change Enriched.weightedCoend.ι
    (leftKanWeight j b) ((restriction j).obj Y).toEnrichedFunctor a ≫
      component epsilon b = _
  rw [hEpsilon, leftKanTransposeMap_component,
    leftKanTransposeMapComponent_ι, leftKanTransposeCocone_eq, component_id]
  simp only [id_tensorHom_id, Category.id_comp]
  rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanRestrictionAdjunction_counit_ι
    (Y : EnrichedFunctorCat V B) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) ((restriction j).obj Y).toEnrichedFunctor a ≫
        component ((leftKanRestrictionAdjunction j).counit.app Y) b =
      (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
  leftKanRestrictionAdjunction_counit_ι_private j Y b a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanRestrictionAdjunction_left_triangle (X : EnrichedFunctorCat V A) :
    (leftKan j).map ((leftKanRestrictionAdjunction j).unit.app X) ≫
        (leftKanRestrictionAdjunction j).counit.app ((leftKan j).obj X) =
      𝟙 ((leftKan j).obj X) :=
  (leftKanRestrictionAdjunction j).left_triangle_components X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanRestrictionAdjunction_right_triangle (Y : EnrichedFunctorCat V B) :
    (leftKanRestrictionAdjunction j).unit.app ((restriction j).obj Y) ≫
        (restriction j).map ((leftKanRestrictionAdjunction j).counit.app Y) =
      𝟙 ((restriction j).obj Y) :=
  (leftKanRestrictionAdjunction j).right_triangle_components Y

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Full transformations with the required restricted-unit property are unique. -/
theorem leftKanTransposeMap_unique
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (gamma : leftKanObject j X ⟶ Y)
    (h : leftKanHomToRestriction j X Y gamma = f) :
    gamma = leftKanTransposeMap j X Y f := by
  calc
    gamma = leftKanTransposeMap j X Y (leftKanHomToRestriction j X Y gamma) :=
      (leftKanTranspose_homToRestriction j X Y gamma).symm
    _ = _ := congrArg (leftKanTransposeMap j X Y) h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanTransposeMap_unique_of_unit_components
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (gamma : leftKanObject j X ⟶ Y)
    (h : ∀ a, leftKanUnitComponent j X a ≫ component gamma (j.obj a) = component f a) :
    gamma = leftKanTransposeMap j X Y f := by
  apply leftKanTransposeMap_unique j X Y f gamma
  apply hom_ext
  intro a
  rw [leftKanHomToRestriction_component]
  exact h a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanTransposeMap_unique_of_generators
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (gamma : leftKanObject j X ⟶ Y)
    (h : ∀ b a, Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a ≫
      component gamma b = leftKanTransposeCocone j X Y f b a) :
    gamma = leftKanTransposeMap j X Y f := by
  apply hom_ext
  intro b
  apply Enriched.weightedCoend.hom_ext (leftKanWeight j b) X.toEnrichedFunctor
  intro a
  rw [leftKanTransposeMap_component, leftKanTransposeMapComponent_ι]
  exact h b a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanHomEquiv_symm_ι
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a ≫
        component ((leftKanHomEquiv j X Y).symm f) b =
      (𝟙 (j.obj a ⟶[V] b) ⊗ₘ component f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) := by
  rw [leftKanHomEquiv_symm_apply, leftKanTransposeMap_component,
    leftKanTransposeMapComponent_ι, leftKanTransposeCocone_eq]

end LeftKanUniversal


section GradedKanUniversal
variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- All central grades use the original Lan coends and the actual grade half-braids. -/
@[no_expose]
def leftKanGradedHomEquiv
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) :
    GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor ≃
      GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor :=
  (gradedCotensorEquiv Γ (leftKanObject j X) Y).trans
    ((leftKanHomEquiv j X (cotensorObject Γ.1 Y)).trans
      ((Iso.homCongr (Iso.refl X) (cotensorRestrictionIso j Γ.1 Y).symm).trans
        (gradedCotensorEquiv Γ X (restrictionObject j Y)).symm))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanGradedHomEquiv_left_inverse
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    (leftKanGradedHomEquiv j Γ X Y).symm (leftKanGradedHomEquiv j Γ X Y t) = t :=
  (leftKanGradedHomEquiv j Γ X Y).symm_apply_apply t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanGradedHomEquiv_right_inverse
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y ((leftKanGradedHomEquiv j Γ X Y).symm t) = t :=
  (leftKanGradedHomEquiv j Γ X Y).apply_symm_apply t

end GradedKanUniversal


/-! Full-grade component laws, central regrading, and the actual mapping presheaf. -/

section GradedKanCharacteristics
variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_factor
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y t =
      cotensorToGraded Γ X (restrictionObject j Y)
        (leftKanHomEquiv j X (cotensorObject Γ.1 Y)
          (gradedToCotensor Γ (leftKanObject j X) Y t) ≫
            (cotensorRestrictionIso j Γ.1 Y).inv) := by
  have h0 : leftKanGradedHomEquiv j Γ X Y t =
      (gradedCotensorEquiv Γ X (restrictionObject j Y)).symm
        (Iso.homCongr (Iso.refl X) (cotensorRestrictionIso j Γ.1 Y).symm
          (leftKanHomEquiv j X (cotensorObject Γ.1 Y)
            (gradedCotensorEquiv Γ (leftKanObject j X) Y t))) := rfl
  rw [gradedCotensorEquiv_symm_apply, gradedCotensorEquiv_apply, Iso.homCongr_apply] at h0
  change leftKanGradedHomEquiv j Γ X Y t =
    cotensorToGraded Γ X (restrictionObject j Y)
      (𝟙 X ≫ leftKanHomEquiv j X (cotensorObject Γ.1 Y)
        (gradedToCotensor Γ (leftKanObject j X) Y t) ≫
          (cotensorRestrictionIso j Γ.1 Y).inv) at h0
  exact h0.trans (congrArg (cotensorToGraded Γ X (restrictionObject j Y)) (Category.id_comp _))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_gradeFirstComponent_private
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (leftKanGradedHomEquiv j Γ X Y t) a =
      (Γ.1 ◁ leftKanUnitComponent j X a) ≫
        GradedNatTrans.gradeFirstComponent Γ t (j.obj a) := by
  rw [leftKanGradedHomEquiv_factor, cotensorToGraded_gradeFirst]
  let T := gradedToCotensor Γ (leftKanObject j X) Y t
  let H := leftKanHomEquiv j X (cotensorObject Γ.1 Y) T
  have hH : component H a = leftKanUnitComponent j X a ≫
      MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t (j.obj a)) := by
    dsimp only [H, T]
    rw [leftKanHomEquiv_apply, leftKanHomToRestriction_component,
      gradedToCotensor_component]
    rfl
  have hI := cotensorRestrictionIso_inv_component j Γ.1 Y a
  have hC : component (H ≫ (cotensorRestrictionIso j Γ.1 Y).inv) a =
      leftKanUnitComponent j X a ≫
        MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t (j.obj a)) :=
    ((component_comp H ((cotensorRestrictionIso j Γ.1 Y).inv) a).trans
      (congrArg₂ (fun f g => f ≫ g) hH hI)).trans (Category.comp_id _)
  change MonoidalClosed.uncurry
    (component (H ≫ (cotensorRestrictionIso j Γ.1 Y).inv) a) = _
  exact (congrArg MonoidalClosed.uncurry hC).trans
    ((MonoidalClosed.uncurry_natural_left (leftKanUnitComponent j X a)
      (MonoidalClosed.curry (GradedNatTrans.gradeFirstComponent Γ t (j.obj a)))).trans
        (congrArg (fun q => (Γ.1 ◁ leftKanUnitComponent j X a) ≫ q)
          (MonoidalClosed.uncurry_curry (GradedNatTrans.gradeFirstComponent Γ t (j.obj a)))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The all-grade forward map precomposes its left coefficient components by the actual unit. -/
theorem leftKanGradedHomEquiv_gradeFirstComponent
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (leftKanGradedHomEquiv j Γ X Y t) a =
      (Γ.1 ◁ leftKanUnitComponent j X a) ≫
        GradedNatTrans.gradeFirstComponent Γ t (j.obj a) :=
  leftKanGradedHomEquiv_gradeFirstComponent_private j Γ X Y t a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_app_private
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (a : A) :
    (leftKanGradedHomEquiv j Γ X Y t).app a =
      t.app (j.obj a) ≫
        (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
          (Y.toEnrichedFunctor.obj (j.obj a)) := by
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (Γ.2.β (X.toEnrichedFunctor.obj a)).hom).1
  change GradedNatTrans.gradeFirstComponent Γ (leftKanGradedHomEquiv j Γ X Y t) a = _
  exact (leftKanGradedHomEquiv_gradeFirstComponent j Γ X Y t a).trans
    ((HalfBraiding.naturality_assoc Γ.2 (leftKanUnitComponent j X a)
      (MonoidalClosed.uncurry (t.app (j.obj a)))).trans
        (congrArg (fun q => (Γ.2.β (X.toEnrichedFunctor.obj a)).hom ≫ q)
          (MonoidalClosed.uncurry_pre_app (C := V)
            (X := Y.toEnrichedFunctor.obj (j.obj a)) (t.app (j.obj a))
            (leftKanUnitComponent j X a)).symm))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Every raw graded component is precomposition by the original Lan unit. -/
theorem leftKanGradedHomEquiv_app
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (a : A) :
    (leftKanGradedHomEquiv j Γ X Y t).app a =
      t.app (j.obj a) ≫
        (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
          (Y.toEnrichedFunctor.obj (j.obj a)) :=
  leftKanGradedHomEquiv_app_private j Γ X Y t a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Forward correspondence commutes with every genuine morphism in the center. -/
theorem leftKanGradedHomEquiv_regrade
    {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ' (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y (GradedNatTrans.regrade u t) =
      GradedNatTrans.regrade u (leftKanGradedHomEquiv j Γ' X Y t) := by
  apply GradedNatTrans.ext
  funext a
  rw [leftKanGradedHomEquiv_app, GradedNatTrans.regrade_app,
    GradedNatTrans.regrade_app, leftKanGradedHomEquiv_app]
  exact Category.assoc _ _ _

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Inverse correspondence commutes with the same actual central scalar maps. -/
theorem leftKanGradedHomEquiv_symm_regrade
    {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ' X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    (leftKanGradedHomEquiv j Γ X Y).symm (GradedNatTrans.regrade u t) =
      GradedNatTrans.regrade u ((leftKanGradedHomEquiv j Γ' X Y).symm t) := by
  apply (leftKanGradedHomEquiv j Γ X Y).injective
  rw [Equiv.apply_symm_apply, leftKanGradedHomEquiv_regrade, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Naturality is for the actual pinned mapping presheaf and its ambient central grades. -/
theorem leftKanGradedHomEquiv_presheaf_naturality
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    {M N : Vᵒᵖ} (h : M ⟶ N)
    (t : (enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor).obj M) :
    leftKanGradedHomEquiv j ((Center.ofBraided V).obj N.unop) X Y
        ((enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor
          Y.toEnrichedFunctor).map h t) =
      (enrichedNatTransYoneda X.toEnrichedFunctor
        (restrictionObject j Y).toEnrichedFunctor).map h
          (leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y t) := by
  apply GradedNatTrans.ext
  funext a
  exact (leftKanGradedHomEquiv_app j ((Center.ofBraided V).obj N.unop) X Y
    ((enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor
      Y.toEnrichedFunctor).map h t) a).trans
      ((Category.assoc h.unop (t.app (j.obj a))
        ((MonoidalClosed.pre (leftKanUnitComponent j X a)).app
          (Y.toEnrichedFunctor.obj (j.obj a)))).trans
            (congrArg (fun q => h.unop ≫ q)
              (leftKanGradedHomEquiv_app j ((Center.ofBraided V).obj M.unop) X Y t a).symm))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The actual enriched mapping presheaves agree after explicit lifts to a common universe. -/
@[no_expose]
def leftKanEnrichedNatTransYonedaIso
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) :
    (enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) ⋙
        uliftFunctor.{max uA uB vV, max uB vV} ≅
      (enrichedNatTransYoneda X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) ⋙
        uliftFunctor.{max uA uB vV, max uA vV} :=
  NatIso.ofComponents
    (fun M => (Equiv.ulift.trans
      ((leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y).trans
        Equiv.ulift.symm)).toIso)
    (by
      intro M N h
      apply ConcreteCategory.ext_apply
      intro t
      apply ULift.ext
      exact leftKanGradedHomEquiv_presheaf_naturality j X Y h t.down)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanEnrichedNatTransYonedaIso_hom_app_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) (M : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor).obj M)) :
    (leftKanEnrichedNatTransYonedaIso j X Y).hom.app M t =
      ULift.up (leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y t.down) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanEnrichedNatTransYonedaIso_hom_app
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) (M : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor).obj M)) :
    (leftKanEnrichedNatTransYonedaIso j X Y).hom.app M t =
      ULift.up (leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y t.down) :=
  leftKanEnrichedNatTransYonedaIso_hom_app_private j X Y M t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanEnrichedNatTransYonedaIso_inv_app_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) (M : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda X.toEnrichedFunctor
        (restrictionObject j Y).toEnrichedFunctor).obj M)) :
    (leftKanEnrichedNatTransYonedaIso j X Y).inv.app M t =
      ULift.up ((leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y).symm t.down) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanEnrichedNatTransYonedaIso_inv_app
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) (M : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda X.toEnrichedFunctor
        (restrictionObject j Y).toEnrichedFunctor).obj M)) :
    (leftKanEnrichedNatTransYonedaIso j X Y).inv.app M t =
      ULift.up ((leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y).symm t.down) :=
  leftKanEnrichedNatTransYonedaIso_inv_app_private j X Y M t

end GradedKanCharacteristics


/-! The all-grade inverse on the original coend generators. -/

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Evaluation moves past the weight using the inverse ambient braid. -/
@[reassoc]
private theorem leftKanCotensorEvaluation_weightSwap (M W Y : V) :
    (M ◁ (β_ W ((ihom M).obj Y)).hom) ≫
        (α_ M ((ihom M).obj Y) W).inv ≫ ((ihom.ev M).app Y ▷ W) =
      (α_ M W ((ihom M).obj Y)).inv ≫
        ((β_ W M).inv ▷ (ihom M).obj Y) ≫
        (α_ W M ((ihom M).obj Y)).hom ≫
        (W ◁ (ihom.ev M).app Y) ≫ (β_ W Y).hom := by
  let Q := (ihom M).obj Y
  let P : M ⊗ (W ⊗ Q) ⟶ W ⊗ (M ⊗ Q) :=
    (α_ M W Q).inv ≫ ((β_ W M).inv ▷ Q) ≫ (α_ W M Q).hom
  have hn : (W ◁ (ihom.ev M).app Y) ≫ (β_ W Y).hom =
      (β_ W (M ⊗ Q)).hom ≫ ((ihom.ev M).app Y ▷ W) :=
    braiding_naturality_right W ((ihom.ev M).app Y)
  have hx : P ≫ (β_ W (M ⊗ Q)).hom =
      (M ◁ (β_ W Q).hom) ≫ (α_ M Q W).inv := by
    dsimp only [P]
    rw [braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
  have hxp : P ≫ (β_ W (M ⊗ Q)).hom ≫ ((ihom.ev M).app Y ▷ W) =
      (M ◁ (β_ W Q).hom) ≫ (α_ M Q W).inv ≫ ((ihom.ev M).app Y ▷ W) := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ ((ihom.ev M).app Y ▷ W)) hx
  have hr := (congrArg (fun q => P ≫ q) hn).trans hxp
  simpa only [P, Q, Category.assoc] using hr.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
@[reassoc]
private theorem leftKanCotensorEvaluation_curry_weightSwap
    (M W X Y : V) (f : M ⊗ X ⟶ Y) :
    (M ◁ ((W ◁ MonoidalClosed.curry f) ≫ (β_ W ((ihom M).obj Y)).hom)) ≫
        (α_ M ((ihom M).obj Y) W).inv ≫ ((ihom.ev M).app Y ▷ W) =
      (α_ M W X).inv ≫ ((β_ W M).inv ▷ X) ≫ (α_ W M X).hom ≫
        (W ◁ f) ≫ (β_ W Y).hom := by
  rw [whiskerLeft_comp, Category.assoc, leftKanCotensorEvaluation_weightSwap]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]

section GradedKanGenerators
variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_symm_factor
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    (leftKanGradedHomEquiv j Γ X Y).symm f =
      cotensorToGraded Γ (leftKanObject j X) Y
        ((leftKanHomEquiv j X (cotensorObject Γ.1 Y)).symm
          (gradedToCotensor Γ X (restrictionObject j Y) f ≫
            (cotensorRestrictionIso j Γ.1 Y).hom)) := by
  have h0 : (leftKanGradedHomEquiv j Γ X Y).symm f =
      (gradedCotensorEquiv Γ (leftKanObject j X) Y).symm
        ((leftKanHomEquiv j X (cotensorObject Γ.1 Y)).symm
          ((Iso.homCongr (Iso.refl X) (cotensorRestrictionIso j Γ.1 Y).symm).symm
            (gradedCotensorEquiv Γ X (restrictionObject j Y) f))) := rfl
  rw [gradedCotensorEquiv_symm_apply, gradedCotensorEquiv_apply,
    Iso.homCongr_symm, Iso.homCongr_apply] at h0
  change (leftKanGradedHomEquiv j Γ X Y).symm f =
    cotensorToGraded Γ (leftKanObject j X) Y
      ((leftKanHomEquiv j X (cotensorObject Γ.1 Y)).symm
        (𝟙 X ≫ gradedToCotensor Γ X (restrictionObject j Y) f ≫
          (cotensorRestrictionIso j Γ.1 Y).hom)) at h0
  exact h0.trans (congrArg
    (fun p => cotensorToGraded Γ (leftKanObject j X) Y
      ((leftKanHomEquiv j X (cotensorObject Γ.1 Y)).symm p)) (Category.id_comp _))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_symm_gradeFirstComponent_ι_private
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (b : B) (a : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        GradedNatTrans.gradeFirstComponent Γ ((leftKanGradedHomEquiv j Γ X Y).symm f) b =
      (α_ Γ.1 (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫
        ((j.obj a ⟶[V] b) ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) := by
  let M : V := Γ.1
  let W : V := j.obj a ⟶[V] b
  let Xa : V := X.toEnrichedFunctor.obj a
  let Ya : V := Y.toEnrichedFunctor.obj (j.obj a)
  let q : M ⊗ Xa ⟶ Ya := GradedNatTrans.gradeFirstComponent Γ f a
  let i : W ⊗ Xa ⟶ (leftKanObject j X).toEnrichedFunctor.obj b :=
    Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a
  let T := gradedToCotensor Γ X (restrictionObject j Y) f
  let P : X ⟶ restrictionObject j (cotensorObject M Y) :=
    T ≫ (cotensorRestrictionIso j M Y).hom
  let H := (leftKanHomEquiv j X (cotensorObject M Y)).symm P
  have hT : component T a = MonoidalClosed.curry q :=
    gradedToCotensor_component Γ X (restrictionObject j Y) f a
  have hP : component P a = MonoidalClosed.curry q :=
    ((component_comp T ((cotensorRestrictionIso j M Y).hom) a).trans
      (congrArg₂ (fun u v => u ≫ v) hT
        (cotensorRestrictionIso_hom_component j M Y a))).trans (Category.comp_id _)
  have hi0 := leftKanHomEquiv_symm_ι j X (cotensorObject M Y) P b a
  have hi : i ≫ component H b =
      ((W ◁ MonoidalClosed.curry q) ≫ (β_ W ((ihom M).obj Ya)).hom) ≫
        MonoidalClosed.uncurry
          ((EnrichedFunctor.cotensor M Y.toEnrichedFunctor).map (j.obj a) b) := by
    have hc := congrArg (fun p => (𝟙 W ⊗ₘ p) ≫
      (β_ W ((ihom M).obj Ya)).hom ≫
        MonoidalClosed.uncurry
          ((EnrichedFunctor.cotensor M Y.toEnrichedFunctor).map (j.obj a) b)) hP
    calc
      i ≫ component H b = (𝟙 W ⊗ₘ MonoidalClosed.curry q) ≫
          (β_ W ((ihom M).obj Ya)).hom ≫
            MonoidalClosed.uncurry
              ((EnrichedFunctor.cotensor M Y.toEnrichedFunctor).map (j.obj a) b) := hi0.trans hc
      _ = ((W ◁ MonoidalClosed.curry q) ≫ (β_ W ((ihom M).obj Ya)).hom) ≫
          MonoidalClosed.uncurry
            ((EnrichedFunctor.cotensor M Y.toEnrichedFunctor).map (j.obj a) b) := by
        rw [id_tensorHom]
        exact (Category.assoc _ _ _).symm
  have hInv : GradedNatTrans.gradeFirstComponent Γ
      ((leftKanGradedHomEquiv j Γ X Y).symm f) b = MonoidalClosed.uncurry (component H b) :=
    (congrArg (fun t => GradedNatTrans.gradeFirstComponent Γ t b)
      (leftKanGradedHomEquiv_symm_factor j Γ X Y f)).trans
        (cotensorToGraded_gradeFirst Γ (leftKanObject j X) Y H b)
  change (M ◁ i) ≫ GradedNatTrans.gradeFirstComponent Γ
    ((leftKanGradedHomEquiv j Γ X Y).symm f) b = _
  calc
    _ = (M ◁ i) ≫ MonoidalClosed.uncurry (component H b) :=
      congrArg (fun p => (M ◁ i) ≫ p) hInv
    _ = MonoidalClosed.uncurry (i ≫ component H b) :=
      (MonoidalClosed.uncurry_natural_left i (component H b)).symm
    _ = MonoidalClosed.uncurry
        (((W ◁ MonoidalClosed.curry q) ≫ (β_ W ((ihom M).obj Ya)).hom) ≫
          MonoidalClosed.uncurry
            ((EnrichedFunctor.cotensor M Y.toEnrichedFunctor).map (j.obj a) b)) :=
      congrArg MonoidalClosed.uncurry hi
    _ = (α_ M W Xa).inv ≫ ((β_ W M).inv ▷ Xa) ≫ (α_ W M Xa).hom ≫
        (W ◁ q) ≫ (β_ W Ya).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) := by
      rw [MonoidalClosed.uncurry_natural_left, EnrichedFunctor.cotensor_doubleUncurry]
      rw [leftKanCotensorEvaluation_curry_weightSwap_assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- Original coend generators give the full graded inverse with the inverse ambient weight braid. -/
theorem leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (b : B) (a : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        GradedNatTrans.gradeFirstComponent Γ ((leftKanGradedHomEquiv j Γ X Y).symm f) b =
      (α_ Γ.1 (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫
        ((j.obj a ⟶[V] b) ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
  leftKanGradedHomEquiv_symm_gradeFirstComponent_ι_private j Γ X Y f b a

end GradedKanGenerators


/-! Recovery of the genuine unit-grade adjunction and all-grade uniqueness. -/

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
omit [BraidedCategory V] in
private theorem leftKanUnitGraded_pre_component
    {P Q R : V} (p : P ⟶ Q) (g : 𝟙_ V ⟶ (ihom Q).obj R) :
    (eHomEquiv V).symm (g ≫ (MonoidalClosed.pre p).app R) =
      p ≫ (eHomEquiv V).symm g := by
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm,
    MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  simp only [MonoidalClosed.uncurry', MonoidalClosed.uncurry_pre_app]
  rw [rightUnitor_inv_naturality_assoc]

section GradedKanUnit
variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
private theorem leftKanGradedHomEquiv_unit_apply_private
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : leftKanObject j X ⟶ Y) :
    leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y t =
      leftKanHomEquiv j X Y t := by
  apply hom_ext
  intro a
  have hG : component
      (leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y t) a =
        leftKanUnitComponent j X a ≫ component t (j.obj a) :=
    (congrArg (eHomEquiv V).symm
      (leftKanGradedHomEquiv_app j ((Center.ofBraided V).obj (𝟙_ V)) X Y t a)).trans
        (leftKanUnitGraded_pre_component (leftKanUnitComponent j X a) (t.app (j.obj a)))
  have hU : component (leftKanHomEquiv j X Y t) a =
      leftKanUnitComponent j X a ≫ component t (j.obj a) :=
    (congrArg (fun f => component f a) (leftKanHomEquiv_apply j X Y t)).trans
      (leftKanHomToRestriction_component j X Y t a)
  exact hG.trans hU.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The canonical tensor-unit grade recovers the exact original Lan Hom correspondence. -/
theorem leftKanGradedHomEquiv_unit_apply
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : leftKanObject j X ⟶ Y) :
    leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y t =
      leftKanHomEquiv j X Y t :=
  leftKanGradedHomEquiv_unit_apply_private j X Y t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanGradedHomEquiv_unit
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) :
    leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y =
      leftKanHomEquiv j X Y :=
  Equiv.ext (leftKanGradedHomEquiv_unit_apply j X Y)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
theorem leftKanGradedHomEquiv_unit_symm_apply
    (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    (leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y).symm f =
      (leftKanHomEquiv j X Y).symm f :=
  congrArg (fun e : (leftKanObject j X ⟶ Y) ≃ (X ⟶ restrictionObject j Y) => e.symm f)
    (leftKanGradedHomEquiv_unit j X Y)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- All-grade transformations out of Lan are detected by the original coend generators. -/
theorem leftKanGradedGenerator_ext
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t t' : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (h : ∀ b a,
      (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
          GradedNatTrans.gradeFirstComponent Γ t b =
        (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
          GradedNatTrans.gradeFirstComponent Γ t' b) : t = t' := by
  apply GradedNatTrans.gradeFirstComponent_ext Γ
  intro b
  apply MonoidalClosed.curry_injective
  apply Enriched.weightedCoend.hom_ext (leftKanWeight j b) X.toEnrichedFunctor
  intro a
  exact (MonoidalClosed.curry_natural_left
      (Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a)
        (GradedNatTrans.gradeFirstComponent Γ t b)).symm.trans
    ((congrArg MonoidalClosed.curry (h b a)).trans
      (MonoidalClosed.curry_natural_left
        (Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a)
          (GradedNatTrans.gradeFirstComponent Γ t' b)))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The full graded universal solution is uniquely determined by its original-unit restriction. -/
theorem leftKanGradedHomEquiv_symm_unique
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (h : ∀ a,
      (Γ.1 ◁ leftKanUnitComponent j X a) ≫
          GradedNatTrans.gradeFirstComponent Γ t (j.obj a) =
        GradedNatTrans.gradeFirstComponent Γ f a) :
    t = (leftKanGradedHomEquiv j Γ X Y).symm f := by
  apply (leftKanGradedHomEquiv j Γ X Y).injective
  rw [Equiv.apply_symm_apply]
  apply GradedNatTrans.gradeFirstComponent_ext Γ
  intro a
  exact (leftKanGradedHomEquiv_gradeFirstComponent j Γ X Y t a).trans (h a)

end GradedKanUnit


/-! The four genuine input naturalities in every central grade. -/

section GradedKanInput
variable (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The graded correspondence respects the actual left Kan functor on its source input. -/
theorem leftKanGradedHomEquiv_naturality_left
    (Γ : Center V) {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (p : X' ⟶ X)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X' Y (gradedPrecomp Γ ((leftKan j).map p) t) =
      gradedPrecomp Γ p (leftKanGradedHomEquiv j Γ X Y t) := by
  apply GradedNatTrans.ext
  funext a
  have hη : component p a ≫ leftKanUnitComponent j X a =
      leftKanUnitComponent j X' a ≫ component ((leftKan j).map p) (j.obj a) := by
    have h := congrArg (fun f => component f a) (leftKanUnit_natural j p)
    rw [component_comp, component_comp, leftKanUnit_component,
      leftKanUnit_component, restrictionMap_component] at h
    exact h
  have hpre :
      (MonoidalClosed.pre (component ((leftKan j).map p) (j.obj a))).app
          (Y.toEnrichedFunctor.obj (j.obj a)) ≫
        (MonoidalClosed.pre (leftKanUnitComponent j X' a)).app
          (Y.toEnrichedFunctor.obj (j.obj a)) =
      (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
          (Y.toEnrichedFunctor.obj (j.obj a)) ≫
        (MonoidalClosed.pre (component p a)).app (Y.toEnrichedFunctor.obj (j.obj a)) := by
    exact (congrArg (fun f => f.app (Y.toEnrichedFunctor.obj (j.obj a)))
      (MonoidalClosed.pre_map (leftKanUnitComponent j X' a)
        (component ((leftKan j).map p) (j.obj a)))).symm.trans
          ((congrArg (fun f => (MonoidalClosed.pre f).app
            (Y.toEnrichedFunctor.obj (j.obj a))) hη).symm.trans
              (congrArg (fun f => f.app (Y.toEnrichedFunctor.obj (j.obj a)))
                (MonoidalClosed.pre_map (component p a) (leftKanUnitComponent j X a))))
  rw [leftKanGradedHomEquiv_app, gradedPrecomp_app, gradedPrecomp_app,
    leftKanGradedHomEquiv_app]
  change (t.app (j.obj a) ≫
      (MonoidalClosed.pre (component ((leftKan j).map p) (j.obj a))).app
        (Y.toEnrichedFunctor.obj (j.obj a))) ≫
      (MonoidalClosed.pre (leftKanUnitComponent j X' a)).app
        (Y.toEnrichedFunctor.obj (j.obj a)) =
    (t.app (j.obj a) ≫ (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
      (Y.toEnrichedFunctor.obj (j.obj a))) ≫
        (MonoidalClosed.pre (component p a)).app (Y.toEnrichedFunctor.obj (j.obj a))
  exact (Category.assoc (t.app (j.obj a))
    ((MonoidalClosed.pre (component ((leftKan j).map p) (j.obj a))).app
      (Y.toEnrichedFunctor.obj (j.obj a)))
    ((MonoidalClosed.pre (leftKanUnitComponent j X' a)).app
      (Y.toEnrichedFunctor.obj (j.obj a)))).trans
        ((congrArg (fun f => t.app (j.obj a) ≫ f) hpre).trans
          (Category.assoc (t.app (j.obj a))
            ((MonoidalClosed.pre (leftKanUnitComponent j X a)).app
              (Y.toEnrichedFunctor.obj (j.obj a)))
            ((MonoidalClosed.pre (component p a)).app
              (Y.toEnrichedFunctor.obj (j.obj a)))).symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The graded correspondence respects the actual target morphism and original restriction. -/
theorem leftKanGradedHomEquiv_naturality_right
    (Γ : Center V) (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (q : Y ⟶ Y') :
    leftKanGradedHomEquiv j Γ X Y' (gradedPostcomp Γ t q) =
      gradedPostcomp Γ (leftKanGradedHomEquiv j Γ X Y t) ((restriction j).map q) := by
  apply GradedNatTrans.ext
  funext a
  rw [leftKanGradedHomEquiv_app, gradedPostcomp_app, gradedPostcomp_app,
    leftKanGradedHomEquiv_app, restrictionMap_component]
  change (t.app (j.obj a) ≫
      (ihom (leftKanCoendObject j X.toEnrichedFunctor (j.obj a))).map
        (component q (j.obj a))) ≫
      (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
        (Y'.toEnrichedFunctor.obj (j.obj a)) =
    (t.app (j.obj a) ≫ (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
      (Y.toEnrichedFunctor.obj (j.obj a))) ≫
        (ihom (X.toEnrichedFunctor.obj a)).map (component q (j.obj a))
  exact (Category.assoc (t.app (j.obj a))
    ((ihom (leftKanCoendObject j X.toEnrichedFunctor (j.obj a))).map (component q (j.obj a)))
    ((MonoidalClosed.pre (leftKanUnitComponent j X a)).app
      (Y'.toEnrichedFunctor.obj (j.obj a)))).trans
        ((congrArg (fun f => t.app (j.obj a) ≫ f)
          ((MonoidalClosed.pre (leftKanUnitComponent j X a)).naturality
            (component q (j.obj a)))).trans
              (Category.assoc (t.app (j.obj a))
                ((MonoidalClosed.pre (leftKanUnitComponent j X a)).app
                  (Y.toEnrichedFunctor.obj (j.obj a)))
                ((ihom (X.toEnrichedFunctor.obj a)).map (component q (j.obj a)))).symm)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The inverse respects the same genuine source input map in the same central grade. -/
theorem leftKanGradedHomEquiv_naturality_left_symm
    (Γ : Center V) {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (p : X' ⟶ X)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    (leftKanGradedHomEquiv j Γ X' Y).symm (gradedPrecomp Γ p f) =
      gradedPrecomp Γ ((leftKan j).map p) ((leftKanGradedHomEquiv j Γ X Y).symm f) := by
  apply (leftKanGradedHomEquiv j Γ X' Y).injective
  rw [Equiv.apply_symm_apply, leftKanGradedHomEquiv_naturality_left, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the complete enriched coend or Hom calculation.
/-- The inverse respects the same actual target input map after literal restriction. -/
theorem leftKanGradedHomEquiv_naturality_right_symm
    (Γ : Center V) (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (q : Y ⟶ Y') :
    (leftKanGradedHomEquiv j Γ X Y').symm (gradedPostcomp Γ f ((restriction j).map q)) =
      gradedPostcomp Γ ((leftKanGradedHomEquiv j Γ X Y).symm f) q := by
  apply (leftKanGradedHomEquiv j Γ X Y').injective
  rw [Equiv.apply_symm_apply, leftKanGradedHomEquiv_naturality_right, Equiv.apply_symm_apply]

end GradedKanInput


end CategoryTheory.EnrichedFunctorCat
