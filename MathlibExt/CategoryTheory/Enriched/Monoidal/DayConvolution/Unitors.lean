/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Kernel
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor

/-!
# Genuine enriched Day unitors

The representable index unit gives actual left and right unitors on the
category of genuine enriched functors. Their full hom-object strengths prove
balance of the original kernels, and actual kernel relations prove both
component inverse laws. Output and input naturality use only the selected
source and target presentations. The enriched-functor isomorphisms and
fixed-unit endofunctor natural isomorphisms retain these component maps and
need only their respective unit-input families of presentations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uI vI

namespace CategoryTheory.EnrichedDayKernel.Unitors

open MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

section ActionLaws

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uI} [EnrichedCategory V C]

open scoped MonoidalClosed

/-- The entire enriched action respects source-first composition. -/
private theorem action_comp (F : EnrichedFunctor V C V) (i j k : C) :
    F.obj i ◁ eComp V i j k ≫ MonoidalClosed.uncurry (F.map i k) =
      (α_ (F.obj i) (i ⟶[V] j) (j ⟶[V] k)).inv ≫
        (MonoidalClosed.uncurry (F.map i j) ▷ (j ⟶[V] k)) ≫
        MonoidalClosed.uncurry (F.map j k) := by
  have h := congrArg (MonoidalClosed.uncurry (A := F.obj i)) (F.map_comp i j k)
  rw [MonoidalClosed.uncurry_eComp] at h
  simpa only [MonoidalClosed.uncurry_natural_left] using h

/-- The full action of the actual enriched identity is the selected right unitor. -/
private theorem action_id (F : EnrichedFunctor V C V) (i : C) :
    (ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V i) ≫
      MonoidalClosed.uncurry (F.map i i) = 𝟙 (F.obj i) := by
  have h := congrArg (MonoidalClosed.uncurry (A := F.obj i)) (F.map_id i)
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  simpa only [id_tensorHom, Category.assoc, Iso.inv_hom_id] using
    congrArg (fun v => (ρ_ (F.obj i)).inv ≫ v) h

end ActionLaws

section Data

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

omit [Category I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I] in
/-- Interchange with two actual unit insertions retains the entire middle braid. -/
private theorem tensorMu_unit_exchange {A B X Y : V}
    (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) :
    (((λ_ X).inv ≫ (f ⊗ₘ 𝟙 X)) ⊗ₘ
        ((ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ g))) ≫ tensorμ A X Y B =
      (β_ X Y).hom ≫
        (((λ_ Y).inv ≫ (f ⊗ₘ 𝟙 Y)) ⊗ₘ
          ((ρ_ X).inv ≫ (𝟙 X ⊗ₘ g))) := by
  have hUnit :
      ((λ_ X).inv ⊗ₘ (ρ_ Y).inv) ≫ tensorμ (𝟙_ V) X Y (𝟙_ V) =
        (β_ X Y).hom ≫ ((λ_ Y).inv ⊗ₘ (ρ_ X).inv) := by
    dsimp only [tensorμ]
    monoidal
  calc
    _ = ((λ_ X).inv ⊗ₘ (ρ_ Y).inv) ≫
        ((f ⊗ₘ 𝟙 X) ⊗ₘ (𝟙 Y ⊗ₘ g)) ≫ tensorμ A X Y B := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ tensorμ A X Y B)
          (tensorHom_comp_tensorHom (λ_ X).inv (ρ_ Y).inv
            (f ⊗ₘ 𝟙 X) (𝟙 Y ⊗ₘ g)).symm
    _ = ((λ_ X).inv ⊗ₘ (ρ_ Y).inv) ≫
        tensorμ (𝟙_ V) X Y (𝟙_ V) ≫
          ((f ⊗ₘ 𝟙 Y) ⊗ₘ (𝟙 X ⊗ₘ g)) := by
      rw [tensorμ_natural]
    _ = (β_ X Y).hom ≫ ((λ_ Y).inv ⊗ₘ (ρ_ X).inv) ≫
        ((f ⊗ₘ 𝟙 Y) ⊗ₘ (𝟙 X ⊗ₘ g)) := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ ((f ⊗ₘ 𝟙 Y) ⊗ₘ (𝟙 X ⊗ₘ g))) hUnit
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun q => (β_ X Y).hom ≫ q)
          (tensorHom_comp_tensorHom (λ_ Y).inv (ρ_ X).inv
            (f ⊗ₘ 𝟙 Y) (𝟙 X ⊗ₘ g))

omit [Category I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I] in
/-- Two actual unit insertions commute through the full middle braid. -/
public theorem tensorMu_two_units_exchange {A B X Y : V}
    (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) :
    (((λ_ X).inv ≫ (f ⊗ₘ 𝟙 X)) ⊗ₘ
        ((ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ g))) ≫ tensorμ A X Y B =
      (β_ X Y).hom ≫
        (((λ_ Y).inv ≫ (f ⊗ₘ 𝟙 Y)) ⊗ₘ
          ((ρ_ X).inv ≫ (𝟙 X ⊗ₘ g))) :=
  tensorMu_unit_exchange f g

/-- Tensor the entire left hom with the actual identity of j. -/
def leftTensorHom (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    (𝟙_ I ⟶[V] i) ⟶ ((𝟙_ I ⊗ j) ⟶[V] (i ⊗ j)) :=
  (ρ_ (𝟙_ I ⟶[V] i)).inv ≫ (𝟙 (𝟙_ I ⟶[V] i) ⊗ₘ eId V j) ≫
    d.tensorMap (𝟙_ I) i j j

/-- Tensor the actual identity of i with the entire right hom. -/
def rightTensorHom (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    (𝟙_ I ⟶[V] j) ⟶ ((i ⊗ 𝟙_ I) ⟶[V] (i ⊗ j)) :=
  (λ_ (𝟙_ I ⟶[V] j)).inv ≫ (eId V i ⊗ₘ 𝟙 (𝟙_ I ⟶[V] j)) ≫
    d.tensorMap i i (𝟙_ I) j

/-- Precompose the selected left tensor hom by the actual inverse index unitor. -/
def leftUnitHom (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    (𝟙_ I ⟶[V] i) ⟶ (j ⟶[V] (i ⊗ j)) :=
  leftTensorHom d i j ≫ eHomWhiskerRight V (λ_ j).inv (i ⊗ j)

/-- Precompose the selected right tensor hom by the actual inverse index unitor. -/
def rightUnitHom (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    (𝟙_ I ⟶[V] j) ⟶ (i ⟶[V] (i ⊗ j)) :=
  rightTensorHom d i j ≫ eHomWhiskerRight V (ρ_ i).inv (i ⊗ j)

/-- The full left hom transport is the contract's literal identity insertion and composition. -/
theorem leftUnitHom_eq (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    leftUnitHom d i j =
      (λ_ (𝟙_ I ⟶[V] i)).inv ≫
        (eHomEquiv V (λ_ j).inv ⊗ₘ leftTensorHom d i j) ≫
        eComp V j (𝟙_ I ⊗ j) (i ⊗ j) := by
  unfold leftUnitHom eHomWhiskerRight
  rw [leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc]

/-- The full right hom transport is the contract's literal identity insertion and composition. -/
theorem rightUnitHom_eq (d : EnrichedMonoidalCategoryData V I) (i j : I) :
    rightUnitHom d i j =
      (λ_ (𝟙_ I ⟶[V] j)).inv ≫
        (eHomEquiv V (ρ_ i).inv ⊗ₘ rightTensorHom d i j) ≫
        eComp V i (i ⊗ 𝟙_ I) (i ⊗ j) := by
  unfold rightUnitHom eHomWhiskerRight
  rw [leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc]

/-- The actual tensor refinement on a supplied generalized element of the left hom. -/
theorem leftTensorHom_eHomEquiv (d : EnrichedMonoidalCategoryData V I)
    {i : I} (f : 𝟙_ I ⟶ i) (j : I) :
    eHomEquiv V f ≫ leftTensorHom d i j = eHomEquiv V (f ⊗ₘ 𝟙 j) := by
  calc
    _ = (ρ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eId V j) ≫
        d.tensorMap (𝟙_ I) i j j := by
      simpa only [leftTensorHom, id_tensorHom, Category.assoc] using
        (rightUnitor_inv_comp_tensorHom_assoc (eHomEquiv V f) (eId V j)
          (d.tensorMap (𝟙_ I) i j j)).symm
    _ = _ := by
      simpa only [eHomEquiv_id, unitors_inv_equal] using
        d.tensorMap_eHomEquiv f (𝟙 j)

/-- The actual tensor refinement on a supplied generalized element of the right hom. -/
theorem rightTensorHom_eHomEquiv (d : EnrichedMonoidalCategoryData V I)
    (i : I) {j : I} (f : 𝟙_ I ⟶ j) :
    eHomEquiv V f ≫ rightTensorHom d i j = eHomEquiv V (𝟙 i ⊗ₘ f) := by
  calc
    _ = (λ_ (𝟙_ V)).inv ≫ (eId V i ⊗ₘ eHomEquiv V f) ≫
        d.tensorMap i i (𝟙_ I) j := by
      simpa only [rightTensorHom, tensorHom_id, Category.assoc] using
        (leftUnitor_inv_comp_tensorHom_assoc (eId V i) (eHomEquiv V f)
          (d.tensorMap i i (𝟙_ I) j)).symm
    _ = _ := by
      simpa only [eHomEquiv_id] using d.tensorMap_eHomEquiv (𝟙 i) f

/-- Left identity transport is the actual inverse index unitor. -/
theorem leftUnitHom_id (d : EnrichedMonoidalCategoryData V I) (j : I) :
    eId V (𝟙_ I) ≫ leftUnitHom d (𝟙_ I) j = eHomEquiv V (λ_ j).inv := by
  unfold leftUnitHom
  rw [← Category.assoc]
  have h := leftTensorHom_eHomEquiv d (𝟙 (𝟙_ I)) j
  simp only [eHomEquiv_id, id_tensorHom_id] at h
  rw [h, eId_comp_eHomWhiskerRight]

/-- Right identity transport is the actual inverse index unitor. -/
theorem rightUnitHom_id (d : EnrichedMonoidalCategoryData V I) (i : I) :
    eId V (𝟙_ I) ≫ rightUnitHom d i (𝟙_ I) = eHomEquiv V (ρ_ i).inv := by
  unfold rightUnitHom
  rw [← Category.assoc]
  have h := rightTensorHom_eHomEquiv d i (𝟙 (𝟙_ I))
  simp only [eHomEquiv_id, id_tensorHom_id] at h
  rw [h, eId_comp_eHomWhiskerRight]

/-- The actual full hom map tensoring with the chosen unit in the first coordinate. -/
private def leftUnitTensorMap (d : EnrichedMonoidalCategoryData V I) (j j' : I) :
    (j ⟶[V] j') ⟶ ((𝟙_ I ⊗ j) ⟶[V] (𝟙_ I ⊗ j')) :=
  (λ_ (j ⟶[V] j')).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (j ⟶[V] j')) ≫
    d.tensorMap (𝟙_ I) (𝟙_ I) j j'

/-- Stored unitor naturality acts on the entire chosen index hom object. -/
private theorem leftUnitTensorMap_natural (d : EnrichedMonoidalCategoryData V I) (j j' : I) :
    leftUnitTensorMap d j j' ≫ eHomWhiskerLeft V (𝟙_ I ⊗ j) (λ_ j').hom =
      eHomWhiskerRight V (λ_ j).hom j' := by
  have h := congrArg (fun v => (λ_ (j ⟶[V] j')).inv ≫ v)
    (d.leftUnitorNaturality j j')
  change
    (λ_ (j ⟶[V] j')).inv ≫ (β_ (𝟙_ V) (j ⟶[V] j')).hom ≫
        (leftUnitTensorMap d j j' ⊗ₘ eHomEquiv V (λ_ j').hom) ≫
        eComp V (𝟙_ I ⊗ j) (𝟙_ I ⊗ j') j' =
      (λ_ (j ⟶[V] j')).inv ≫
        (eHomEquiv V (λ_ j).hom ⊗ₘ 𝟙 (j ⟶[V] j')) ≫
        eComp V (𝟙_ I ⊗ j) j j' at h
  rw [leftUnitor_inv_braiding_assoc, rightUnitor_inv_comp_tensorHom_assoc] at h
  simpa only [eHomWhiskerLeft, eHomWhiskerRight, tensorHom_id, Category.assoc] using h

/-- The actual inverse index unitor conjugates the entire unit-tensor hom map. -/
private theorem leftUnitTensorMap_inv_natural
    (d : EnrichedMonoidalCategoryData V I) (j j' : I) :
    leftUnitTensorMap d j j' ≫ eHomWhiskerRight V (λ_ j).inv (𝟙_ I ⊗ j') =
      eHomWhiskerLeft V j (λ_ j').inv := by
  have h := congrArg
    (fun v => v ≫ eHomWhiskerRight V (λ_ j).inv j' ≫
      eHomWhiskerLeft V j (λ_ j').inv) (leftUnitTensorMap_natural d j j')
  simp only [Category.assoc] at h
  rw [eHom_whisker_exchange_assoc] at h
  simpa only [Category.assoc, ← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, eHomWhiskerLeft_id, eHomWhiskerRight_id,
    Category.comp_id, Category.id_comp] using h

omit [BraidedCategory V] [MonoidalCategory I] in
/-- Composition transports the entire middle hom across a supplied index isomorphism. -/
private theorem eComp_middle_inverse {Y Y' : I} (e : Y ≅ Y') (X Z : I)
    {A : V} (p : A ⟶ (Y ⟶[V] Z)) :
    (eHomWhiskerLeft V X e.inv ⊗ₘ p) ≫ eComp V X Y Z =
      (𝟙 (X ⟶[V] Y') ⊗ₘ (p ≫ eHomWhiskerRight V e.inv Z)) ≫
        eComp V X Y' Z := by
  have h := congrArg
    (fun v => (𝟙 (X ⟶[V] Y') ⊗ₘ (p ≫ eHomWhiskerRight V e.inv Z)) ≫ v)
    (eHom_whisker_cancel_inv (V := V) (X := X) (Z := Z) e)
  simpa only [tensorHom_comp_whiskerRight_assoc, tensorHom_comp_whiskerLeft_assoc,
    Category.id_comp, Category.assoc, ← eHomWhiskerRight_comp,
    Iso.hom_inv_id, eHomWhiskerRight_id, Category.comp_id] using h

variable [MonoidalClosed V]

open scoped MonoidalClosed
open Limits

attribute [local instance] Enriched.prodCategory

/-- The actual full-hom left strength on the original external coefficient. -/
def leftStrengthComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X : I × I) :
    (GradedYoneda.representable (𝟙_ I)).obj X.1 ⊗ F.obj X.2 ⟶
      F.obj (X.1 ⊗ X.2) :=
  (β_ (𝟙_ I ⟶[V] X.1) (F.obj X.2)).hom ≫
    F.obj X.2 ◁ leftUnitHom d X.1 X.2 ≫
    MonoidalClosed.uncurry (F.map X.2 (X.1 ⊗ X.2))

/-- The literal family defining the left Day unitor on every full integrand. -/
def leftForwardGen (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k X ⟶ F.obj k :=
  (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv ≫
    (((β_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1)).hom ≫
        (leftUnitHom d X.1 X.2 ⊗ₘ 𝟙 ((X.1 ⊗ X.2) ⟶[V] k)) ≫
        eComp V X.2 (X.1 ⊗ X.2) k) ⊗ₘ 𝟙 (F.obj X.2)) ≫
    (β_ (X.2 ⟶[V] k) (F.obj X.2)).hom ≫
    MonoidalClosed.uncurry (F.map X.2 k)

/-- The literal family defining the right Day unitor on every full integrand. -/
def rightForwardGen (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k X ⟶ F.obj k :=
  (β_ ((X.1 ⊗ X.2) ⟶[V] k) (F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2))).hom ≫
    (α_ (F.obj X.1) (𝟙_ I ⟶[V] X.2) ((X.1 ⊗ X.2) ⟶[V] k)).hom ≫
    F.obj X.1 ◁ ((rightUnitHom d X.1 X.2 ⊗ₘ 𝟙 ((X.1 ⊗ X.2) ⟶[V] k)) ≫
      eComp V X.1 (X.1 ⊗ X.2) k) ≫
    MonoidalClosed.uncurry (F.map X.1 k)

/-- The left inverse inserts the actual unit identity into the chosen (unit,k)-generator. -/
def leftInvComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k)] :
    F.obj k ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k :=
  (λ_ (F.obj k)).inv ≫
    (eHomEquiv V (λ_ k).hom ⊗ₘ
      ((λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k)))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k (𝟙_ I, k)

/-- The right inverse inserts the actual unit identity into the chosen (k,unit)-generator. -/
def rightInvComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k)] :
    F.obj k ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k :=
  (λ_ (F.obj k)).inv ≫
    (eHomEquiv V (ρ_ k).hom ⊗ₘ
      ((ρ_ (F.obj k)).inv ≫ (𝟙 (F.obj k) ⊗ₘ eId V (𝟙_ I)))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k (k, 𝟙_ I)

/-- The actual full relation face moving i to the chosen index unit. -/
private def leftRelationOne (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k X ⟶
      EnrichedDayKernel.relations d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k ((𝟙_ I, X.2), X) :=
  ((X.1 ⊗ X.2) ⟶[V] k) ◁
    (((ρ_ (𝟙_ I ⟶[V] X.1)).inv ≫
        (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ eId V X.2)) ⊗ₘ
      ((λ_ (F.obj X.2)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj X.2))))

/-- The actual full relation face moving j to output k through the chosen unitor. -/
private def leftRelationTwo (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k j : I) :
    ((𝟙_ I ⊗ j) ⟶[V] k) ⊗ F.obj j ⟶
      EnrichedDayKernel.relations d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k ((𝟙_ I, j), (𝟙_ I, k)) :=
  (λ_ (((𝟙_ I ⊗ j) ⟶[V] k) ⊗ F.obj j)).inv ≫
    (eHomEquiv V (λ_ k).hom ⊗ₘ
      (((λ_ ((𝟙_ I ⊗ j) ⟶[V] k)).inv ≫
          (eId V (𝟙_ I) ⊗ₘ eHomWhiskerRight V (λ_ j).inv k)) ⊗ₘ
        ((λ_ (F.obj j)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj j)))))

variable (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

/-- The literal reduced generator at the chosen first-coordinate unit. -/
private def leftCanonicalGen (j : I) :
    ((𝟙_ I ⊗ j) ⟶[V] k) ⊗ F.obj j ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k :=
  (𝟙 ((𝟙_ I ⊗ j) ⟶[V] k) ⊗ₘ
      ((λ_ (F.obj j)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj j)))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k (𝟙_ I, j)

end Data

section InputGeneratorNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- Genuine input transformations retain the literal left unitor generator family. -/
theorem leftForwardGen_input_natural (d : EnrichedMonoidalCategoryData V I)
    {F G : EnrichedFunctor V I V}
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    (k : I) (X : I × I) :
    (((X.1 ⊗ X.2) ⟶[V] k) ◁
        (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ (eHomEquiv V).symm (a.app X.2))) ≫
        leftForwardGen d G k X =
      leftForwardGen d F k X ≫ (eHomEquiv V).symm (a.app k) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.1
  let H : V := X.2 ⟶[V] k
  let c : W ⊗ U ⟶ H :=
    (β_ W U).hom ≫ (leftUnitHom d X.1 X.2 ⊗ₘ 𝟙 W) ≫
      eComp V X.2 (X.1 ⊗ X.2) k
  let f : F.obj X.2 ⟶ G.obj X.2 := (eHomEquiv V).symm (a.app X.2)
  let g : F.obj k ⟶ G.obj k := (eHomEquiv V).symm (a.app k)
  have hAction :
      (f ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (G.map X.2 k) =
        MonoidalClosed.uncurry (F.map X.2 k) ≫ g :=
    (a.uncurriedNaturality X.2 k).symm
  have hAssoc :
      W ◁ (𝟙 U ⊗ₘ f) ≫ (α_ W U (G.obj X.2)).inv =
        (α_ W U (F.obj X.2)).inv ≫ (𝟙 (W ⊗ U) ⊗ₘ f) := by
    simpa only [id_tensorHom] using associator_inv_naturality_right W U f
  have hTensor :
      (𝟙 (W ⊗ U) ⊗ₘ f) ≫ (c ⊗ₘ 𝟙 (G.obj X.2)) =
        (c ⊗ₘ 𝟙 (F.obj X.2)) ≫ (𝟙 H ⊗ₘ f) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hBraid :
      (𝟙 H ⊗ₘ f) ≫ (β_ H (G.obj X.2)).hom =
        (β_ H (F.obj X.2)).hom ≫ (f ⊗ₘ 𝟙 H) :=
    braiding_naturality (𝟙 H) f
  have hWord :
      W ◁ (𝟙 U ⊗ₘ f) ≫ (α_ W U (G.obj X.2)).inv ≫
          (c ⊗ₘ 𝟙 (G.obj X.2)) ≫ (β_ H (G.obj X.2)).hom ≫
          MonoidalClosed.uncurry (G.map X.2 k) =
        ((α_ W U (F.obj X.2)).inv ≫ (c ⊗ₘ 𝟙 (F.obj X.2)) ≫
          (β_ H (F.obj X.2)).hom ≫ MonoidalClosed.uncurry (F.map X.2 k)) ≫ g := by
    calc
      _ = (α_ W U (F.obj X.2)).inv ≫ (𝟙 (W ⊗ U) ⊗ₘ f) ≫
          (c ⊗ₘ 𝟙 (G.obj X.2)) ≫ (β_ H (G.obj X.2)).hom ≫
          MonoidalClosed.uncurry (G.map X.2 k) := by
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ (c ⊗ₘ 𝟙 (G.obj X.2)) ≫
            (β_ H (G.obj X.2)).hom ≫ MonoidalClosed.uncurry (G.map X.2 k)) hAssoc
      _ = (α_ W U (F.obj X.2)).inv ≫ (c ⊗ₘ 𝟙 (F.obj X.2)) ≫
          (𝟙 H ⊗ₘ f) ≫ (β_ H (G.obj X.2)).hom ≫
          MonoidalClosed.uncurry (G.map X.2 k) := by
        simpa only [Category.assoc] using
          congrArg (fun q => (α_ W U (F.obj X.2)).inv ≫ q ≫
            (β_ H (G.obj X.2)).hom ≫ MonoidalClosed.uncurry (G.map X.2 k)) hTensor
      _ = (α_ W U (F.obj X.2)).inv ≫ (c ⊗ₘ 𝟙 (F.obj X.2)) ≫
          (β_ H (F.obj X.2)).hom ≫ (f ⊗ₘ 𝟙 H) ≫
          MonoidalClosed.uncurry (G.map X.2 k) := by
        simpa only [Category.assoc] using
          congrArg (fun q => (α_ W U (F.obj X.2)).inv ≫
            (c ⊗ₘ 𝟙 (F.obj X.2)) ≫ q ≫
            MonoidalClosed.uncurry (G.map X.2 k)) hBraid
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun q => (α_ W U (F.obj X.2)).inv ≫
            (c ⊗ₘ 𝟙 (F.obj X.2)) ≫ (β_ H (F.obj X.2)).hom ≫ q) hAction
  have hF : leftForwardGen d F k X =
      (α_ W U (F.obj X.2)).inv ≫ (c ⊗ₘ 𝟙 (F.obj X.2)) ≫
        (β_ H (F.obj X.2)).hom ≫ MonoidalClosed.uncurry (F.map X.2 k) := rfl
  have hG : leftForwardGen d G k X =
      (α_ W U (G.obj X.2)).inv ≫ (c ⊗ₘ 𝟙 (G.obj X.2)) ≫
        (β_ H (G.obj X.2)).hom ≫ MonoidalClosed.uncurry (G.map X.2 k) := rfl
  exact (congrArg (fun q => W ◁ (𝟙 U ⊗ₘ f) ≫ q) hG).trans
    (hWord.trans (congrArg (fun q => q ≫ g) hF).symm)

end InputGeneratorNaturality

section ProductUnitLaws

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uI} [EnrichedCategory V C]
  {D : Type vI} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

/-- Full product composition with two identity insertions is the actual middle braid. -/
private theorem productComp_two_identities (c c' : C) (d d' : D) :
    (((λ_ (d ⟶[V] d')).inv ≫
          (eId V c ⊗ₘ 𝟙 (d ⟶[V] d'))) ⊗ₘ
        ((ρ_ (c ⟶[V] c')).inv ≫
          (𝟙 (c ⟶[V] c') ⊗ₘ eId V d'))) ≫
      eComp V (c, d) (c, d') (c', d') =
        (β_ (d ⟶[V] d') (c ⟶[V] c')).hom := by
  have h0 := tensorMu_unit_exchange (X := d ⟶[V] d') (Y := c ⟶[V] c')
    (eId V c) (eId V d')
  have h := congrArg
    (fun v => v ≫ (eComp V c c c' ⊗ₘ eComp V d d' d')) h0
  have hProd : eComp V (c, d) (c, d') (c', d') =
      tensorμ (c ⟶[V] c) (d ⟶[V] d') (c ⟶[V] c') (d' ⟶[V] d') ≫
        (eComp V c c c' ⊗ₘ eComp V d d' d') := rfl
  rw [hProd]
  simpa only [Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_id, id_tensorHom, e_id_comp, e_comp_id, id_tensorHom_id,
    id_whiskerRight, Category.comp_id] using h

/-- The first identity-padded product hom composes the full active first hom. -/
private theorem productComp_first_identity (c₀ c₁ c₂ : C) (d₀ d₁ : D) :
    (((ρ_ (c₀ ⟶[V] c₁)).inv ≫
          (𝟙 (c₀ ⟶[V] c₁) ⊗ₘ eId V d₀)) ⊗ₘ
        𝟙 ((c₁ ⟶[V] c₂) ⊗ (d₀ ⟶[V] d₁))) ≫
      eComp V (c₀, d₀) (c₁, d₀) (c₂, d₁) =
        (α_ (c₀ ⟶[V] c₁) (c₁ ⟶[V] c₂) (d₀ ⟶[V] d₁)).inv ≫
          (eComp V c₀ c₁ c₂ ⊗ₘ 𝟙 (d₀ ⟶[V] d₁)) := by
  let U : V := c₀ ⟶[V] c₁
  let P : V := c₁ ⟶[V] c₂
  let Q : V := d₀ ⟶[V] d₁
  have hUnit :
      (ρ_ U).inv ▷ (P ⊗ Q) ≫ tensorμ U (𝟙_ V) P Q =
        (α_ U P Q).inv ≫ (𝟙 (U ⊗ P) ⊗ₘ (λ_ Q).inv) := by
    dsimp only [tensorμ]
    rw [braiding_tensorUnit_left]
    monoidal
  have h := congrArg
    (fun v => v ≫ ((𝟙 U ▷ P ⊗ₘ eId V d₀ ▷ Q) ≫
      (eComp V c₀ c₁ c₂ ⊗ₘ eComp V d₀ d₀ d₁))) hUnit
  have hProd : eComp V (c₀, d₀) (c₁, d₀) (c₂, d₁) =
      tensorμ U (d₀ ⟶[V] d₀) P Q ≫
        (eComp V c₀ c₁ c₂ ⊗ₘ eComp V d₀ d₀ d₁) := rfl
  have hNat := tensorμ_natural_left (𝟙 U) (eId V d₀) P Q
  have hPad := congrArg
    (fun q => (ρ_ U).inv ▷ (P ⊗ Q) ≫ q ≫
      (eComp V c₀ c₁ c₂ ⊗ₘ eComp V d₀ d₀ d₁)) hNat
  rw [hProd]
  calc
    _ = (ρ_ U).inv ▷ (P ⊗ Q) ≫ tensorμ U (𝟙_ V) P Q ≫
        (𝟙 U ▷ P ⊗ₘ eId V d₀ ▷ Q) ≫
        (eComp V c₀ c₁ c₂ ⊗ₘ eComp V d₀ d₀ d₁) := by
      simpa only [U, P, Q, tensorHom_id, comp_whiskerRight, Category.assoc] using hPad
    _ = _ := by
      simpa only [U, P, Q, id_whiskerRight, tensorHom_comp_tensorHom,
        Category.assoc, e_id_comp, Category.id_comp] using h

end ProductUnitLaws

section FullUnitors

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
/-- The entire left active hom composes before applying the tensor map. -/
private theorem leftTensorHom_comp_full (d : EnrichedMonoidalCategoryData V I)
    (i i' j j' : I) :
    (leftTensorHom d i j ⊗ₘ d.tensorMap i i' j j') ≫
        eComp V (𝟙_ I ⊗ j) (i ⊗ j) (i' ⊗ j') =
      (α_ (𝟙_ I ⟶[V] i) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (eComp V (𝟙_ I) i i' ⊗ₘ 𝟙 (j ⟶[V] j')) ≫
        d.tensorMap (𝟙_ I) i' j j' := by
  let r : (𝟙_ I ⟶[V] i) ⟶ (𝟙_ I ⟶[V] i) ⊗ (j ⟶[V] j) :=
    (ρ_ (𝟙_ I ⟶[V] i)).inv ≫ (𝟙 (𝟙_ I ⟶[V] i) ⊗ₘ eId V j)
  have hPad := productComp_first_identity (V := V) (𝟙_ I) i i' j j'
  change
    (r ⊗ₘ 𝟙 ((i ⟶[V] i') ⊗ (j ⟶[V] j'))) ≫
        (Enriched.prodCategory V I I).comp (𝟙_ I, j) (i, j) (i', j') =
      (α_ (𝟙_ I ⟶[V] i) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (eComp V (𝟙_ I) i i' ⊗ₘ 𝟙 (j ⟶[V] j')) at hPad
  have h := congrArg (fun v => (r ⊗ₘ 𝟙 ((i ⟶[V] i') ⊗ (j ⟶[V] j'))) ≫ v)
    (d.tensorMap_comp (𝟙_ I) i i' j j j')
  rw [← Category.assoc, hPad] at h
  simpa only [leftTensorHom, r, tensorHom_id,
    whiskerRight_comp_tensorHom_assoc, Category.assoc] using h.symm

omit [MonoidalClosed V] in
/-- Mixed tensor homs retain the whole braid between the two active hom objects. -/
private theorem tensorMap_left_mixed (d : EnrichedMonoidalCategoryData V I) (i j j' : I) :
    (β_ (j ⟶[V] j') (𝟙_ I ⟶[V] i)).hom ≫ d.tensorMap (𝟙_ I) i j j' =
      (leftUnitTensorMap d j j' ⊗ₘ leftTensorHom d i j') ≫
        eComp V (𝟙_ I ⊗ j) (𝟙_ I ⊗ j') (i ⊗ j') := by
  let p : (j ⟶[V] j') ⟶ (𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] j') :=
    (λ_ (j ⟶[V] j')).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (j ⟶[V] j'))
  let q : (𝟙_ I ⟶[V] i) ⟶ (𝟙_ I ⟶[V] i) ⊗ (j' ⟶[V] j') :=
    (ρ_ (𝟙_ I ⟶[V] i)).inv ≫ (𝟙 (𝟙_ I ⟶[V] i) ⊗ₘ eId V j')
  have hPad := productComp_two_identities (V := V) (𝟙_ I) i j j'
  change
    (p ⊗ₘ q) ≫ (Enriched.prodCategory V I I).comp
        (𝟙_ I, j) (𝟙_ I, j') (i, j') =
      (β_ (j ⟶[V] j') (𝟙_ I ⟶[V] i)).hom at hPad
  have h := congrArg (fun v => (p ⊗ₘ q) ≫ v)
    (d.tensorMap_comp (𝟙_ I) (𝟙_ I) i j j' j')
  rw [← Category.assoc, hPad] at h
  simpa only [leftUnitTensorMap, leftTensorHom, p, q,
    ← tensorHom_comp_tensorHom, Category.assoc] using h

omit [MonoidalClosed V] in
/-- Symmetry expresses the full mixed tensor hom with the requested source-first order. -/
private theorem tensorMap_left_mixed_symm (d : EnrichedMonoidalCategoryData V I)
    (i j j' : I) :
    d.tensorMap (𝟙_ I) i j j' =
      (β_ (𝟙_ I ⟶[V] i) (j ⟶[V] j')).hom ≫
        (leftUnitTensorMap d j j' ⊗ₘ leftTensorHom d i j') ≫
        eComp V (𝟙_ I ⊗ j) (𝟙_ I ⊗ j') (i ⊗ j') := by
  have h := congrArg (fun v => (β_ (𝟙_ I ⟶[V] i) (j ⟶[V] j')).hom ≫ v)
    (tensorMap_left_mixed d i j j')
  simpa only [Category.assoc, SymmetricCategory.symmetry_assoc, Category.id_comp] using h

omit [MonoidalClosed V] in
/-- The actual inverse unitor moves through the full index contraction. -/
private theorem leftTensorHom_middle_transport (d : EnrichedMonoidalCategoryData V I)
    (i j j' : I) :
    (leftUnitTensorMap d j j' ⊗ₘ leftTensorHom d i j') ≫
        eComp V (𝟙_ I ⊗ j) (𝟙_ I ⊗ j') (i ⊗ j') ≫
        eHomWhiskerRight V (λ_ j).inv (i ⊗ j') =
      (𝟙 (j ⟶[V] j') ⊗ₘ leftUnitHom d i j') ≫
        eComp V j j' (i ⊗ j') := by
  rw [eComp_eHomWhiskerRight, tensorHom_comp_whiskerRight_assoc,
    leftUnitTensorMap_inv_natural,
    eComp_middle_inverse (λ_ j') j (i ⊗ j') (leftTensorHom d i j')]
  rfl

omit [MonoidalClosed V] in
/-- The complete two-coordinate hom identity behind the left Day unitor. -/
private theorem leftUnitHom_product_natural (d : EnrichedMonoidalCategoryData V I)
    (i i' j j' : I) :
    (leftUnitHom d i j ⊗ₘ d.tensorMap i i' j j') ≫
        eComp V j (i ⊗ j) (i' ⊗ j') =
      (α_ (𝟙_ I ⟶[V] i) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (eComp V (𝟙_ I) i i' ⊗ₘ 𝟙 (j ⟶[V] j')) ≫
        (β_ (𝟙_ I ⟶[V] i') (j ⟶[V] j')).hom ≫
        (𝟙 (j ⟶[V] j') ⊗ₘ leftUnitHom d i' j') ≫
          eComp V j j' (i' ⊗ j') := by
  calc
    _ = ((leftTensorHom d i j ⊗ₘ d.tensorMap i i' j j') ≫
          eComp V (𝟙_ I ⊗ j) (i ⊗ j) (i' ⊗ j')) ≫
        eHomWhiskerRight V (λ_ j).inv (i' ⊗ j') := by
      unfold leftUnitHom
      rw [← tensorHom_comp_whiskerRight_assoc, ← eComp_eHomWhiskerRight]
      simp only [Category.assoc]
    _ = ((α_ (𝟙_ I ⟶[V] i) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
          (eComp V (𝟙_ I) i i' ⊗ₘ 𝟙 (j ⟶[V] j')) ≫
          d.tensorMap (𝟙_ I) i' j j') ≫
        eHomWhiskerRight V (λ_ j).inv (i' ⊗ j') :=
      congrArg (fun v => v ≫ eHomWhiskerRight V (λ_ j).inv (i' ⊗ j'))
        (leftTensorHom_comp_full d i i' j j')
    _ = _ := by
      rw [tensorMap_left_mixed_symm]
      simp only [Category.assoc]
      rw [leftTensorHom_middle_transport]

/-- The left strength retains naturality on the entire product-enriched hom. -/
theorem leftStrength_natural (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X Y : I × I) :
    MonoidalClosed.uncurry
        (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map X Y) ≫
        leftStrengthComponent d F Y =
      (leftStrengthComponent d F X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) := by
  let a : V := 𝟙_ I ⟶[V] X.1
  let b : V := 𝟙_ I ⟶[V] Y.1
  let P : V := X.1 ⟶[V] Y.1
  let Q : V := X.2 ⟶[V] Y.2
  let z : V := F.obj X.2
  let z' : V := F.obj Y.2
  let A : I := X.1 ⊗ X.2
  let B : I := Y.1 ⊗ Y.2
  let J : V := X.2 ⟶[V] A
  let L : V := Y.2 ⟶[V] B
  let M : V := A ⟶[V] B
  let p : a ⊗ P ⟶ b := eComp V (𝟙_ I) X.1 Y.1
  let q : z ⊗ Q ⟶ z' := MonoidalClosed.uncurry (F.map X.2 Y.2)
  let t : P ⊗ Q ⟶ M := d.tensorMap X.1 Y.1 X.2 Y.2
  let theta : a ⟶ J := leftUnitHom d X.1 X.2
  let theta' : b ⟶ L := leftUnitHom d Y.1 Y.2
  let u : z ⊗ J ⟶ F.obj A := MonoidalClosed.uncurry (F.map X.2 A)
  let v : z' ⊗ L ⟶ F.obj B := MonoidalClosed.uncurry (F.map Y.2 B)
  let w : F.obj A ⊗ M ⟶ F.obj B := MonoidalClosed.uncurry (F.map A B)
  let cX : J ⊗ M ⟶ (X.2 ⟶[V] B) := eComp V X.2 A B
  let cY : Q ⊗ L ⟶ (X.2 ⟶[V] B) := eComp V X.2 Y.2 B
  let act : z ⊗ (X.2 ⟶[V] B) ⟶ F.obj B :=
    MonoidalClosed.uncurry (F.map X.2 B)
  let S : (a ⊗ z) ⊗ (P ⊗ Q) ⟶ (z ⊗ Q) ⊗ (a ⊗ P) :=
    tensorμ a z P Q ≫ (β_ (a ⊗ P) (z ⊗ Q)).hom
  let k0 : (a ⊗ z) ⊗ (P ⊗ Q) ⟶ z ⊗ (a ⊗ (P ⊗ Q)) :=
    (β_ a z).hom ▷ (P ⊗ Q) ≫ (α_ z a (P ⊗ Q)).hom
  let r : (a ⊗ z) ⊗ (P ⊗ Q) ⟶ z ⊗ (Q ⊗ b) :=
    S ≫ (𝟙 (z ⊗ Q) ⊗ₘ p) ≫ (α_ z Q b).hom
  have hShuffle :
      k0 ≫ z ◁ ((α_ a P Q).inv ≫ (β_ (a ⊗ P) Q).hom) =
        S ≫ (α_ z Q (a ⊗ P)).hom := by
    have hExpand :
        S ≫ (α_ z Q (a ⊗ P)).hom =
          (α_ a z (P ⊗ Q)).hom ≫ a ◁ (α_ z P Q).inv ≫
            a ◁ (((β_ z P).hom ≫ (β_ P z).hom) ▷ Q) ≫
            (α_ a (z ⊗ P) Q).inv ≫ (α_ a z P).inv ▷ Q ≫
            (β_ a z).hom ▷ P ▷ Q ≫ (α_ z a P).hom ▷ Q ≫
            (α_ z (a ⊗ P) Q).hom ≫ z ◁ (β_ (a ⊗ P) Q).hom := by
      dsimp only [S, tensorμ]
      rw [braiding_tensor_right_hom (a ⊗ P) z Q, braiding_tensor_left_hom a P z]
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      monoidal
    calc
      _ = (α_ a z (P ⊗ Q)).hom ≫ a ◁ (α_ z P Q).inv ≫
          a ◁ (((β_ z P).hom ≫ (β_ P z).hom) ▷ Q) ≫
          (α_ a (z ⊗ P) Q).inv ≫ (α_ a z P).inv ▷ Q ≫
          (β_ a z).hom ▷ P ▷ Q ≫ (α_ z a P).hom ▷ Q ≫
          (α_ z (a ⊗ P) Q).hom ≫ z ◁ (β_ (a ⊗ P) Q).hom := by
        rw [SymmetricCategory.symmetry]
        dsimp only [k0]
        simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
          whiskerLeft_comp, Category.assoc]
        monoidal
      _ = _ := hExpand.symm
  have hp : (p ⊗ₘ 𝟙 Q) ≫ (β_ b Q).hom =
      (β_ (a ⊗ P) Q).hom ≫ (𝟙 Q ⊗ₘ p) :=
    braiding_naturality p (𝟙 Q)
  have hk :
      k0 ≫ z ◁ ((α_ a P Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ (β_ b Q).hom) = r := by
    calc
      _ = (k0 ≫ z ◁ ((α_ a P Q).inv ≫ (β_ (a ⊗ P) Q).hom)) ≫
          z ◁ (𝟙 Q ⊗ₘ p) := by
        rw [hp]
        simp only [whiskerLeft_comp, Category.assoc]
      _ = (S ≫ (α_ z Q (a ⊗ P)).hom) ≫ z ◁ (𝟙 Q ⊗ₘ p) :=
        congrArg (fun f => f ≫ z ◁ (𝟙 Q ⊗ₘ p)) hShuffle
      _ = r := by
        simpa only [r, id_tensorHom, Category.assoc] using
          congrArg (fun f => S ≫ f) (associator_naturality_right z Q p).symm
  have hMoveY :
      (𝟙 (z ⊗ Q) ⊗ₘ p) ≫ (α_ z Q b).hom ≫ z ◁ (Q ◁ theta') ≫
          (α_ z Q L).inv ≫ (q ▷ L) =
        (q ⊗ₘ p) ≫ z' ◁ theta' := by
    rw [← associator_naturality_right_assoc, Iso.hom_inv_id_assoc]
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  have hActionY : z ◁ cY ≫ act =
      (α_ z Q L).inv ≫ (q ▷ L) ≫ v :=
    action_comp F X.2 Y.2 B
  have hY :
      r ≫ z ◁ ((Q ◁ theta') ≫ cY) ≫ act =
        S ≫ (q ⊗ₘ p) ≫ z' ◁ theta' ≫ v := by
    calc
      _ = r ≫ z ◁ (Q ◁ theta') ≫ (z ◁ cY ≫ act) := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
      _ = r ≫ z ◁ (Q ◁ theta') ≫ (α_ z Q L).inv ≫ (q ▷ L) ≫ v := by
        rw [hActionY]
      _ = _ := by
        simpa only [r, Category.assoc] using
          congrArg (fun f => S ≫ f ≫ v) hMoveY
  have hTheta :
      (theta ⊗ₘ t) ≫ cX =
        (α_ a P Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ (β_ b Q).hom ≫
          (Q ◁ theta') ≫ cY := by
    simpa only [a, b, P, Q, p, t, theta, theta', cX, cY, A, B, id_tensorHom] using
      leftUnitHom_product_natural d X.1 Y.1 X.2 Y.2
  have hIndex :
      k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act =
        r ≫ z ◁ ((Q ◁ theta') ≫ cY) ≫ act := by
    let b0 : a ⊗ (P ⊗ Q) ⟶ Q ⊗ b :=
      (α_ a P Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ (β_ b Q).hom
    let b1 : Q ⊗ b ⟶ (X.2 ⟶[V] B) := (Q ◁ theta') ≫ cY
    have hI : (theta ⊗ₘ t) ≫ cX = b0 ≫ b1 := by
      simpa only [b0, b1, Category.assoc] using hTheta
    have hW := congrArg
      (fun f : a ⊗ (P ⊗ Q) ⟶ (X.2 ⟶[V] B) => k0 ≫ z ◁ f ≫ act) hI
    have hF : k0 ≫ z ◁ (b0 ≫ b1) ≫ act =
        (k0 ≫ z ◁ b0) ≫ z ◁ b1 ≫ act := by
      simp only [whiskerLeft_comp, Category.assoc]
    have hK := congrArg
      (fun f : (a ⊗ z) ⊗ (P ⊗ Q) ⟶ z ⊗ (Q ⊗ b) => f ≫ z ◁ b1 ≫ act) hk
    exact hW.trans (hF.trans hK)
  have hMoveX :
      k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (α_ z J M).inv ≫ (u ▷ M) =
        (((β_ a z).hom ≫ z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫
          (𝟙 (F.obj A) ⊗ₘ t) := by
    have ha := associator_inv_naturality (𝟙 z) theta t
    simp only [id_tensorHom] at ha
    have h := congrArg
      (fun f => (β_ a z).hom ▷ (P ⊗ Q) ≫ (α_ z a (P ⊗ Q)).hom ≫ f ≫ (u ▷ M)) ha
    simpa only [k0, Category.assoc, Iso.hom_inv_id_assoc, ← tensorHom_id,
      ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using h
  have hActionX : z ◁ cX ≫ act =
      (α_ z J M).inv ≫ (u ▷ M) ≫ w :=
    action_comp F X.2 A B
  have hX :
      k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act =
        (((β_ a z).hom ≫ z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫
          (𝟙 (F.obj A) ⊗ₘ t) ≫ w := by
    calc
      _ = k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (z ◁ cX ≫ act) := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
      _ = k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (α_ z J M).inv ≫ (u ▷ M) ≫ w := by
        rw [hActionX]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ w) hMoveX
  have hExternal :
      MonoidalClosed.uncurry
          (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map X Y) =
        tensorμ a z P Q ≫ (p ⊗ₘ q) := by
    rw [EnrichedFunctor.externalTensor_uncurry, GradedYoneda.representable_uncurry]
  have hTarget :
      MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) =
        (𝟙 (F.obj A) ⊗ₘ t) ≫ w := by
    change MonoidalClosed.uncurry (t ≫ F.map A B) = _
    rw [MonoidalClosed.uncurry_natural_left, id_tensorHom]
  let sX : a ⊗ z ⟶ F.obj A := leftStrengthComponent d F X
  let sY : b ⊗ z' ⟶ F.obj B := leftStrengthComponent d F Y
  have hSX : sX = (β_ a z).hom ≫ z ◁ theta ≫ u := rfl
  have hSY : sY = (β_ b z').hom ≫ z' ◁ theta' ≫ v := rfl
  have hE := congrArg
    (fun f : (a ⊗ z) ⊗ (P ⊗ Q) ⟶ b ⊗ z' => f ≫ sY) hExternal
  have hT := congrArg
    (fun f : F.obj A ⊗ (P ⊗ Q) ⟶ F.obj B => (sX ⊗ₘ 𝟙 (P ⊗ Q)) ≫ f) hTarget
  have hWord :
      (tensorμ a z P Q ≫ (p ⊗ₘ q)) ≫ sY =
        (sX ⊗ₘ 𝟙 (P ⊗ Q)) ≫ ((𝟙 (F.obj A) ⊗ₘ t) ≫ w) := by
    calc
      _ = tensorμ a z P Q ≫ (p ⊗ₘ q) ≫ (β_ b z').hom ≫ z' ◁ theta' ≫ v := by
        simpa only [Category.assoc] using
          congrArg (fun f => (tensorμ a z P Q ≫ (p ⊗ₘ q)) ≫ f) hSY
      _ = S ≫ (q ⊗ₘ p) ≫ z' ◁ theta' ≫ v := by
        rw [braiding_naturality_assoc]
        simp only [S, Category.assoc]
      _ = r ≫ z ◁ ((Q ◁ theta') ≫ cY) ≫ act := hY.symm
      _ = k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act := hIndex.symm
      _ = (((β_ a z).hom ≫ z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫
          (𝟙 (F.obj A) ⊗ₘ t) ≫ w := hX
      _ = _ := congrArg
        (fun f => (f ⊗ₘ 𝟙 (P ⊗ Q)) ≫ (𝟙 (F.obj A) ⊗ₘ t) ≫ w) hSX.symm
  exact hE.trans (hWord.trans hT.symm)

/-- The genuine left strength uses the actual full-hom component equation. -/
abbrev leftStrength (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      ((GradedYoneda.representable (𝟙_ I)).externalTensor F)
      (d.tensorEnrichedFunctor.comp V F) :=
  GradedNatTrans.unitOfComponents (leftStrengthComponent d F) (leftStrength_natural d F)

/-- Components of the genuine strength are the literal chosen hom transport. -/
theorem leftStrength_component (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X : I × I) :
    (eHomEquiv V).symm ((leftStrength d F).app X) = leftStrengthComponent d F X :=
  GradedNatTrans.unitOfComponents_component _ _ X

/-- The actual evaluation cocone after the binary index object. -/
private def evaluationGen (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    ((X.1 ⊗ X.2) ⟶[V] k) ⊗ F.obj (X.1 ⊗ X.2) ⟶ F.obj k :=
  (β_ ((X.1 ⊗ X.2) ⟶[V] k) (F.obj (X.1 ⊗ X.2))).hom ≫
    MonoidalClosed.uncurry (F.map (X.1 ⊗ X.2) k)

/-- Pull the actual limit-free co-Yoneda cocone equation back along the full T hom map. -/
private theorem evaluationGen_balanced (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X Y : I × I) :
    ((α_ ((Y.1 ⊗ Y.2) ⟶[V] k) (X ⟶[V] Y) (F.obj (X.1 ⊗ X.2))).inv ≫
        ((((Y.1 ⊗ Y.2) ⟶[V] k) ◁ d.tensorMap X.1 Y.1 X.2 Y.2 ≫
            (β_ ((Y.1 ⊗ Y.2) ⟶[V] k) ((X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2))).hom ≫
            eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ
          𝟙 (F.obj (X.1 ⊗ X.2)))) ≫ evaluationGen F k X =
      ((Y.1 ⊗ Y.2) ⟶[V] k) ◁
          ((β_ (X ⟶[V] Y) (F.obj (X.1 ⊗ X.2))).hom ≫
            MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y)) ≫
        evaluationGen F k Y := by
  let W : V := (Y.1 ⊗ Y.2) ⟶[V] k
  let A : V := F.obj (X.1 ⊗ X.2)
  let H : V := X ⟶[V] Y
  let K : V := (X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2)
  let t : H ⟶ K := d.tensorMap X.1 Y.1 X.2 Y.2
  let r : W ⊗ (H ⊗ A) ⟶ W ⊗ (K ⊗ A) := W ◁ (t ⊗ₘ 𝟙 A)
  have hLeft :
      r ≫ (α_ W K A).inv ≫
          (((β_ W K).hom ≫ eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 A) =
        (α_ W H A).inv ≫
          ((W ◁ t ≫ (β_ W K).hom ≫
            eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 A) := by
    dsimp only [r]
    rw [tensorHom_id, associator_inv_naturality_middle_assoc,
      whiskerRight_comp_tensorHom]
  have hRight :
      r ≫ W ◁ ((β_ K A).hom ≫ MonoidalClosed.uncurry
          (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))) =
        W ◁ ((β_ H A).hom ≫ MonoidalClosed.uncurry
          ((d.tensorEnrichedFunctor.comp V F).map X Y)) := by
    let v : A ⊗ K ⟶ F.obj (Y.1 ⊗ Y.2) :=
      MonoidalClosed.uncurry (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))
    let vT : A ⊗ H ⟶ F.obj (Y.1 ⊗ Y.2) :=
      MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y)
    have hT : vT = (A ◁ t) ≫ v := by
      change MonoidalClosed.uncurry
        (t ≫ F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2)) = _
      exact MonoidalClosed.uncurry_natural_left t
        (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))
    calc
      _ = W ◁ ((t ⊗ₘ 𝟙 A) ≫ (β_ K A).hom ≫
          MonoidalClosed.uncurry (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))) := by
        simp only [r, whiskerLeft_comp]
      _ = W ◁ ((β_ H A).hom ≫ (𝟙 A ⊗ₘ t) ≫
          MonoidalClosed.uncurry (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))) :=
        congrArg (fun f => W ◁ f)
          (braiding_naturality_assoc t (𝟙 A)
            (MonoidalClosed.uncurry (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))))
      _ = _ := by
        have hT0 : (𝟙 A ⊗ₘ t) ≫ v = vT :=
          (congrArg (fun f : A ⊗ H ⟶ A ⊗ K => f ≫ v)
            (id_tensorHom A t)).trans hT.symm
        exact congrArg
          (fun f : A ⊗ H ⟶ F.obj (Y.1 ⊗ Y.2) => W ◁ ((β_ H A).hom ≫ f)) hT0
  change (show W ⊗ (H ⊗ A) ⟶ F.obj k from
      ((α_ W H A).inv ≫
        ((W ◁ t ≫ (β_ W K).hom ≫
          eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 A)) ≫
        evaluationGen F k X) =
    (show W ⊗ (H ⊗ A) ⟶ F.obj k from
      W ◁ ((β_ H A).hom ≫ MonoidalClosed.uncurry
        ((d.tensorEnrichedFunctor.comp V F).map X Y)) ≫ evaluationGen F k Y)
  calc
    _ = (r ≫ (α_ W K A).inv ≫
          (((β_ W K).hom ≫ eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 A)) ≫
        evaluationGen F k X := by
      simpa only [W, A, H, K, t, Category.assoc] using
        congrArg (fun v => v ≫ evaluationGen F k X) hLeft.symm
    _ = r ≫ (W ◁ ((β_ K A).hom ≫ MonoidalClosed.uncurry
          (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))) ≫ evaluationGen F k Y) := by
      simpa only [evaluationGen, W, A, H, K, t, Category.assoc] using
        congrArg (fun v => r ≫ v)
          (Enriched.weightedCoend.coyonedaCondition F k
            (X.1 ⊗ X.2) (Y.1 ⊗ Y.2))
    _ = _ := by
      exact (Category.assoc r
        (W ◁ ((β_ K A).hom ≫ MonoidalClosed.uncurry
          (F.map (X.1 ⊗ X.2) (Y.1 ⊗ Y.2)))) (evaluationGen F k Y)).symm.trans
          (congrArg
            (fun f : W ⊗ (H ⊗ A) ⟶ W ⊗ F.obj (Y.1 ⊗ Y.2) =>
              f ≫ evaluationGen F k Y) hRight)

/-- The literal left unitor family is the actual strength followed by evaluation. -/
private theorem leftForwardGen_eq_strength (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    leftForwardGen d F k X =
      (𝟙 ((X.1 ⊗ X.2) ⟶[V] k) ⊗ₘ leftStrengthComponent d F X) ≫
        evaluationGen F k X := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let a : V := 𝟙_ I ⟶[V] X.1
  let z : V := F.obj X.2
  let A : I := X.1 ⊗ X.2
  let J : V := X.2 ⟶[V] A
  let B : V := F.obj A
  let theta : a ⟶ J := leftUnitHom d X.1 X.2
  let c : J ⊗ W ⟶ (X.2 ⟶[V] k) := eComp V X.2 A k
  let u : z ⊗ J ⟶ B := MonoidalClosed.uncurry (F.map X.2 A)
  let v : B ⊗ W ⟶ F.obj k := MonoidalClosed.uncurry (F.map A k)
  let w : z ⊗ (X.2 ⟶[V] k) ⟶ F.obj k := MonoidalClosed.uncurry (F.map X.2 k)
  let K : W ⊗ (a ⊗ z) ⟶ z ⊗ (J ⊗ W) :=
    (α_ W a z).inv ≫ (β_ (W ⊗ a) z).hom ≫
      z ◁ ((β_ W a).hom ≫ (theta ⊗ₘ 𝟙 W))
  have hStructure :
      (α_ W a z).inv ≫ (β_ (W ⊗ a) z).hom ≫ z ◁ (β_ W a).hom =
        (β_ W (a ⊗ z)).hom ≫ (β_ a z).hom ▷ W ≫ (α_ z a W).hom := by
    simpa only [braiding_tensor_left_hom, braiding_tensor_right_hom,
      Category.assoc, Iso.inv_hom_id_assoc] using (yang_baxter W a z).symm
  have hK :
      K = (β_ W (a ⊗ z)).hom ≫ (β_ a z).hom ▷ W ≫
        (z ◁ theta) ▷ W ≫ (α_ z J W).hom := by
    calc
      _ = ((α_ W a z).inv ≫ (β_ (W ⊗ a) z).hom ≫ z ◁ (β_ W a).hom) ≫
          z ◁ (theta ⊗ₘ 𝟙 W) := by
        simp only [K, whiskerLeft_comp, Category.assoc]
      _ = ((β_ W (a ⊗ z)).hom ≫ (β_ a z).hom ▷ W ≫ (α_ z a W).hom) ≫
          z ◁ (theta ⊗ₘ 𝟙 W) :=
        congrArg (fun f => f ≫ z ◁ (theta ⊗ₘ 𝟙 W)) hStructure
      _ = _ := by
        simpa only [tensorHom_id, Category.assoc] using
          congrArg (fun f => (β_ W (a ⊗ z)).hom ≫ (β_ a z).hom ▷ W ≫ f)
            (associator_naturality_middle z theta W).symm
  change (show W ⊗ (a ⊗ z) ⟶ F.obj k from leftForwardGen d F k X) =
    (𝟙 W ⊗ₘ leftStrengthComponent d F X) ≫ evaluationGen F k X
  have hLeft :
      (show W ⊗ (a ⊗ z) ⟶ F.obj k from leftForwardGen d F k X) =
        K ≫ z ◁ c ≫ w := by
    let m : W ⊗ a ⟶ (X.2 ⟶[V] k) :=
      (β_ W a).hom ≫ (theta ⊗ₘ 𝟙 W) ≫ c
    have hData :
        (show W ⊗ (a ⊗ z) ⟶ F.obj k from leftForwardGen d F k X) =
          (α_ W a z).inv ≫ (m ⊗ₘ 𝟙 z) ≫ (β_ (X.2 ⟶[V] k) z).hom ≫ w := rfl
    have hPure :
        (α_ W a z).inv ≫ (m ⊗ₘ 𝟙 z) ≫ (β_ (X.2 ⟶[V] k) z).hom ≫ w =
          K ≫ z ◁ c ≫ w := by
      simpa only [m, K, id_tensorHom, whiskerLeft_comp, Category.assoc] using
        congrArg (fun f : (W ⊗ a) ⊗ z ⟶ F.obj k => (α_ W a z).inv ≫ f)
          (braiding_naturality_assoc m (𝟙 z) w)
    exact hData.trans hPure
  have hAction : z ◁ c ≫ w = (α_ z J W).inv ≫ (u ▷ W) ≫ v :=
    action_comp F X.2 A k
  calc
    _ = K ≫ z ◁ c ≫ w := hLeft
    _ = K ≫ (α_ z J W).inv ≫ (u ▷ W) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun f => K ≫ f) hAction
    _ = (β_ W (a ⊗ z)).hom ≫
        ((β_ a z).hom ≫ z ◁ theta ≫ u) ▷ W ≫ v := by
      rw [hK]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]
    _ = _ := by
      let s : a ⊗ z ⟶ B := (β_ a z).hom ≫ z ◁ theta ≫ u
      have hB : (β_ W (a ⊗ z)).hom ≫ s ▷ W ≫ v =
          (𝟙 W ⊗ₘ s) ≫ (β_ W B).hom ≫ v := by
        simpa only [tensorHom_id] using (braiding_naturality_assoc (𝟙 W) s v).symm
      have hData :
          (𝟙 W ⊗ₘ s) ≫ (β_ W B).hom ≫ v =
            (𝟙 W ⊗ₘ leftStrengthComponent d F X) ≫ evaluationGen F k X := rfl
      exact hB.trans hData

/-- Full strength naturality and the actual evaluation cocone balance the original kernel. -/
theorem leftForwardGen_balanced (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) :
    EnrichedDayKernel.Balanced d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k (leftForwardGen d F k) := by
  intro X Y
  let W : V := (Y.1 ⊗ Y.2) ⟶[V] k
  let W' : V := (X.1 ⊗ X.2) ⟶[V] k
  let H : V := X ⟶[V] Y
  let A : V := (𝟙_ I ⟶[V] X.1) ⊗ F.obj X.2
  let A' : V := (𝟙_ I ⟶[V] Y.1) ⊗ F.obj Y.2
  let B : V := F.obj (X.1 ⊗ X.2)
  let B' : V := F.obj (Y.1 ⊗ Y.2)
  let s : A ⟶ B := leftStrengthComponent d F X
  let s' : A' ⟶ B' := leftStrengthComponent d F Y
  let m : W ⊗ H ⟶ W' := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map (Opposite.op Y) (Opposite.op X))
  let h : A ⊗ H ⟶ A' := MonoidalClosed.uncurry
    (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map X Y)
  let h' : B ⊗ H ⟶ B' := MonoidalClosed.uncurry
    ((d.tensorEnrichedFunctor.comp V F).map X Y)
  let r : W ⊗ (H ⊗ A) ⟶ W ⊗ (H ⊗ B) := W ◁ (𝟙 H ⊗ₘ s)
  have hWeight :
      ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫ (𝟙 W' ⊗ₘ s) =
        r ≫ (α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B) := by
    have ha :
        (𝟙 W ⊗ₘ (𝟙 H ⊗ₘ s)) ≫ (α_ W H B).inv =
          (α_ W H A).inv ≫ ((𝟙 W ⊗ₘ 𝟙 H) ⊗ₘ s) :=
      associator_inv_naturality (𝟙 W) (𝟙 H) s
    have h := congrArg (fun f => f ≫ (m ⊗ₘ 𝟙 B)) ha
    simp only [Category.assoc, tensorHom_comp_tensorHom, id_tensorHom_id,
      Category.id_comp, Category.comp_id] at h
    have hR : (α_ W H A).inv ≫ (m ⊗ₘ s) =
        r ≫ (α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B) := by
      simpa only [r, id_tensorHom, Category.assoc] using h.symm
    have hFactor : (m ⊗ₘ 𝟙 A) ≫ (𝟙 W' ⊗ₘ s) = m ⊗ₘ s := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact (Category.assoc (α_ W H A).inv (m ⊗ₘ 𝟙 A) (𝟙 W' ⊗ₘ s)).trans
      ((congrArg (fun f => (α_ W H A).inv ≫ f) hFactor).trans hR)
  have hNatural : h ≫ s' = (s ⊗ₘ 𝟙 H) ≫ h' :=
    leftStrength_natural d F X Y
  have hDiagram :
      (β_ H A).hom ≫ h ≫ s' =
        (𝟙 H ⊗ₘ s) ≫ (β_ H B).hom ≫ h' := by
    have hN : (β_ H A).hom ≫ h ≫ s' = (β_ H A).hom ≫ (s ⊗ₘ 𝟙 H) ≫ h' := by
      simpa only [Category.assoc] using
        congrArg (fun f => (β_ H A).hom ≫ f) hNatural
    exact hN.trans (braiding_naturality_assoc (𝟙 H) s h').symm
  have hEvaluation :
      ((α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X =
        W ◁ ((β_ H B).hom ≫ h') ≫ evaluationGen F k Y := by
    have hM : m =
        W ◁ d.tensorMap X.1 Y.1 X.2 Y.2 ≫
          (β_ W ((X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2))).hom ≫
          eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k := by
      exact EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k X Y
    calc
      _ = ((α_ W H B).inv ≫
          ((W ◁ d.tensorMap X.1 Y.1 X.2 Y.2 ≫
            (β_ W ((X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2))).hom ≫
            eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 B)) ≫
            evaluationGen F k X :=
        congrArg (fun f : W ⊗ H ⟶ W' =>
          ((α_ W H B).inv ≫ (f ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X) hM
      _ = _ := evaluationGen_balanced d F k X Y
  change ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫ leftForwardGen d F k X =
    W ◁ ((β_ H A).hom ≫ h) ≫ leftForwardGen d F k Y
  rw [leftForwardGen_eq_strength, leftForwardGen_eq_strength]
  change ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫
      (𝟙 W' ⊗ₘ s) ≫ evaluationGen F k X =
    W ◁ ((β_ H A).hom ≫ h) ≫ (𝟙 W ⊗ₘ s') ≫ evaluationGen F k Y
  calc
    _ = r ≫ ((α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ evaluationGen F k X) hWeight
    _ = r ≫ W ◁ ((β_ H B).hom ≫ h') ≫ evaluationGen F k Y := by
      simpa only [Category.assoc] using congrArg (fun f => r ≫ f) hEvaluation
    _ = _ := by
      simpa only [r, id_tensorHom, whiskerLeft_comp, Category.assoc] using
        congrArg (fun f => W ◁ f ≫ evaluationGen F k Y) hDiagram.symm

/-- The literal first-coordinate contraction in the contravariant kernel weight. -/
private def leftCollapseBase (d : EnrichedMonoidalCategoryData V I)
    (k : I) (X : I × I) :
    ((X.1 ⊗ X.2) ⟶[V] k) ⊗ (𝟙_ I ⟶[V] X.1) ⟶ ((𝟙_ I ⊗ X.2) ⟶[V] k) :=
  ((X.1 ⊗ X.2) ⟶[V] k) ◁ leftTensorHom d X.1 X.2 ≫
    (β_ ((X.1 ⊗ X.2) ⟶[V] k)
      ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2))).hom ≫
    eComp V (𝟙_ I ⊗ X.2) (X.1 ⊗ X.2) k

/-- The first relation weight face is exactly the selected identity-inserting collapse. -/
private theorem leftRelationOne_weightFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    leftRelationOne d F k X ≫
        (α_ ((X.1 ⊗ X.2) ⟶[V] k)
          ((𝟙_ I ⟶[V] X.1) ⊗ (X.2 ⟶[V] X.2))
          ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj X.2)).inv ≫
        (MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op X) (Opposite.op (𝟙_ I, X.2))) ⊗ₘ
          𝟙 ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj X.2)) =
      (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv ≫
        (leftCollapseBase d k X ⊗ₘ
          ((λ_ (F.obj X.2)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj X.2)))) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let H : V := 𝟙_ I ⟶[V] X.1
  let J : V := X.2 ⟶[V] X.2
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let A : V := F.obj X.2
  let W' : V := (𝟙_ I ⊗ X.2) ⟶[V] k
  let p : H ⟶ H ⊗ J := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V X.2)
  let q : A ⟶ U ⊗ A := (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let m : W ⊗ (H ⊗ J) ⟶ W' := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
      (Opposite.op X) (Opposite.op (𝟙_ I, X.2)))
  have hM : m = W ◁ d.tensorMap (𝟙_ I) X.1 X.2 X.2 ≫
      (β_ W ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2))).hom ≫
      eComp V (𝟙_ I ⊗ X.2) (X.1 ⊗ X.2) k := by
    exact EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k (𝟙_ I, X.2) X
  have hCollapse : W ◁ p ≫ m = leftCollapseBase d k X := by
    let t : H ⟶ ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2)) := leftTensorHom d X.1 X.2
    have ht : t = p ≫ d.tensorMap (𝟙_ I) X.1 X.2 X.2 := by
      exact (Category.assoc (ρ_ H).inv (𝟙 H ⊗ₘ eId V X.2)
        (d.tensorMap (𝟙_ I) X.1 X.2 X.2)).symm
    have hWh : W ◁ p ≫ W ◁ d.tensorMap (𝟙_ I) X.1 X.2 X.2 = W ◁ t :=
      (whiskerLeft_comp W p (d.tensorMap (𝟙_ I) X.1 X.2 X.2)).symm.trans
        (congrArg (fun f => W ◁ f) ht.symm)
    have hData : W ◁ t ≫
        (β_ W ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2))).hom ≫
        eComp V (𝟙_ I ⊗ X.2) (X.1 ⊗ X.2) k = leftCollapseBase d k X := rfl
    exact (congrArg (fun f : W ⊗ (H ⊗ J) ⟶ W' => W ◁ p ≫ f) hM).trans
      ((Category.assoc (W ◁ p) (W ◁ d.tensorMap (𝟙_ I) X.1 X.2 X.2)
        ((β_ W ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2))).hom ≫
          eComp V (𝟙_ I ⊗ X.2) (X.1 ⊗ X.2) k)).symm.trans
        ((congrArg (fun f => f ≫
          (β_ W ((𝟙_ I ⊗ X.2) ⟶[V] (X.1 ⊗ X.2))).hom ≫
          eComp V (𝟙_ I ⊗ X.2) (X.1 ⊗ X.2) k) hWh).trans hData))
  have hA :
      W ◁ (p ⊗ₘ q) ≫ (α_ W (H ⊗ J) (U ⊗ A)).inv =
        (α_ W H A).inv ≫ ((W ◁ p) ⊗ₘ q) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 W) p q
  change W ◁ (p ⊗ₘ q) ≫ (α_ W (H ⊗ J) (U ⊗ A)).inv ≫
      (m ⊗ₘ 𝟙 (U ⊗ A)) = (α_ W H A).inv ≫ (leftCollapseBase d k X ⊗ₘ q)
  calc
    _ = (α_ W H A).inv ≫ ((W ◁ p ≫ m) ⊗ₘ q) := by
      simpa only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id] using
        congrArg (fun f => f ≫ (m ⊗ₘ 𝟙 (U ⊗ A))) hA
    _ = _ := congrArg (fun f : W ⊗ H ⟶ W' => (α_ W H A).inv ≫ (f ⊗ₘ q)) hCollapse

/-- The first full relation face restores the actual external coefficient. -/
private theorem leftRelationOne_coeffIdentity (F : EnrichedFunctor V I V) (i j : I) :
    (((ρ_ (𝟙_ I ⟶[V] i)).inv ≫
          (𝟙 (𝟙_ I ⟶[V] i) ⊗ₘ eId V j)) ⊗ₘ
        ((λ_ (F.obj j)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj j)))) ≫
      (β_ ((𝟙_ I ⟶[V] i) ⊗ (j ⟶[V] j))
        ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj j)).hom ≫
      MonoidalClosed.uncurry
        (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
          (𝟙_ I, j) (i, j)) = 𝟙 ((𝟙_ I ⟶[V] i) ⊗ F.obj j) := by
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let H : V := 𝟙_ I ⟶[V] i
  let K : V := j ⟶[V] j
  let A : V := F.obj j
  let r : H ⟶ H ⊗ K := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V j)
  let l : A ⟶ U ⊗ A := (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let p : H ⟶ U ⊗ H := (λ_ H).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 H)
  let q : A ⟶ A ⊗ K := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V j)
  have hInsert :
      (r ⊗ₘ l) ≫ (β_ (H ⊗ K) (U ⊗ A)).hom ≫ tensorμ U A H K = p ⊗ₘ q := by
    calc
      _ = (β_ H A).hom ≫ ((l ⊗ₘ r) ≫ tensorμ U A H K) :=
        braiding_naturality_assoc r l (tensorμ U A H K)
      _ = (β_ H A).hom ≫ (β_ A H).hom ≫ (p ⊗ₘ q) := by
        dsimp only [l, r, p, q]
        rw [tensorMu_unit_exchange]
      _ = _ := by rw [SymmetricCategory.symmetry_assoc]
  have hU : p ≫ eComp V (𝟙_ I) (𝟙_ I) i = 𝟙 H := by
    simpa only [p, H, tensorHom_id, Category.assoc] using e_id_comp V (𝟙_ I) i
  have h0 := congrArg (MonoidalClosed.uncurry (A := A)) (F.map_id j)
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h0
  have hF : q ≫ MonoidalClosed.uncurry (F.map j j) = 𝟙 A := by
    simpa only [q, A, id_tensorHom, Category.assoc, Iso.inv_hom_id] using
      congrArg (fun v => (ρ_ A).inv ≫ v) h0
  have hExternal :
      (show (U ⊗ A) ⊗ (H ⊗ K) ⟶ H ⊗ A from
        MonoidalClosed.uncurry
          (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
            (𝟙_ I, j) (i, j))) =
        tensorμ U A H K ≫
          (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j)) := by
    calc
      _ = tensorμ U A H K ≫
          (MonoidalClosed.uncurry ((GradedYoneda.representable (𝟙_ I)).map (𝟙_ I) i) ⊗ₘ
            MonoidalClosed.uncurry (F.map j j)) :=
        EnrichedFunctor.externalTensor_uncurry (GradedYoneda.representable (𝟙_ I))
          F (𝟙_ I, j) (i, j)
      _ = _ := congrArg
        (fun f : U ⊗ H ⟶ H => tensorμ U A H K ≫
          (f ⊗ₘ MonoidalClosed.uncurry (F.map j j)))
        (GradedYoneda.representable_uncurry (𝟙_ I) (𝟙_ I) i)
  change (r ⊗ₘ l) ≫ (β_ (H ⊗ K) (U ⊗ A)).hom ≫
      MonoidalClosed.uncurry
        (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
          (𝟙_ I, j) (i, j)) = 𝟙 (H ⊗ A)
  calc
    _ = ((r ⊗ₘ l) ≫ (β_ (H ⊗ K) (U ⊗ A)).hom ≫ tensorμ U A H K) ≫
        (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j)) := by
      have hE := congrArg
        (fun f : (U ⊗ A) ⊗ (H ⊗ K) ⟶ H ⊗ A =>
          (r ⊗ₘ l) ≫ (β_ (H ⊗ K) (U ⊗ A)).hom ≫ f) hExternal
      have hA := (Category.assoc (r ⊗ₘ l)
        ((β_ (H ⊗ K) (U ⊗ A)).hom ≫ tensorμ U A H K)
        (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j))).trans
          (congrArg (fun f => (r ⊗ₘ l) ≫ f)
            (Category.assoc (β_ (H ⊗ K) (U ⊗ A)).hom (tensorμ U A H K)
              (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j))))
      exact hE.trans hA.symm
    _ = (p ⊗ₘ q) ≫
        (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j)) :=
      congrArg (fun v => v ≫
        (eComp V (𝟙_ I) (𝟙_ I) i ⊗ₘ MonoidalClosed.uncurry (F.map j j))) hInsert
    _ = (p ≫ eComp V (𝟙_ I) (𝟙_ I) i) ⊗ₘ
        (q ≫ MonoidalClosed.uncurry (F.map j j)) := tensorHom_comp_tensorHom _ _ _ _
    _ = _ := by rw [hU, hF, id_tensorHom_id]

/-- The first relation diagram face is the identity on the entire original integrand. -/
private theorem leftRelationOne_rightFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    leftRelationOne d F k X ≫
        ((X.1 ⊗ X.2) ⟶[V] k) ◁
          ((β_ ((𝟙_ I ⟶[V] X.1) ⊗ (X.2 ⟶[V] X.2))
              ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj X.2)).hom ≫
            MonoidalClosed.uncurry
              (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
                (𝟙_ I, X.2) X)) =
      𝟙 (EnrichedDayKernel.objects d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k X) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let H : V := 𝟙_ I ⟶[V] X.1
  let J : V := X.2 ⟶[V] X.2
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let A : V := F.obj X.2
  let p : H ⟶ H ⊗ J := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V X.2)
  let q : A ⟶ U ⊗ A := (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let h : (U ⊗ A) ⊗ (H ⊗ J) ⟶ H ⊗ A := MonoidalClosed.uncurry
    (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map (𝟙_ I, X.2) X)
  have hCoeff : (p ⊗ₘ q) ≫ (β_ (H ⊗ J) (U ⊗ A)).hom ≫ h = 𝟙 (H ⊗ A) :=
    leftRelationOne_coeffIdentity F X.1 X.2
  have hW := congrArg (fun f : H ⊗ A ⟶ H ⊗ A => W ◁ f) hCoeff
  change W ◁ (p ⊗ₘ q) ≫ W ◁ ((β_ (H ⊗ J) (U ⊗ A)).hom ≫ h) = 𝟙 (W ⊗ (H ⊗ A))
  simpa only [← whiskerLeft_comp, whiskerLeft_id] using hW

/-- The second relation's weight contraction is the actual whole-hom unitor identity. -/
private theorem leftRelationTwo_weightBase (d : EnrichedMonoidalCategoryData V I) (j k : I) :
    (λ_ ((𝟙_ I ⊗ j) ⟶[V] k)).inv ≫
        (eHomEquiv V (λ_ k).hom ⊗ₘ
          ((λ_ ((𝟙_ I ⊗ j) ⟶[V] k)).inv ≫
            (eId V (𝟙_ I) ⊗ₘ eHomWhiskerRight V (λ_ j).inv k))) ≫
        MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (𝟙_ I, k)) (Opposite.op (𝟙_ I, j))) =
      𝟙 ((𝟙_ I ⊗ j) ⟶[V] k) := by
  let W : V := (𝟙_ I ⊗ j) ⟶[V] k
  let m : W ⟶ (j ⟶[V] k) := eHomWhiskerRight V (λ_ j).inv k
  have hMap :
      ((λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ m)) ≫
          d.tensorMap (𝟙_ I) (𝟙_ I) j k =
        m ≫ leftUnitTensorMap d j k := by
    simpa only [leftUnitTensorMap, tensorHom_id, Category.assoc] using
      leftUnitor_inv_comp_tensorHom_assoc (eId V (𝟙_ I)) m
        (d.tensorMap (𝟙_ I) (𝟙_ I) j k)
  have hWeight :
      (show ((𝟙_ I ⊗ k) ⟶[V] k) ⊗ ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] k)) ⟶ W from
        MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (𝟙_ I, k)) (Opposite.op (𝟙_ I, j)))) =
        ((𝟙_ I ⊗ k) ⟶[V] k) ◁ d.tensorMap (𝟙_ I) (𝟙_ I) j k ≫
          (β_ ((𝟙_ I ⊗ k) ⟶[V] k) ((𝟙_ I ⊗ j) ⟶[V] (𝟙_ I ⊗ k))).hom ≫
          eComp V (𝟙_ I ⊗ j) (𝟙_ I ⊗ k) k :=
    EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k (𝟙_ I, j) (𝟙_ I, k)
  change (λ_ W).inv ≫
      (eHomEquiv V (λ_ k).hom ⊗ₘ ((λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ m))) ≫
      (show ((𝟙_ I ⊗ k) ⟶[V] k) ⊗ ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] k)) ⟶ W from
        MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (𝟙_ I, k)) (Opposite.op (𝟙_ I, j)))) = 𝟙 W
  rw [hWeight, tensorHom_comp_whiskerLeft_assoc]
  rw [hMap, braiding_naturality_assoc, leftUnitor_inv_braiding_assoc,
    rightUnitor_inv_comp_tensorHom_assoc]
  change (m ≫ leftUnitTensorMap d j k) ≫
      eHomWhiskerLeft V (𝟙_ I ⊗ j) (λ_ k).hom = 𝟙 W
  rw [Category.assoc, leftUnitTensorMap_natural]
  simp only [m, ← eHomWhiskerRight_comp, Iso.hom_inv_id, eHomWhiskerRight_id]
  rfl

omit [MonoidalClosed V] in
/-- Two literal left unit insertions commute with the actual tensor interchange. -/
private theorem tensorMu_left_insert {A B R S : V}
    (e : 𝟙_ V ⟶ R) (f : 𝟙_ V ⟶ S) :
    (((λ_ A).inv ≫ (e ⊗ₘ 𝟙 A)) ⊗ₘ
        ((λ_ B).inv ≫ (f ⊗ₘ 𝟙 B))) ≫ tensorμ R A S B =
      (λ_ (A ⊗ B)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ f)) ⊗ₘ 𝟙 (A ⊗ B)) := by
  have hUnit :
      ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ tensorμ (𝟙_ V) A (𝟙_ V) B =
        (λ_ (A ⊗ B)).inv ≫ (λ_ (𝟙_ V)).inv ▷ (A ⊗ B) := by
    apply (cancel_mono ((λ_ (𝟙_ V)).hom ▷ (A ⊗ B) ≫ (λ_ (A ⊗ B)).hom)).1
    calc
      _ = ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ ((λ_ A).hom ⊗ₘ (λ_ B).hom) := by
        simpa only [Category.assoc] using
          congrArg (fun f => ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ f)
            (leftUnitor_monoidal A B).symm
      _ = 𝟙 (A ⊗ B) := by
        rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]
      _ = _ := by
        simp only [Category.assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id]
  calc
    _ = ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫
        ((e ⊗ₘ 𝟙 A) ⊗ₘ (f ⊗ₘ 𝟙 B)) ≫ tensorμ R A S B := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ tensorμ R A S B)
          (tensorHom_comp_tensorHom (λ_ A).inv (λ_ B).inv
            (e ⊗ₘ 𝟙 A) (f ⊗ₘ 𝟙 B)).symm
    _ = ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ tensorμ (𝟙_ V) A (𝟙_ V) B ≫
        ((e ⊗ₘ f) ⊗ₘ 𝟙 (A ⊗ B)) := by
      simpa only [id_tensorHom_id] using
        congrArg (fun q => ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ q)
          (tensorμ_natural e (𝟙 A) f (𝟙 B))
    _ = (λ_ (A ⊗ B)).inv ≫ (λ_ (𝟙_ V)).inv ▷ (A ⊗ B) ≫
        ((e ⊗ₘ f) ⊗ₘ 𝟙 (A ⊗ B)) := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ ((e ⊗ₘ f) ⊗ₘ 𝟙 (A ⊗ B))) hUnit
    _ = _ := by rw [whiskerRight_comp_tensorHom]

/-- The second full relation coefficient inserts one actual unit identity after evaluation. -/
private theorem leftRelationTwo_coeffFace (F : EnrichedFunctor V I V)
    (j k : I) {W : V} (m : W ⟶ (j ⟶[V] k)) :
    (((λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ m)) ⊗ₘ
        ((λ_ (F.obj j)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj j)))) ≫
      (β_ ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] k))
        ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj j)).hom ≫
      MonoidalClosed.uncurry
        (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
          (𝟙_ I, j) (𝟙_ I, k)) =
      (λ_ (W ⊗ F.obj j)).inv ≫
        (eId V (𝟙_ I) ⊗ₘ
          ((β_ W (F.obj j)).hom ≫ F.obj j ◁ m ≫
            MonoidalClosed.uncurry (F.map j k))) := by
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let A : V := F.obj j
  let H : V := j ⟶[V] k
  let e : 𝟙_ V ⟶ U := eId V (𝟙_ I)
  let l : A ⟶ U ⊗ A := (λ_ A).inv ≫ (e ⊗ₘ 𝟙 A)
  let lW : W ⟶ U ⊗ W := (λ_ W).inv ≫ (e ⊗ₘ 𝟙 W)
  let p : W ⟶ U ⊗ H := (λ_ W).inv ≫ (e ⊗ₘ m)
  let c : U ⊗ U ⟶ U := eComp V (𝟙_ I) (𝟙_ I) (𝟙_ I)
  let q : A ⊗ H ⟶ F.obj k := MonoidalClosed.uncurry (F.map j k)
  let delta : 𝟙_ V ⟶ U ⊗ U := (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ e)
  have hId : delta ≫ c = e := by
    simpa only [delta, e, c, eHomEquiv_id, Category.id_comp, Category.assoc] using
      (eHomEquiv_comp V (𝟙 (𝟙_ I)) (𝟙 (𝟙_ I))).symm
  have hp : p = lW ≫ (𝟙 U ⊗ₘ m) := by
    simp only [p, lW, tensorHom_comp_tensorHom, Category.assoc,
      Category.id_comp, Category.comp_id]
  have hMu :
      (𝟙 (U ⊗ A) ⊗ₘ (𝟙 U ⊗ₘ m)) ≫ tensorμ U A U H =
        tensorμ U A U W ≫ (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m)) := by
    simpa only [id_tensorHom_id] using tensorμ_natural (𝟙 U) (𝟙 A) (𝟙 U) m
  have hSplit :
      l ⊗ₘ p = (l ⊗ₘ lW) ≫ (𝟙 (U ⊗ A) ⊗ₘ (𝟙 U ⊗ₘ m)) := by
    calc
      _ = l ⊗ₘ (lW ≫ (𝟙 U ⊗ₘ m)) := congrArg (fun f => l ⊗ₘ f) hp
      _ = _ := by
        simpa only [Category.comp_id] using
          (tensorHom_comp_tensorHom l lW (𝟙 (U ⊗ A)) (𝟙 U ⊗ₘ m)).symm
  have hPad :
      (l ⊗ₘ lW) ≫ tensorμ U A U W =
        (λ_ (A ⊗ W)).inv ≫ (delta ⊗ₘ 𝟙 (A ⊗ W)) := tensorMu_left_insert e e
  have hTail :
      (delta ⊗ₘ 𝟙 (A ⊗ W)) ≫
          (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m)) ≫ (c ⊗ₘ q) =
        (delta ≫ c) ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q) := by
    calc
      _ = ((delta ⊗ₘ 𝟙 (A ⊗ W)) ≫
          (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m))) ≫ (c ⊗ₘ q) :=
        (Category.assoc _ _ _).symm
      _ = (delta ⊗ₘ (𝟙 A ⊗ₘ m)) ≫ (c ⊗ₘ q) := by
        rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      _ = _ := tensorHom_comp_tensorHom _ _ _ _
  have hInsert :
      (l ⊗ₘ p) ≫ tensorμ U A U H ≫ (c ⊗ₘ q) =
        (λ_ (A ⊗ W)).inv ≫ (e ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q)) := by
    calc
      _ = (l ⊗ₘ lW) ≫ (𝟙 (U ⊗ A) ⊗ₘ (𝟙 U ⊗ₘ m)) ≫
          tensorμ U A U H ≫ (c ⊗ₘ q) := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ tensorμ U A U H ≫ (c ⊗ₘ q)) hSplit
      _ = (l ⊗ₘ lW) ≫ tensorμ U A U W ≫
          (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m)) ≫ (c ⊗ₘ q) := by
        simpa only [Category.assoc] using
          congrArg (fun f => (l ⊗ₘ lW) ≫ f ≫ (c ⊗ₘ q)) hMu
      _ = (λ_ (A ⊗ W)).inv ≫ (delta ⊗ₘ 𝟙 (A ⊗ W)) ≫
          (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m)) ≫ (c ⊗ₘ q) := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫
            (𝟙 (U ⊗ U) ⊗ₘ (𝟙 A ⊗ₘ m)) ≫ (c ⊗ₘ q)) hPad
      _ = (λ_ (A ⊗ W)).inv ≫ ((delta ≫ c) ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q)) := by
        simpa only [Category.assoc] using
          congrArg (fun f => (λ_ (A ⊗ W)).inv ≫ f) hTail
      _ = _ := by rw [hId]
  have hExternal :
      (show (U ⊗ A) ⊗ (U ⊗ H) ⟶ U ⊗ F.obj k from
        MonoidalClosed.uncurry
          (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
            (𝟙_ I, j) (𝟙_ I, k))) = tensorμ U A U H ≫ (c ⊗ₘ q) := by
    calc
      _ = tensorμ U A U H ≫
          (MonoidalClosed.uncurry ((GradedYoneda.representable (𝟙_ I)).map (𝟙_ I) (𝟙_ I)) ⊗ₘ q) :=
        EnrichedFunctor.externalTensor_uncurry (GradedYoneda.representable (𝟙_ I))
          F (𝟙_ I, j) (𝟙_ I, k)
      _ = _ := congrArg (fun f : U ⊗ U ⟶ U => tensorμ U A U H ≫ (f ⊗ₘ q))
        (GradedYoneda.representable_uncurry (𝟙_ I) (𝟙_ I) (𝟙_ I))
  change (p ⊗ₘ l) ≫ (β_ (U ⊗ H) (U ⊗ A)).hom ≫
      (show (U ⊗ A) ⊗ (U ⊗ H) ⟶ U ⊗ F.obj k from
        MonoidalClosed.uncurry
          (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
            (𝟙_ I, j) (𝟙_ I, k))) =
    (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ ((β_ W A).hom ≫ A ◁ m ≫ q))
  calc
    _ = (p ⊗ₘ l) ≫ (β_ (U ⊗ H) (U ⊗ A)).hom ≫ tensorμ U A U H ≫ (c ⊗ₘ q) := by
      simpa only [Category.assoc] using
        congrArg (fun f : (U ⊗ A) ⊗ (U ⊗ H) ⟶ U ⊗ F.obj k =>
          (p ⊗ₘ l) ≫ (β_ (U ⊗ H) (U ⊗ A)).hom ≫ f) hExternal
    _ = (β_ W A).hom ≫ (l ⊗ₘ p) ≫ tensorμ U A U H ≫ (c ⊗ₘ q) :=
      braiding_naturality_assoc p l (tensorμ U A U H ≫ (c ⊗ₘ q))
    _ = (β_ W A).hom ≫ (λ_ (A ⊗ W)).inv ≫
        (e ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q)) := by
      simpa only [Category.assoc] using congrArg (fun f => (β_ W A).hom ≫ f) hInsert
    _ = (λ_ (W ⊗ A)).inv ≫ (𝟙_ V) ◁ (β_ W A).hom ≫
        (e ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q)) := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ (e ⊗ₘ ((𝟙 A ⊗ₘ m) ≫ q)))
          (leftUnitor_inv_naturality (β_ W A).hom)
    _ = _ := by
      rw [whiskerLeft_comp_tensorHom]
      rw [id_tensorHom]

/-- The second relation's full weight face is the original identity insertion. -/
private theorem leftRelationTwo_weightFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (j k : I) :
    leftRelationTwo d F k j ≫
        (α_ ((𝟙_ I ⊗ k) ⟶[V] k)
          ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] k))
          ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj j)).inv ≫
        (MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (𝟙_ I, k)) (Opposite.op (𝟙_ I, j))) ⊗ₘ
          𝟙 ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj j)) =
      (𝟙 ((𝟙_ I ⊗ j) ⟶[V] k) ⊗ₘ
        ((λ_ (F.obj j)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj j)))) := by
  let W : V := (𝟙_ I ⊗ j) ⟶[V] k
  let A : V := F.obj j
  let E : V := (𝟙_ I ⊗ k) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let H : V := j ⟶[V] k
  let e : 𝟙_ V ⟶ E := eHomEquiv V (λ_ k).hom
  let p : W ⟶ U ⊗ H :=
    (λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ eHomWhiskerRight V (λ_ j).inv k)
  let q : A ⟶ U ⊗ A := (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let m : E ⊗ (U ⊗ H) ⟶ W := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
      (Opposite.op (𝟙_ I, k)) (Opposite.op (𝟙_ I, j)))
  have hUnit : (λ_ (W ⊗ A)).inv ≫ (α_ (𝟙_ V) W A).inv = (λ_ W).inv ▷ A :=
    (leftUnitor_inv_whiskerRight W A).symm
  have hPad :
      (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) ≫ (α_ E (U ⊗ H) (U ⊗ A)).inv =
        ((λ_ W).inv ≫ (e ⊗ₘ p)) ⊗ₘ q := by
    calc
      _ = ((λ_ (W ⊗ A)).inv ≫ (α_ (𝟙_ V) W A).inv) ≫ ((e ⊗ₘ p) ⊗ₘ q) := by
        simpa only [Category.assoc] using
          congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ f)
            (associator_inv_naturality e p q)
      _ = (λ_ W).inv ▷ A ≫ ((e ⊗ₘ p) ⊗ₘ q) :=
        congrArg (fun f => f ≫ ((e ⊗ₘ p) ⊗ₘ q)) hUnit
      _ = _ := whiskerRight_comp_tensorHom _ _ _
  have hBase : (λ_ W).inv ≫ (e ⊗ₘ p) ≫ m = 𝟙 W := leftRelationTwo_weightBase d j k
  have hStep :
      (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) ≫
          (α_ E (U ⊗ H) (U ⊗ A)).inv ≫ (m ⊗ₘ 𝟙 (U ⊗ A)) =
        ((λ_ W).inv ≫ (e ⊗ₘ p) ≫ m) ⊗ₘ q := by
    simpa only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id] using
      congrArg (fun f => f ≫ (m ⊗ₘ 𝟙 (U ⊗ A))) hPad
  have hRel : leftRelationTwo d F k j =
      (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) := rfl
  have hTransport := congrArg
    (fun f : W ⊗ A ⟶ E ⊗ ((U ⊗ H) ⊗ (U ⊗ A)) =>
      f ≫ (α_ E (U ⊗ H) (U ⊗ A)).inv ≫ (m ⊗ₘ 𝟙 (U ⊗ A))) hRel
  exact hTransport.trans
    ((Category.assoc (λ_ (W ⊗ A)).inv (e ⊗ₘ (p ⊗ₘ q))
      ((α_ E (U ⊗ H) (U ⊗ A)).inv ≫ (m ⊗ₘ 𝟙 (U ⊗ A)))).trans
        (hStep.trans (congrArg (fun f : W ⟶ W => f ⊗ₘ q) hBase)))

/-- The literal contraction in the second relation, on its complete hom object. -/
private def leftContraction (F : EnrichedFunctor V I V) (j k : I) :
    ((𝟙_ I ⊗ j) ⟶[V] k) ⊗ F.obj j ⟶ F.obj k :=
  (β_ ((𝟙_ I ⊗ j) ⟶[V] k) (F.obj j)).hom ≫
    F.obj j ◁ eHomWhiskerRight V (λ_ j).inv k ≫
    MonoidalClosed.uncurry (F.map j k)

/-- The second relation's diagram face is the actual contraction followed by unit insertion. -/
private theorem leftRelationTwo_diagramFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (j k : I) :
    leftRelationTwo d F k j ≫
        ((𝟙_ I ⊗ k) ⟶[V] k) ◁
          ((β_ ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ (j ⟶[V] k))
              ((𝟙_ I ⟶[V] 𝟙_ I) ⊗ F.obj j)).hom ≫
            MonoidalClosed.uncurry
              (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map
                (𝟙_ I, j) (𝟙_ I, k))) =
      leftContraction F j k ≫ (λ_ (F.obj k)).inv ≫
        (eHomEquiv V (λ_ k).hom ⊗ₘ
          ((λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k)))) := by
  let W : V := (𝟙_ I ⊗ j) ⟶[V] k
  let A : V := F.obj j
  let E : V := (𝟙_ I ⊗ k) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let H : V := j ⟶[V] k
  let e : 𝟙_ V ⟶ E := eHomEquiv V (λ_ k).hom
  let m : W ⟶ H := eHomWhiskerRight V (λ_ j).inv k
  let p : W ⟶ U ⊗ H := (λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ m)
  let q : A ⟶ U ⊗ A := (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let a : (U ⊗ A) ⊗ (U ⊗ H) ⟶ U ⊗ F.obj k := MonoidalClosed.uncurry
    (((GradedYoneda.representable (𝟙_ I)).externalTensor F).map (𝟙_ I, j) (𝟙_ I, k))
  let c : W ⊗ A ⟶ F.obj k := leftContraction F j k
  let q' : F.obj k ⟶ U ⊗ F.obj k :=
    (λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k))
  have hCoeff : (p ⊗ₘ q) ≫ (β_ (U ⊗ H) (U ⊗ A)).hom ≫ a =
      (λ_ (W ⊗ A)).inv ≫ (eId V (𝟙_ I) ⊗ₘ c) :=
    leftRelationTwo_coeffFace F j k m
  have hInner : (λ_ (W ⊗ A)).inv ≫ (eId V (𝟙_ I) ⊗ₘ c) = c ≫ q' := by
    simpa only [q', tensorHom_id] using leftUnitor_inv_comp_tensorHom (eId V (𝟙_ I)) c
  have hOuter : (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ c) =
      c ≫ (λ_ (F.obj k)).inv ≫ (e ⊗ₘ 𝟙 (F.obj k)) := by
    simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom e c
  have hWord :
      (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) ≫
          E ◁ ((β_ (U ⊗ H) (U ⊗ A)).hom ≫ a) =
        c ≫ (λ_ (F.obj k)).inv ≫ (e ⊗ₘ q') := by
    calc
      _ = (λ_ (W ⊗ A)).inv ≫
          (e ⊗ₘ ((p ⊗ₘ q) ≫ (β_ (U ⊗ H) (U ⊗ A)).hom ≫ a)) := by
        rw [tensorHom_comp_whiskerLeft]
      _ = (λ_ (W ⊗ A)).inv ≫
          (e ⊗ₘ ((λ_ (W ⊗ A)).inv ≫ (eId V (𝟙_ I) ⊗ₘ c))) :=
        congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ f)) hCoeff
      _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (c ≫ q')) :=
        congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ f)) hInner
      _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ c) ≫ E ◁ q' := by
        rw [tensorHom_comp_whiskerLeft]
      _ = c ≫ (λ_ (F.obj k)).inv ≫ (e ⊗ₘ 𝟙 (F.obj k)) ≫ E ◁ q' := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ E ◁ q') hOuter
      _ = _ := by rw [tensorHom_comp_whiskerLeft, Category.id_comp]
  have hRel : leftRelationTwo d F k j =
      (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) := rfl
  have hTransport := congrArg
    (fun f : W ⊗ A ⟶ E ⊗ ((U ⊗ H) ⊗ (U ⊗ A)) =>
      f ≫ E ◁ ((β_ (U ⊗ H) (U ⊗ A)).hom ≫ a)) hRel
  exact hTransport.trans
    ((Category.assoc (λ_ (W ⊗ A)).inv (e ⊗ₘ (p ⊗ₘ q))
      (E ◁ ((β_ (U ⊗ H) (U ⊗ A)).hom ≫ a))).trans hWord)

/-- The two complete index relations identify the original forward contraction. -/
private theorem leftForwardGen_eq_contraction (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    leftForwardGen d F k X =
      (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv ≫
        (leftCollapseBase d k X ⊗ₘ 𝟙 (F.obj X.2)) ≫ leftContraction F X.2 k := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.1
  let A : V := F.obj X.2
  let m : ((𝟙_ I ⊗ X.2) ⟶[V] k) ⟶ (X.2 ⟶[V] k) :=
    eHomWhiskerRight V (λ_ X.2).inv k
  have hBase :
      leftCollapseBase d k X ≫ m =
        (β_ W U).hom ≫ (leftUnitHom d X.1 X.2 ⊗ₘ 𝟙 W) ≫
          eComp V X.2 (X.1 ⊗ X.2) k := by
    dsimp only [m]
    unfold leftCollapseBase
    simp only [Category.assoc]
    rw [eComp_eHomWhiskerRight, ← id_tensorHom, braiding_naturality_assoc]
    rw [tensorHom_comp_whiskerRight_assoc]
    rfl
  have hSwap :
      (β_ ((𝟙_ I ⊗ X.2) ⟶[V] k) A).hom ≫ (𝟙 A ⊗ₘ m) =
        (m ⊗ₘ 𝟙 A) ≫ (β_ (X.2 ⟶[V] k) A).hom :=
    (braiding_naturality m (𝟙 A)).symm
  calc
    _ = (α_ W U A).inv ≫ ((leftCollapseBase d k X ≫ m) ⊗ₘ 𝟙 A) ≫
        (β_ (X.2 ⟶[V] k) A).hom ≫ MonoidalClosed.uncurry (F.map X.2 k) := by
      rw [hBase]
      rfl
    _ = _ := by
      simpa only [leftContraction, W, U, A, id_tensorHom, Category.assoc,
        tensorHom_comp_tensorHom_assoc, Category.comp_id] using
        congrArg (fun f => (α_ W U A).inv ≫ (leftCollapseBase d k X ⊗ₘ 𝟙 A) ≫
          f ≫ MonoidalClosed.uncurry (F.map X.2 k)) hSwap.symm

/-- The actual left component descends the proven full-hom balanced family. -/
def leftComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k)] :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k ⟶ F.obj k :=
  EnrichedDayKernel.desc d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k
    (leftForwardGen d F k) (leftForwardGen_balanced d F k)

/-- Every integrand generator has precisely the original left unitor formula. -/
@[reassoc]
theorem gen_leftComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k)] (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k X ≫ leftComponent d F k =
      leftForwardGen d F k X :=
  EnrichedDayKernel.gen_desc d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k _ (leftForwardGen_balanced d F k) X

omit [SymmetricCategory V] [MonoidalClosed V] in
/-- The two actual point insertions have the selected associator normalization. -/
private theorem leftDoubleInsert_assoc {A B X : V}
    (e : 𝟙_ V ⟶ A) (f : 𝟙_ V ⟶ B) :
    (λ_ X).inv ≫ (e ⊗ₘ ((λ_ X).inv ≫ (f ⊗ₘ 𝟙 X))) ≫
        (α_ A B X).inv =
      (λ_ X).inv ≫ (((λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ f)) ⊗ₘ 𝟙 X) := by
  have hUnit :
      (λ_ X).inv ≫ (𝟙_ V) ◁ (λ_ X).inv ≫ (α_ (𝟙_ V) (𝟙_ V) X).inv =
        (λ_ X).inv ≫ (λ_ (𝟙_ V)).inv ▷ X := by
    monoidal
  calc
    _ = (λ_ X).inv ≫ (𝟙_ V) ◁ (λ_ X).inv ≫
        (e ⊗ₘ (f ⊗ₘ 𝟙 X)) ≫ (α_ A B X).inv := by
      simpa only [Category.assoc] using
        congrArg (fun q => (λ_ X).inv ≫ q ≫ (α_ A B X).inv)
          (whiskerLeft_comp_tensorHom e (λ_ X).inv (f ⊗ₘ 𝟙 X)).symm
    _ = (λ_ X).inv ≫ (𝟙_ V) ◁ (λ_ X).inv ≫
        (α_ (𝟙_ V) (𝟙_ V) X).inv ≫ ((e ⊗ₘ f) ⊗ₘ 𝟙 X) := by
      simpa only [Category.assoc] using
        congrArg (fun q => (λ_ X).inv ≫ (𝟙_ V) ◁ (λ_ X).inv ≫ q)
          (associator_inv_naturality e f (𝟙 X))
    _ = (λ_ X).inv ≫ (λ_ (𝟙_ V)).inv ▷ X ≫ ((e ⊗ₘ f) ⊗ₘ 𝟙 X) := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ ((e ⊗ₘ f) ⊗ₘ 𝟙 X)) hUnit
    _ = _ := by rw [whiskerRight_comp_tensorHom]

omit [MonoidalClosed V] in
/-- Contracting the actual unitor point and unit identity gives the actual output identity. -/
private theorem leftUnitPoint_contraction (d : EnrichedMonoidalCategoryData V I) (k : I) :
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ k).hom ⊗ₘ eId V (𝟙_ I)) ≫
      (β_ ((𝟙_ I ⊗ k) ⟶[V] k) (𝟙_ I ⟶[V] 𝟙_ I)).hom ≫
      (leftUnitHom d (𝟙_ I) k ⊗ₘ 𝟙 ((𝟙_ I ⊗ k) ⟶[V] k)) ≫
      eComp V k (𝟙_ I ⊗ k) k = eId V k := by
  rw [braiding_naturality_assoc, leftUnitor_inv_braiding_assoc]
  rw [tensorHom_comp_tensorHom_assoc, leftUnitHom_id]
  simp only [Category.comp_id]
  rw [← unitors_inv_equal, ← eHomEquiv_comp, Iso.inv_hom_id, eHomEquiv_id]

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The output hom action commutes with an arbitrary map of the actual coefficient. -/
private theorem outputAction_coefficient (x k k' : I) {A B : V} (s : A ⟶ B) :
    Output.outputAction x k k' A ≫ (𝟙 (x ⟶[V] k') ⊗ₘ s) =
      ((k ⟶[V] k') ◁ (𝟙 (x ⟶[V] k) ⊗ₘ s)) ≫ Output.outputAction x k k' B := by
  let R : V := k ⟶[V] k'
  let H : V := x ⟶[V] k
  let H' : V := x ⟶[V] k'
  let b : R ⊗ H ⟶ H ⊗ R := (β_ R H).hom
  let c : H ⊗ R ⟶ H' := eComp V x k k'
  have hA :
      R ◁ (𝟙 H ⊗ₘ s) ≫ (α_ R H B).inv =
        (α_ R H A).inv ≫ (𝟙 (R ⊗ H) ⊗ₘ s) := by
    simpa only [id_tensorHom] using associator_inv_naturality_right R H s
  have hTensor :
      (𝟙 (R ⊗ H) ⊗ₘ s) ≫ (b ⊗ₘ 𝟙 B) ≫ (c ⊗ₘ 𝟙 B) =
        (b ⊗ₘ 𝟙 A) ≫ (c ⊗ₘ 𝟙 A) ≫ (𝟙 H' ⊗ₘ s) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  unfold Output.outputAction
  change ((α_ R H A).inv ≫ (b ⊗ₘ 𝟙 A) ≫ (c ⊗ₘ 𝟙 A)) ≫ (𝟙 H' ⊗ₘ s) =
    R ◁ (𝟙 H ⊗ₘ s) ≫ (α_ R H B).inv ≫ (b ⊗ₘ 𝟙 B) ≫ (c ⊗ₘ 𝟙 B)
  calc
    _ = (α_ R H A).inv ≫ (𝟙 (R ⊗ H) ⊗ₘ s) ≫ (b ⊗ₘ 𝟙 B) ≫ (c ⊗ₘ 𝟙 B) := by
      simpa only [Category.assoc] using
        congrArg (fun f => (α_ R H A).inv ≫ f) hTensor.symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ (b ⊗ₘ 𝟙 B) ≫ (c ⊗ₘ 𝟙 B)) hA.symm

/-- Evaluation retains naturality on the entire output hom. -/
private theorem evaluationGen_output_natural (F : EnrichedFunctor V I V)
    (k k' : I) (X : I × I) :
    Output.outputAction (X.1 ⊗ X.2) k k' (F.obj (X.1 ⊗ X.2)) ≫
        evaluationGen F k' X =
      (k ⟶[V] k') ◁ evaluationGen F k X ≫
        (β_ (k ⟶[V] k') (F.obj k)).hom ≫ MonoidalClosed.uncurry (F.map k k') := by
  let x : I := X.1 ⊗ X.2
  let R : V := k ⟶[V] k'
  let H : V := x ⟶[V] k
  let A : V := F.obj x
  let c : H ⊗ R ⟶ (x ⟶[V] k') := eComp V x k k'
  let u : A ⊗ H ⟶ F.obj k := MonoidalClosed.uncurry (F.map x k)
  let v : F.obj k ⊗ R ⟶ F.obj k' := MonoidalClosed.uncurry (F.map k k')
  let w : A ⊗ (x ⟶[V] k') ⟶ F.obj k' := MonoidalClosed.uncurry (F.map x k')
  let K : R ⊗ (H ⊗ A) ⟶ A ⊗ (H ⊗ R) :=
    (α_ R H A).inv ≫ (β_ (R ⊗ H) A).hom ≫ A ◁ (β_ R H).hom
  have hStructure :
      K = R ◁ (β_ H A).hom ≫ (β_ R (A ⊗ H)).hom ≫ (α_ A H R).hom := by
    calc
      _ = (β_ R (H ⊗ A)).hom ≫ (β_ H A).hom ▷ R ≫ (α_ A H R).hom := by
        simpa only [K, braiding_tensor_left_hom, braiding_tensor_right_hom,
          Category.assoc, Iso.inv_hom_id_assoc] using (yang_baxter R H A).symm
      _ = _ := by
        simpa only [id_tensorHom, tensorHom_id, Category.assoc] using
          (braiding_naturality_assoc (𝟙 R) (β_ H A).hom (α_ A H R).hom).symm
  have hLeft :
      Output.outputAction x k k' A ≫ evaluationGen F k' X = K ≫ A ◁ c ≫ w := by
    have h := congrArg (fun f => (α_ R H A).inv ≫ f)
      (braiding_naturality_assoc ((β_ R H).hom ≫ c) (𝟙 A) w)
    simpa only [Output.outputAction, evaluationGen, K, x, R, H, A, c, w,
      tensorHom_comp_tensorHom_assoc, Category.comp_id, id_tensorHom,
      whiskerLeft_comp, Category.assoc] using h
  have hAction : A ◁ c ≫ w = (α_ A H R).inv ≫ (u ▷ R) ≫ v :=
    action_comp F x k k'
  calc
    _ = K ≫ A ◁ c ≫ w := hLeft
    _ = K ≫ (α_ A H R).inv ≫ (u ▷ R) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun f => K ≫ f) hAction
    _ = R ◁ (β_ H A).hom ≫ (β_ R (A ⊗ H)).hom ≫ (u ▷ R) ≫ v := by
      rw [hStructure]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      simpa only [evaluationGen, R, H, A, x, u, v, id_tensorHom, tensorHom_id,
        whiskerLeft_comp, Category.assoc] using
        congrArg (fun f => R ◁ (β_ H A).hom ≫ f)
          (braiding_naturality_assoc (𝟙 R) u v).symm

/-- The full left forward family intertwines the actual output hom action. -/
private theorem leftForwardGen_output_natural (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k k' : I) (X : I × I) :
    Output.outputAction (X.1 ⊗ X.2) k k'
        ((𝟙_ I ⟶[V] X.1) ⊗ F.obj X.2) ≫ leftForwardGen d F k' X =
      (k ⟶[V] k') ◁ leftForwardGen d F k X ≫
        (β_ (k ⟶[V] k') (F.obj k)).hom ≫ MonoidalClosed.uncurry (F.map k k') := by
  let R : V := k ⟶[V] k'
  let H : V := (X.1 ⊗ X.2) ⟶[V] k
  let H' : V := (X.1 ⊗ X.2) ⟶[V] k'
  let A : V := (𝟙_ I ⟶[V] X.1) ⊗ F.obj X.2
  let B : V := F.obj (X.1 ⊗ X.2)
  let s : A ⟶ B := leftStrengthComponent d F X
  let b : R ⊗ F.obj k ⟶ F.obj k ⊗ R := (β_ R (F.obj k)).hom
  let a : F.obj k ⊗ R ⟶ F.obj k' := MonoidalClosed.uncurry (F.map k k')
  have hX : (show H ⊗ A ⟶ F.obj k from leftForwardGen d F k X) =
      (𝟙 H ⊗ₘ s) ≫ evaluationGen F k X := leftForwardGen_eq_strength d F k X
  have hX' : (show H' ⊗ A ⟶ F.obj k' from leftForwardGen d F k' X) =
      (𝟙 H' ⊗ₘ s) ≫ evaluationGen F k' X := leftForwardGen_eq_strength d F k' X
  change (show R ⊗ (H ⊗ A) ⟶ F.obj k' from
      Output.outputAction (X.1 ⊗ X.2) k k' A ≫ leftForwardGen d F k' X) =
    (show R ⊗ (H ⊗ A) ⟶ F.obj k' from R ◁ leftForwardGen d F k X ≫ b ≫ a)
  calc
    _ = Output.outputAction (X.1 ⊗ X.2) k k' A ≫
        (𝟙 H' ⊗ₘ s) ≫ evaluationGen F k' X :=
      congrArg (fun f : H' ⊗ A ⟶ F.obj k' =>
        Output.outputAction (X.1 ⊗ X.2) k k' A ≫ f) hX'
    _ = R ◁ (𝟙 H ⊗ₘ s) ≫ Output.outputAction (X.1 ⊗ X.2) k k' B ≫
        evaluationGen F k' X := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ evaluationGen F k' X)
          (outputAction_coefficient (X.1 ⊗ X.2) k k' s)
    _ = R ◁ (𝟙 H ⊗ₘ s) ≫ R ◁ evaluationGen F k X ≫ b ≫ a :=
      congrArg (fun f => R ◁ (𝟙 H ⊗ₘ s) ≫ f)
        (evaluationGen_output_natural F k k' X)
    _ = R ◁ ((𝟙 H ⊗ₘ s) ≫ evaluationGen F k X) ≫ b ≫ a := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ b ≫ a)
          (whiskerLeft_comp R (𝟙 H ⊗ₘ s) (evaluationGen F k X)).symm
    _ = _ := congrArg (fun f : H ⊗ A ⟶ F.obj k => R ◁ f ≫ b ≫ a) hX.symm

variable (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

/-- The first full kernel relation reduces every generator to the chosen first index unit. -/
private theorem leftGen_first_reduction (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k X =
      (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv ≫
        (leftCollapseBase d k X ⊗ₘ 𝟙 (F.obj X.2)) ≫
          leftCanonicalGen d F k X.2 := by
  let T := d.tensorEnrichedFunctor
  let R := GradedYoneda.representable (V := V) (𝟙_ I)
  let B : I × I := (𝟙_ I, X.2)
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.1
  let A : V := F.obj X.2
  let W₀ : V := (𝟙_ I ⊗ X.2) ⟶[V] k
  let Q : V := EnrichedDayKernel.relations T R F k (B, X)
  let g₀ := EnrichedDayKernel.gen T R F k B
  let g := EnrichedDayKernel.gen T R F k X
  let r := leftRelationOne d F k X
  let w : Q ⟶ EnrichedDayKernel.objects T R F k B :=
    (α_ ((EnrichedDayKernel.weight T k).obj (Opposite.op X)) (B ⟶[V] X)
      ((R.externalTensor F).obj B)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight T k).map
        (Opposite.op X) (Opposite.op B)) ⊗ₘ 𝟙 ((R.externalTensor F).obj B))
  let q : Q ⟶ EnrichedDayKernel.objects T R F k X :=
    (EnrichedDayKernel.weight T k).obj (Opposite.op X) ◁
      ((β_ (B ⟶[V] X) ((R.externalTensor F).obj B)).hom ≫
        MonoidalClosed.uncurry ((R.externalTensor F).map B X))
  let c := leftCollapseBase d k X
  let i : A ⟶ (𝟙_ I ⟶[V] 𝟙_ I) ⊗ A :=
    (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let t₁ := c ⊗ₘ 𝟙 A
  let t₂ := 𝟙 W₀ ⊗ₘ i
  have h : r ≫ (w ≫ g₀) = r ≫ (q ≫ g) :=
    congrArg (fun f => r ≫ f) (EnrichedDayKernel.gen_balanced T R F k B X)
  have hGrouped : (r ≫ w) ≫ g₀ = (r ≫ q) ≫ g :=
    (Category.assoc r w g₀).trans (h.trans (Category.assoc r q g).symm)
  have hWeight : r ≫ w = (α_ W U A).inv ≫ (c ⊗ₘ i) :=
    leftRelationOne_weightFace d F k X
  have hDiagram : r ≫ q = 𝟙 (EnrichedDayKernel.objects T R F k X) :=
    leftRelationOne_rightFace d F k X
  have hReduced : ((α_ W U A).inv ≫ (c ⊗ₘ i)) ≫ g₀ = g :=
    (congrArg (fun f => f ≫ g₀) hWeight).symm.trans
      (hGrouped.trans ((congrArg (fun f => f ≫ g) hDiagram).trans (Category.id_comp g)))
  have hFactor : c ⊗ₘ i = t₁ ≫ t₂ := by
    exact ((tensorHom_comp_tensorHom c (𝟙 A) (𝟙 W₀) i).trans
      ((congrArg (fun q => q ⊗ₘ (𝟙 A ≫ i)) (Category.comp_id c)).trans
        (congrArg (fun q => c ⊗ₘ q) (Category.id_comp i)))).symm
  have hFinal : ((α_ W U A).inv ≫ (c ⊗ₘ i)) ≫ g₀ =
      (α_ W U A).inv ≫ (leftCollapseBase d k X ⊗ₘ 𝟙 A) ≫ leftCanonicalGen d F k X.2 :=
    (Category.assoc (α_ W U A).inv (c ⊗ₘ i) g₀).trans
      ((congrArg (fun f => (α_ W U A).inv ≫ (f ≫ g₀)) hFactor).trans
        (congrArg (fun f => (α_ W U A).inv ≫ f) (Category.assoc t₁ t₂ g₀)))
  exact hReduced.symm.trans hFinal

/-- The second full relation reduces the canonical generator to the original inverse. -/
private theorem leftGen_second_reduction (j : I) :
    leftCanonicalGen d F k j = leftContraction F j k ≫ leftInvComponent d F k := by
  let T := d.tensorEnrichedFunctor
  let R := GradedYoneda.representable (V := V) (𝟙_ I)
  let B : I × I := (𝟙_ I, j)
  let C : I × I := (𝟙_ I, k)
  let W : V := (𝟙_ I ⊗ j) ⟶[V] k
  let A : V := F.obj j
  let Q : V := EnrichedDayKernel.relations T R F k (B, C)
  let g₀ := EnrichedDayKernel.gen T R F k B
  let g₁ := EnrichedDayKernel.gen T R F k C
  let r := leftRelationTwo d F k j
  let w : Q ⟶ EnrichedDayKernel.objects T R F k B :=
    (α_ ((EnrichedDayKernel.weight T k).obj (Opposite.op C)) (B ⟶[V] C)
      ((R.externalTensor F).obj B)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight T k).map
        (Opposite.op C) (Opposite.op B)) ⊗ₘ 𝟙 ((R.externalTensor F).obj B))
  let q : Q ⟶ EnrichedDayKernel.objects T R F k C :=
    (EnrichedDayKernel.weight T k).obj (Opposite.op C) ◁
      ((β_ (B ⟶[V] C) ((R.externalTensor F).obj B)).hom ≫
        MonoidalClosed.uncurry ((R.externalTensor F).map B C))
  let i : A ⟶ (𝟙_ I ⟶[V] 𝟙_ I) ⊗ A :=
    (λ_ A).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 A)
  let c := leftContraction F j k
  let p := eHomEquiv V (λ_ k).hom ⊗ₘ
    ((λ_ (F.obj k)).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 (F.obj k)))
  let n := (λ_ (F.obj k)).inv ≫ p
  have h : r ≫ (w ≫ g₀) = r ≫ (q ≫ g₁) :=
    congrArg (fun f => r ≫ f) (EnrichedDayKernel.gen_balanced T R F k B C)
  have hGrouped : (r ≫ w) ≫ g₀ = (r ≫ q) ≫ g₁ :=
    (Category.assoc r w g₀).trans (h.trans (Category.assoc r q g₁).symm)
  have hWeight : r ≫ w = 𝟙 W ⊗ₘ i := leftRelationTwo_weightFace d F j k
  have hDiagram : r ≫ q = c ≫ n := leftRelationTwo_diagramFace d F j k
  have hFlow : (𝟙 W ⊗ₘ i) ≫ g₀ = (c ≫ n) ≫ g₁ :=
    (congrArg (fun f => f ≫ g₀) hWeight).symm.trans
      (hGrouped.trans (congrArg (fun f => f ≫ g₁) hDiagram))
  exact hFlow.trans ((Category.assoc c n g₁).trans
    (congrArg (fun f => c ≫ f) (Category.assoc (λ_ (F.obj k)).inv p g₁)))

/-- Forward then inverse is the identity, by both actual enriched kernel relations. -/
theorem leftComponent_hom_inv_id :
    leftComponent d F k ≫ leftInvComponent d F k =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k) := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k
  intro X
  let g := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k X
  let a := (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.1) (F.obj X.2)).inv
  let c := leftCollapseBase d k X ⊗ₘ 𝟙 (F.obj X.2)
  let t := leftContraction F X.2 k
  let i := leftInvComponent d F k
  have h₀ := congrArg (fun f => f ≫ i) (gen_leftComponent d F k X)
  have h₁ := congrArg (fun f => f ≫ i) (leftForwardGen_eq_contraction d F k X)
  have hAssoc : (a ≫ c ≫ t) ≫ i = a ≫ c ≫ (t ≫ i) :=
    (Category.assoc a (c ≫ t) i).trans
      (congrArg (fun f => a ≫ f) (Category.assoc c t i))
  have h₂ := congrArg (fun f => a ≫ c ≫ f) (leftGen_second_reduction d F k X.2).symm
  exact (Category.assoc g (leftComponent d F k) i).symm.trans
    (h₀.trans (h₁.trans (hAssoc.trans
      (h₂.trans ((leftGen_first_reduction d F k X).symm.trans (Category.comp_id g).symm)))))

/-- Inverse then forward is the actual full enriched identity contraction. -/
theorem leftComponent_inv_hom_id :
    leftInvComponent d F k ≫ leftComponent d F k = 𝟙 (F.obj k) := by
  let W : V := (𝟙_ I ⊗ k) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let A : V := F.obj k
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k
  let Q : V := W ⊗ (U ⊗ A)
  let e : 𝟙_ V ⟶ W := eHomEquiv V (λ_ k).hom
  let f : 𝟙_ V ⟶ U := eId V (𝟙_ I)
  let delta : 𝟙_ V ⟶ W ⊗ U := (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ f)
  let p : W ⊗ U ⟶ (k ⟶[V] k) :=
    (β_ W U).hom ≫ (leftUnitHom d (𝟙_ I) k ⊗ₘ 𝟙 W) ≫ eComp V k (𝟙_ I ⊗ k) k
  let x : (𝟙_ V) ⊗ A ⟶ Q := e ⊗ₘ ((λ_ A).inv ≫ (f ⊗ₘ 𝟙 A))
  let n : A ⟶ Q := (λ_ A).inv ≫ x
  let g : Q ⟶ E := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k (𝟙_ I, k)
  let c : Q ⟶ A := leftForwardGen d F k (𝟙_ I, k)
  let a := leftComponent d F k
  let b := (β_ (k ⟶[V] k) A).hom
  let v := MonoidalClosed.uncurry (F.map k k)
  have hContract : delta ≫ p = eId V k := by
    simpa only [delta, p, W, U, e, f, Category.assoc] using leftUnitPoint_contraction d k
  have hInv₀ : leftInvComponent d F k = (λ_ A).inv ≫ x ≫ g := rfl
  have hInv : leftInvComponent d F k = n ≫ g :=
    hInv₀.trans (Category.assoc (λ_ A).inv x g).symm
  have hGen : g ≫ a = c := gen_leftComponent d F k (𝟙_ I, k)
  have hData : c = (α_ W U A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ b ≫ v := rfl
  have hDouble : n ≫ (α_ W U A).inv = (λ_ A).inv ≫ (delta ⊗ₘ 𝟙 A) :=
    (Category.assoc (λ_ A).inv x (α_ W U A).inv).trans
      (leftDoubleInsert_assoc (X := A) e f)
  have hCollect : (delta ⊗ₘ 𝟙 A) ≫ (p ⊗ₘ 𝟙 A) = eId V k ⊗ₘ 𝟙 A := by
    simp only [tensorHom_comp_tensorHom, hContract, Category.id_comp]
  have hSwap : (λ_ A).inv ≫ (eId V k ⊗ₘ 𝟙 A) ≫ b =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V k) := by
    simpa only [b, Category.assoc, leftUnitor_inv_braiding_assoc] using
      congrArg (fun q => (λ_ A).inv ≫ q) (braiding_naturality (eId V k) (𝟙 A))
  calc
    _ = (n ≫ g) ≫ a := congrArg (fun q => q ≫ a) hInv
    _ = n ≫ c := (Category.assoc n g a).trans (congrArg (fun q => n ≫ q) hGen)
    _ = n ≫ (α_ W U A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ b ≫ v :=
      congrArg (fun q => n ≫ q) hData
    _ = (λ_ A).inv ≫ (delta ⊗ₘ 𝟙 A) ≫ (p ⊗ₘ 𝟙 A) ≫ b ≫ v := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (p ⊗ₘ 𝟙 A) ≫ b ≫ v) hDouble
    _ = (λ_ A).inv ≫ (eId V k ⊗ₘ 𝟙 A) ≫ b ≫ v := by
      simpa only [Category.assoc] using
        congrArg (fun q => (λ_ A).inv ≫ q ≫ b ≫ v) hCollect
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V k) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ v) hSwap
    _ = _ := action_id F k

/-- The constructed left component is an isomorphism using only this particular kernel. -/
def leftComponentIso :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k ≅ F.obj k where
  hom := leftComponent d F k
  inv := leftInvComponent d F k
  hom_inv_id := leftComponent_hom_inv_id d F k
  inv_hom_id := leftComponent_inv_hom_id d F k

/-- The component isomorphism retains the actual descended map. -/
@[simp]
theorem leftComponentIso_hom : (leftComponentIso d F k).hom = leftComponent d F k := rfl

/-- The component isomorphism retains the actual unit-identity generator insertion. -/
@[simp]
theorem leftComponentIso_inv : (leftComponentIso d F k).inv = leftInvComponent d F k := rfl

/-- The actual descended left component retains full output-hom naturality. -/
theorem leftComponent_natural (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k')] :
    MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k k') ≫ leftComponent d F k' =
      (leftComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫ MonoidalClosed.uncurry (F.map k k') := by
  let R : V := k ⟶[V] k'
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k
  let E' : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k'
  let a : E ⟶ F.obj k := leftComponent d F k
  let b : E' ⟶ F.obj k' := leftComponent d F k'
  let u : E ⊗ R ⟶ E' := MonoidalClosed.uncurry
    (Output.map d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) F k k')
  let v : F.obj k ⊗ R ⟶ F.obj k' := MonoidalClosed.uncurry (F.map k k')
  let l : R ⊗ E ⟶ F.obj k' := (β_ R E).hom ≫ u ≫ b
  let r : R ⊗ E ⟶ F.obj k' := (β_ R E).hom ≫ (a ⊗ₘ 𝟙 R) ≫ v
  have h : l = r := by
    apply MonoidalClosed.curry_injective
    apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k
    intro X
    rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
    apply congrArg (MonoidalClosed.curry (A := R))
    let Q : V := EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k X
    let g : Q ⟶ E := EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k X
    have hLeft :
        R ◁ g ≫ l = Output.outputAction (X.1 ⊗ X.2) k k'
          ((𝟙_ I ⟶[V] X.1) ⊗ F.obj X.2) ≫ leftForwardGen d F k' X := by
      let g' := EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k' X
      let t := Output.outputAction (X.1 ⊗ X.2) k k'
        ((𝟙_ I ⟶[V] X.1) ⊗ F.obj X.2)
      have hAG : Output.actionGenerator d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) F k k' X = t ≫ g' := rfl
      have hg : (β_ R Q).hom ≫ (g ⊗ₘ 𝟙 R) ≫ u = t ≫ g' :=
        (Output.gen_naturality d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) F k k' X).trans hAG
      have hG' : g' ≫ b = leftForwardGen d F k' X := gen_leftComponent d F k' X
      have hBraid : (R ◁ g) ≫ (β_ R E).hom = (β_ R Q).hom ≫ (g ⊗ₘ 𝟙 R) := by
        simpa only [id_tensorHom] using braiding_naturality (𝟙 R) g
      have hA : R ◁ g ≫ l = ((R ◁ g ≫ (β_ R E).hom) ≫ u) ≫ b :=
        (Category.assoc (R ◁ g) (β_ R E).hom (u ≫ b)).symm.trans
          (Category.assoc (R ◁ g ≫ (β_ R E).hom) u b).symm
      have hB := congrArg (fun f => (f ≫ u) ≫ b) hBraid
      have hC := congrArg (fun f => f ≫ b) hg
      exact hA.trans (hB.trans
        ((congrArg (fun f => f ≫ b) (Category.assoc (β_ R Q).hom (g ⊗ₘ 𝟙 R) u)).trans
          (hC.trans ((Category.assoc t g' b).trans (congrArg (fun f => t ≫ f) hG')))))
    have hRight :
        R ◁ g ≫ r = R ◁ leftForwardGen d F k X ≫ (β_ R (F.obj k)).hom ≫ v := by
      calc
        _ = R ◁ (g ≫ a) ≫ (β_ R (F.obj k)).hom ≫ v := by
          simpa only [r, id_tensorHom, whiskerLeft_comp, Category.assoc] using
            congrArg (fun f => R ◁ g ≫ f ≫ v) (braiding_naturality (𝟙 R) a).symm
        _ = _ := by
          dsimp only [a, g]
          rw [gen_leftComponent]
    exact hLeft.trans ((leftForwardGen_output_natural d F k k' X).trans hRight.symm)
  have h' := congrArg (fun f => (β_ R E).inv ≫ f) h
  simpa only [l, r, Category.assoc, Iso.inv_hom_id_assoc] using h'

/-- The actual inverse components retain full output-hom naturality. -/
theorem leftInvComponent_natural (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k')] :
    MonoidalClosed.uncurry (F.map k k') ≫ leftInvComponent d F k' =
      (leftInvComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) F k k') := by
  have h := congrArg
    (fun f => (leftInvComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
      f ≫ leftInvComponent d F k') (leftComponent_natural d F k k')
  simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    leftComponent_hom_inv_id, leftComponent_inv_hom_id,
    id_tensorHom_id, Category.id_comp, Category.comp_id] using h.symm

end FullUnitors

section LeftFamily

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V)
  [∀ k, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ k, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ k, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- The left unitor is a genuine unit-graded transformation on the constructed output functor. -/
abbrev leftUnitorHom :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (Output.functor d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) F) F :=
  GradedNatTrans.unitOfComponents (fun k => leftComponent d F k)
    (fun k k' => leftComponent_natural d F k k')

/-- The original identity-inserting inverses form a genuine unit-graded transformation. -/
abbrev leftUnitorInv :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F
      (Output.functor d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) F) :=
  GradedNatTrans.unitOfComponents (fun k => leftInvComponent d F k)
    (fun k k' => leftInvComponent_natural d F k k')

/-- The genuine unitor's components are the actual descended maps. -/
theorem leftUnitorHom_component (k : I) :
    (eHomEquiv V).symm ((leftUnitorHom d F).app k) = leftComponent d F k :=
  GradedNatTrans.unitOfComponents_component (V := V)
    (F' := Output.functor d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) F)
    (G' := F) (fun k => leftComponent d F k)
    (fun k k' => leftComponent_natural d F k k') k

/-- The genuine inverse's components are the original chosen generators. -/
theorem leftUnitorInv_component (k : I) :
    (eHomEquiv V).symm ((leftUnitorInv d F).app k) = leftInvComponent d F k :=
  GradedNatTrans.unitOfComponents_component (V := V) (F' := F)
    (G' := Output.functor d.tensorEnrichedFunctor (GradedYoneda.representable (𝟙_ I)) F)
    (fun k => leftInvComponent d F k)
    (fun k k' => leftInvComponent_natural d F k k') k

/-- The left Day unitor is an actual isomorphism of genuine enriched functors. -/
def leftUnitor :
    (⟨Output.functor d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F⟩ : EnrichedFunctorCat V I) ≅ ⟨F⟩ where
  hom := leftUnitorHom d F
  inv := leftUnitorInv d F
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((leftUnitorHom d F).app k) ≫
      (eHomEquiv V).symm ((leftUnitorInv d F).app k) = _
    rw [leftUnitorHom_component, leftUnitorInv_component]
    exact leftComponent_hom_inv_id d F k
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((leftUnitorInv d F).app k) ≫
      (eHomEquiv V).symm ((leftUnitorHom d F).app k) = _
    rw [leftUnitorInv_component, leftUnitorHom_component]
    exact leftComponent_inv_hom_id d F k

/-- The isomorphism keeps the literal genuine forward transformation. -/
@[simp]
theorem leftUnitor_hom : (leftUnitor d F).hom = leftUnitorHom d F := rfl

/-- The isomorphism keeps the literal genuine inverse transformation. -/
@[simp]
theorem leftUnitor_inv : (leftUnitor d F).inv = leftUnitorInv d F := rfl

end LeftFamily

section InputComponentNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) {F G : EnrichedFunctor V I V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) G k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) G k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) G k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- Input naturality needs only the particular source and target unit kernels. -/
theorem leftComponent_input_natural :
    Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k ≫
        leftComponent d G k =
      leftComponent d F k ≫ (eHomEquiv V).symm (a.app k) := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k
  intro X
  let gF := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F k X
  let gG := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) G k X
  let m := Input.mapAt d.tensorEnrichedFunctor
    (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k
  let c := 𝟙 ((X.1 ⊗ X.2) ⟶[V] k) ⊗ₘ
    (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ (eHomEquiv V).symm (a.app X.2))
  let z : F.obj k ⟶ G.obj k := (eHomEquiv V).symm (a.app k)
  have hMap :
      EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) F k X ≫
          Input.mapAt d.tensorEnrichedFunctor
            (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k =
        (𝟙 ((X.1 ⊗ X.2) ⟶[V] k) ⊗ₘ
          (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ (eHomEquiv V).symm (a.app X.2))) ≫
            EnrichedDayKernel.gen d.tensorEnrichedFunctor
              (GradedYoneda.representable (𝟙_ I)) G k X := by
    have hId := GradedNatTrans.unitId_component (V := V)
      (GradedYoneda.representable (V := V) (𝟙_ I)) X.1
    have hCoeff :
        (𝟙 (d.tensorEnrichedFunctor.obj X ⟶[V] k) ⊗ₘ
          ((eHomEquiv V).symm
            ((GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))).app X.1) ⊗ₘ
              (eHomEquiv V).symm (a.app X.2))) =
          (𝟙 ((X.1 ⊗ X.2) ⟶[V] k) ⊗ₘ
            (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ (eHomEquiv V).symm (a.app X.2))) :=
      congrArg
        (fun q : (𝟙_ I ⟶[V] X.1) ⟶ (𝟙_ I ⟶[V] X.1) =>
          𝟙 (d.tensorEnrichedFunctor.obj X ⟶[V] k) ⊗ₘ
            (q ⊗ₘ (eHomEquiv V).symm (a.app X.2))) hId
    exact (Input.gen_mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k X).trans
        (congrArg (fun q => q ≫ EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (GradedYoneda.representable (𝟙_ I)) G k X) hCoeff)
  have hF : gF ≫ leftComponent d F k = leftForwardGen d F k X := gen_leftComponent d F k X
  have hG : gG ≫ leftComponent d G k = leftForwardGen d G k X := gen_leftComponent d G k X
  have hC : c = ((X.1 ⊗ X.2) ⟶[V] k) ◁
      (𝟙 (𝟙_ I ⟶[V] X.1) ⊗ₘ (eHomEquiv V).symm (a.app X.2)) := id_tensorHom _ _
  exact (Category.assoc gF m (leftComponent d G k)).symm.trans
    ((congrArg (fun q => q ≫ leftComponent d G k) hMap).trans
      ((Category.assoc c gG (leftComponent d G k)).trans
        ((congrArg (fun q => c ≫ q) hG).trans
          ((congrArg (fun q => q ≫ leftForwardGen d G k X) hC).trans
            ((leftForwardGen_input_natural d a k X).trans
              ((congrArg (fun q => q ≫ z) hF).symm.trans
                (Category.assoc gF (leftComponent d F k) z)))))))

end InputComponentNaturality

section LeftUnitEndofunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) F k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        (GradedYoneda.representable (𝟙_ I)) F k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- Tensoring by the actual representable unit needs only the unit-input kernels. -/
def leftUnitEndofunctor : EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I where
  obj F := ⟨Output.functor d.tensorEnrichedFunctor
    (GradedYoneda.representable (𝟙_ I)) F.toEnrichedFunctor⟩
  map a := Input.natTrans d.tensorEnrichedFunctor
    (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm
      ((Input.natTrans d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I)))
        (GradedNatTrans.unitId F.toEnrichedFunctor)).app k) = _
    rw [Input.natTrans_component, Input.mapAt_id]
  map_comp a b := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp]
    change (eHomEquiv V).symm
      ((Input.natTrans d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I)))
        (GradedNatTrans.unitComp a b)).app k) =
      (eHomEquiv V).symm
        ((Input.natTrans d.tensorEnrichedFunctor
          (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a).app k) ≫
      (eHomEquiv V).symm
        ((Input.natTrans d.tensorEnrichedFunctor
          (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) b).app k)
    rw [Input.natTrans_component, Input.natTrans_component, Input.natTrans_component]
    have hUnit :
        GradedNatTrans.unitComp
            (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))
            (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I))) =
          GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)) := by
      exact Category.id_comp
        (𝟙 (⟨GradedYoneda.representable (V := V) (𝟙_ I)⟩ : EnrichedFunctorCat V I))
    simpa only [hUnit] using Input.mapAt_comp d.tensorEnrichedFunctor
      (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I)))
      (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a b k

/-- The actual fixed-unit functor acts by the selected genuine diagram maps. -/
@[simp]
theorem leftUnitEndofunctor_map_component {F G : EnrichedFunctorCat V I}
    (a : F ⟶ G) (k : I) :
    EnrichedFunctorCat.component ((leftUnitEndofunctor d).map a) k =
      Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k :=
  Input.natTrans_component d.tensorEnrichedFunctor _ a k

/-- The genuine left Day unitors are natural in every genuine enriched input transformation. -/
def leftUnitorNatIso : leftUnitEndofunctor d ≅ 𝟭 (EnrichedFunctorCat V I) :=
  NatIso.ofComponents (fun F => leftUnitor d F.toEnrichedFunctor) (by
    intro F G a
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      leftUnitEndofunctor_map_component]
    change Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) a k ≫
        (eHomEquiv V).symm ((leftUnitorHom d G.toEnrichedFunctor).app k) =
      (eHomEquiv V).symm ((leftUnitorHom d F.toEnrichedFunctor).app k) ≫
        (eHomEquiv V).symm (a.app k)
    rw [leftUnitorHom_component, leftUnitorHom_component]
    exact leftComponent_input_natural d a k)

end LeftUnitEndofunctor

section RightIndexFull

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

attribute [local instance] Enriched.prodCategory

/-- The actual full hom map tensoring by the chosen unit on the right. -/
private def rightUnitTensorMap (d : EnrichedMonoidalCategoryData V I) (i i' : I) :
    (i ⟶[V] i') ⟶ ((i ⊗ 𝟙_ I) ⟶[V] (i' ⊗ 𝟙_ I)) :=
  (ρ_ (i ⟶[V] i')).inv ≫ (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I)) ≫
    d.tensorMap i i' (𝟙_ I) (𝟙_ I)

/-- Stored rho naturality acts on the entire chosen index hom. -/
private theorem rightUnitTensorMap_natural (d : EnrichedMonoidalCategoryData V I)
    (i i' : I) :
    rightUnitTensorMap d i i' ≫ eHomWhiskerLeft V (i ⊗ 𝟙_ I) (ρ_ i').hom =
      eHomWhiskerRight V (ρ_ i).hom i' := by
  have h := congrArg (fun f => (λ_ (i ⟶[V] i')).inv ≫ f)
    (d.rightUnitorNaturality i i')
  change (λ_ (i ⟶[V] i')).inv ≫ (β_ (𝟙_ V) (i ⟶[V] i')).hom ≫
      (rightUnitTensorMap d i i' ⊗ₘ eHomEquiv V (ρ_ i').hom) ≫
        eComp V (i ⊗ 𝟙_ I) (i' ⊗ 𝟙_ I) i' =
    (λ_ (i ⟶[V] i')).inv ≫
      (eHomEquiv V (ρ_ i).hom ⊗ₘ 𝟙 (i ⟶[V] i')) ≫
        eComp V (i ⊗ 𝟙_ I) i i' at h
  rw [leftUnitor_inv_braiding_assoc, rightUnitor_inv_comp_tensorHom_assoc] at h
  simpa only [eHomWhiskerLeft, eHomWhiskerRight, tensorHom_id, Category.assoc] using h

/-- The actual inverse rho conjugates the full right-unit tensor hom. -/
private theorem rightUnitTensorMap_inv_natural (d : EnrichedMonoidalCategoryData V I)
    (i i' : I) :
    rightUnitTensorMap d i i' ≫ eHomWhiskerRight V (ρ_ i).inv (i' ⊗ 𝟙_ I) =
      eHomWhiskerLeft V i (ρ_ i').inv := by
  have h := congrArg
    (fun v => v ≫ eHomWhiskerRight V (ρ_ i).inv i' ≫
      eHomWhiskerLeft V i (ρ_ i').inv) (rightUnitTensorMap_natural d i i')
  simp only [Category.assoc] at h
  rw [eHom_whisker_exchange_assoc] at h
  simpa only [Category.assoc, ← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, eHomWhiskerLeft_id, eHomWhiskerRight_id,
    Category.comp_id, Category.id_comp] using h

omit [MonoidalCategory I] in
/-- Identity insertions in the two middle slots leave the full active tensor unchanged. -/
private theorem tensorMu_middle_insert {P Q A B : V}
    (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) :
    (((ρ_ P).inv ≫ (𝟙 P ⊗ₘ f)) ⊗ₘ
        ((λ_ Q).inv ≫ (g ⊗ₘ 𝟙 Q))) ≫ tensorμ P A B Q =
      ((ρ_ P).inv ≫ (𝟙 P ⊗ₘ g)) ⊗ₘ
        ((λ_ Q).inv ≫ (f ⊗ₘ 𝟙 Q)) := by
  have hUnit :
      ((ρ_ P).inv ⊗ₘ (λ_ Q).inv) ≫ tensorμ P (𝟙_ V) (𝟙_ V) Q =
        (ρ_ P).inv ⊗ₘ (λ_ Q).inv := by
    dsimp only [tensorμ]
    rw [braiding_tensorUnit_left]
    monoidal
  calc
    _ = ((ρ_ P).inv ⊗ₘ (λ_ Q).inv) ≫
        ((𝟙 P ⊗ₘ f) ⊗ₘ (g ⊗ₘ 𝟙 Q)) ≫ tensorμ P A B Q := by
      simpa only [Category.assoc] using
        congrArg (fun v => v ≫ tensorμ P A B Q)
          (tensorHom_comp_tensorHom (ρ_ P).inv (λ_ Q).inv
            (𝟙 P ⊗ₘ f) (g ⊗ₘ 𝟙 Q)).symm
    _ = ((ρ_ P).inv ⊗ₘ (λ_ Q).inv) ≫ tensorμ P (𝟙_ V) (𝟙_ V) Q ≫
        ((𝟙 P ⊗ₘ g) ⊗ₘ (f ⊗ₘ 𝟙 Q)) := by
      simpa only [Category.assoc] using
        congrArg (fun v => ((ρ_ P).inv ⊗ₘ (λ_ Q).inv) ≫ v)
          (tensorμ_natural (𝟙 P) f g (𝟙 Q))
    _ = _ := by
      have h := congrArg
        (fun v => v ≫ ((𝟙 P ⊗ₘ g) ⊗ₘ (f ⊗ₘ 𝟙 Q))) hUnit
      simpa only [Category.assoc, tensorHom_comp_tensorHom] using h

omit [MonoidalCategory I] in
/-- The straight two-coordinate product path composes both full active homs. -/
private theorem productComp_straight (i i' j j' : I) :
    (((ρ_ (i ⟶[V] i')).inv ≫ (𝟙 (i ⟶[V] i') ⊗ₘ eId V j)) ⊗ₘ
        ((λ_ (j ⟶[V] j')).inv ≫ (eId V i' ⊗ₘ 𝟙 (j ⟶[V] j')))) ≫
      eComp V (i, j) (i', j) (i', j') = 𝟙 ((i ⟶[V] i') ⊗ (j ⟶[V] j')) := by
  have h := congrArg
    (fun f => f ≫ (eComp V i i' i' ⊗ₘ eComp V j j j'))
      (tensorMu_middle_insert (P := i ⟶[V] i') (Q := j ⟶[V] j')
        (eId V j) (eId V i'))
  have hProd : eComp V (i, j) (i', j) (i', j') =
      tensorμ (i ⟶[V] i') (j ⟶[V] j) (i' ⟶[V] i') (j ⟶[V] j') ≫
        (eComp V i i' i' ⊗ₘ eComp V j j j') := rfl
  rw [hProd]
  simpa only [Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_id, id_tensorHom, e_comp_id, e_id_comp, id_tensorHom_id,
    id_whiskerRight, Category.comp_id] using h

omit [MonoidalCategory I] in
/-- Padding the first hom by its actual identity retains the full active braid. -/
private theorem productComp_second_identity (i i' j j' j'' : I) :
    (((λ_ (j ⟶[V] j')).inv ≫ (eId V i ⊗ₘ 𝟙 (j ⟶[V] j'))) ⊗ₘ
        𝟙 ((i ⟶[V] i') ⊗ (j' ⟶[V] j''))) ≫
      eComp V (i, j) (i, j') (i', j'') =
      (α_ (j ⟶[V] j') (i ⟶[V] i') (j' ⟶[V] j'')).inv ≫
        (β_ (j ⟶[V] j') (i ⟶[V] i')).hom ▷ (j' ⟶[V] j'') ≫
        (α_ (i ⟶[V] i') (j ⟶[V] j') (j' ⟶[V] j'')).hom ≫
        ((i ⟶[V] i') ◁ eComp V j j' j'') := by
  let U : V := j ⟶[V] j'
  let P : V := i ⟶[V] i'
  let Q : V := j' ⟶[V] j''
  have hUnit :
      (λ_ U).inv ▷ (P ⊗ Q) ≫ tensorμ (𝟙_ V) U P Q =
        (α_ U P Q).inv ≫ (β_ U P).hom ▷ Q ≫ (α_ P U Q).hom ≫
          ((λ_ P).inv ⊗ₘ 𝟙 (U ⊗ Q)) := by
    dsimp only [tensorμ]
    monoidal
  have h := congrArg
    (fun f => f ≫ ((eId V i ▷ P ⊗ₘ 𝟙 (U ⊗ Q)) ≫
      (eComp V i i i' ⊗ₘ eComp V j j' j''))) hUnit
  have hProd : eComp V (i, j) (i, j') (i', j'') =
      tensorμ (i ⟶[V] i) U P Q ≫
        (eComp V i i i' ⊗ₘ eComp V j j' j'') := rfl
  have hNat := tensorμ_natural_left (eId V i) (𝟙 U) P Q
  have hPad := congrArg
    (fun v => (λ_ U).inv ▷ (P ⊗ Q) ≫ v ≫
      (eComp V i i i' ⊗ₘ eComp V j j' j'')) hNat
  rw [hProd]
  calc
    _ = (λ_ U).inv ▷ (P ⊗ Q) ≫ tensorμ (𝟙_ V) U P Q ≫
        (eId V i ▷ P ⊗ₘ 𝟙 U ▷ Q) ≫
        (eComp V i i i' ⊗ₘ eComp V j j' j'') := by
      simpa only [U, P, Q, tensorHom_id, comp_whiskerRight, Category.assoc] using hPad
    _ = _ := by
      simpa only [U, P, Q, id_whiskerRight, id_tensorHom, tensorHom_comp_tensorHom,
        Category.assoc, e_id_comp, Category.id_comp] using h

/-- The whole active right hom composes before the actual binary tensor hom map. -/
private theorem rightTensorHom_comp_full (d : EnrichedMonoidalCategoryData V I)
    (i i' j j' : I) :
    (rightTensorHom d i j ⊗ₘ d.tensorMap i i' j j') ≫
        eComp V (i ⊗ 𝟙_ I) (i ⊗ j) (i' ⊗ j') =
      (α_ (𝟙_ I ⟶[V] j) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (β_ (𝟙_ I ⟶[V] j) (i ⟶[V] i')).hom ▷ (j ⟶[V] j') ≫
        (α_ (i ⟶[V] i') (𝟙_ I ⟶[V] j) (j ⟶[V] j')).hom ≫
        ((i ⟶[V] i') ◁ eComp V (𝟙_ I) j j') ≫ d.tensorMap i i' (𝟙_ I) j' := by
  let r : (𝟙_ I ⟶[V] j) ⟶ (i ⟶[V] i) ⊗ (𝟙_ I ⟶[V] j) :=
    (λ_ (𝟙_ I ⟶[V] j)).inv ≫ (eId V i ⊗ₘ 𝟙 (𝟙_ I ⟶[V] j))
  have hPad := productComp_second_identity (V := V) i i' (𝟙_ I) j j'
  change
    (r ⊗ₘ 𝟙 ((i ⟶[V] i') ⊗ (j ⟶[V] j'))) ≫
        (Enriched.prodCategory V I I).comp (i, 𝟙_ I) (i, j) (i', j') =
      (α_ (𝟙_ I ⟶[V] j) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (β_ (𝟙_ I ⟶[V] j) (i ⟶[V] i')).hom ▷ (j ⟶[V] j') ≫
        (α_ (i ⟶[V] i') (𝟙_ I ⟶[V] j) (j ⟶[V] j')).hom ≫
        ((i ⟶[V] i') ◁ eComp V (𝟙_ I) j j') at hPad
  have h := congrArg
    (fun f => (r ⊗ₘ 𝟙 ((i ⟶[V] i') ⊗ (j ⟶[V] j'))) ≫ f)
    (d.tensorMap_comp i i i' (𝟙_ I) j j')
  rw [← Category.assoc, hPad] at h
  simpa only [rightTensorHom, r, tensorHom_id,
    whiskerRight_comp_tensorHom_assoc, Category.assoc] using h.symm

/-- The straight mixed tensor hom is the actual first-coordinate then second-coordinate action. -/
private theorem tensorMap_right_mixed (d : EnrichedMonoidalCategoryData V I)
    (i i' j : I) :
    d.tensorMap i i' (𝟙_ I) j =
      (rightUnitTensorMap d i i' ⊗ₘ rightTensorHom d i' j) ≫
        eComp V (i ⊗ 𝟙_ I) (i' ⊗ 𝟙_ I) (i' ⊗ j) := by
  let p : (i ⟶[V] i') ⟶ (i ⟶[V] i') ⊗ (𝟙_ I ⟶[V] 𝟙_ I) :=
    (ρ_ (i ⟶[V] i')).inv ≫ (𝟙 (i ⟶[V] i') ⊗ₘ eId V (𝟙_ I))
  let q : (𝟙_ I ⟶[V] j) ⟶ (i' ⟶[V] i') ⊗ (𝟙_ I ⟶[V] j) :=
    (λ_ (𝟙_ I ⟶[V] j)).inv ≫ (eId V i' ⊗ₘ 𝟙 (𝟙_ I ⟶[V] j))
  have hPad := productComp_straight (V := V) i i' (𝟙_ I) j
  change (p ⊗ₘ q) ≫ (Enriched.prodCategory V I I).comp
      (i, 𝟙_ I) (i', 𝟙_ I) (i', j) =
    𝟙 ((i ⟶[V] i') ⊗ (𝟙_ I ⟶[V] j)) at hPad
  have h := congrArg (fun f => (p ⊗ₘ q) ≫ f)
    (d.tensorMap_comp i i' i' (𝟙_ I) (𝟙_ I) j)
  rw [← Category.assoc, hPad, Category.id_comp] at h
  simpa only [rightUnitTensorMap, rightTensorHom, p, q,
    ← tensorHom_comp_tensorHom, Category.assoc] using h

/-- The inverse index rho transports the entire mixed contraction. -/
private theorem rightTensorHom_middle_transport (d : EnrichedMonoidalCategoryData V I)
    (i i' j : I) :
    (rightUnitTensorMap d i i' ⊗ₘ rightTensorHom d i' j) ≫
        eComp V (i ⊗ 𝟙_ I) (i' ⊗ 𝟙_ I) (i' ⊗ j) ≫
        eHomWhiskerRight V (ρ_ i).inv (i' ⊗ j) =
      (𝟙 (i ⟶[V] i') ⊗ₘ rightUnitHom d i' j) ≫ eComp V i i' (i' ⊗ j) := by
  rw [eComp_eHomWhiskerRight, tensorHom_comp_whiskerRight_assoc,
    rightUnitTensorMap_inv_natural,
    eComp_middle_inverse (ρ_ i') i (i' ⊗ j) (rightTensorHom d i' j)]
  rfl

/-- The right index unitor identity retains both complete product hom coordinates. -/
private theorem rightUnitHom_product_natural (d : EnrichedMonoidalCategoryData V I)
    (i i' j j' : I) :
    (rightUnitHom d i j ⊗ₘ d.tensorMap i i' j j') ≫ eComp V i (i ⊗ j) (i' ⊗ j') =
      (α_ (𝟙_ I ⟶[V] j) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
        (β_ (𝟙_ I ⟶[V] j) (i ⟶[V] i')).hom ▷ (j ⟶[V] j') ≫
        (α_ (i ⟶[V] i') (𝟙_ I ⟶[V] j) (j ⟶[V] j')).hom ≫
        ((i ⟶[V] i') ◁ (eComp V (𝟙_ I) j j' ≫ rightUnitHom d i' j')) ≫
          eComp V i i' (i' ⊗ j') := by
  calc
    _ = ((rightTensorHom d i j ⊗ₘ d.tensorMap i i' j j') ≫
          eComp V (i ⊗ 𝟙_ I) (i ⊗ j) (i' ⊗ j')) ≫
        eHomWhiskerRight V (ρ_ i).inv (i' ⊗ j') := by
      unfold rightUnitHom
      rw [← tensorHom_comp_whiskerRight_assoc, ← eComp_eHomWhiskerRight]
      simp only [Category.assoc]
    _ = ((α_ (𝟙_ I ⟶[V] j) (i ⟶[V] i') (j ⟶[V] j')).inv ≫
          (β_ (𝟙_ I ⟶[V] j) (i ⟶[V] i')).hom ▷ (j ⟶[V] j') ≫
          (α_ (i ⟶[V] i') (𝟙_ I ⟶[V] j) (j ⟶[V] j')).hom ≫
          ((i ⟶[V] i') ◁ eComp V (𝟙_ I) j j') ≫
          d.tensorMap i i' (𝟙_ I) j') ≫
        eHomWhiskerRight V (ρ_ i).inv (i' ⊗ j') :=
      congrArg (fun f => f ≫ eHomWhiskerRight V (ρ_ i).inv (i' ⊗ j'))
        (rightTensorHom_comp_full d i i' j j')
    _ = _ := by
      rw [tensorMap_right_mixed]
      simp only [Category.assoc]
      rw [rightTensorHom_middle_transport]
      simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]

end RightIndexFull

section RightStrengthFull

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- The literal right strength acts on the full actual right index hom. -/
def rightStrengthComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X : I × I) :
    F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2) ⟶ F.obj (X.1 ⊗ X.2) :=
  F.obj X.1 ◁ rightUnitHom d X.1 X.2 ≫
    MonoidalClosed.uncurry (F.map X.1 (X.1 ⊗ X.2))

/-- The genuine right strength retains the entire product-enriched hom. -/
theorem rightStrength_natural (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X Y : I × I) :
    MonoidalClosed.uncurry
        ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map X Y) ≫
        rightStrengthComponent d F Y =
      (rightStrengthComponent d F X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) := by
  let a : V := 𝟙_ I ⟶[V] X.2
  let b : V := 𝟙_ I ⟶[V] Y.2
  let P : V := X.1 ⟶[V] Y.1
  let Q : V := X.2 ⟶[V] Y.2
  let z : V := F.obj X.1
  let z' : V := F.obj Y.1
  let A : I := X.1 ⊗ X.2
  let B : I := Y.1 ⊗ Y.2
  let J : V := X.1 ⟶[V] A
  let L : V := Y.1 ⟶[V] B
  let M : V := A ⟶[V] B
  let p : a ⊗ Q ⟶ b := eComp V (𝟙_ I) X.2 Y.2
  let q : z ⊗ P ⟶ z' := MonoidalClosed.uncurry (F.map X.1 Y.1)
  let t : P ⊗ Q ⟶ M := d.tensorMap X.1 Y.1 X.2 Y.2
  let theta : a ⟶ J := rightUnitHom d X.1 X.2
  let theta' : b ⟶ L := rightUnitHom d Y.1 Y.2
  let u : z ⊗ J ⟶ F.obj A := MonoidalClosed.uncurry (F.map X.1 A)
  let v : z' ⊗ L ⟶ F.obj B := MonoidalClosed.uncurry (F.map Y.1 B)
  let w : F.obj A ⊗ M ⟶ F.obj B := MonoidalClosed.uncurry (F.map A B)
  let cX : J ⊗ M ⟶ (X.1 ⟶[V] B) := eComp V X.1 A B
  let cY : P ⊗ L ⟶ (X.1 ⟶[V] B) := eComp V X.1 Y.1 B
  let act : z ⊗ (X.1 ⟶[V] B) ⟶ F.obj B := MonoidalClosed.uncurry (F.map X.1 B)
  let S : (z ⊗ a) ⊗ (P ⊗ Q) ⟶ (z ⊗ P) ⊗ (a ⊗ Q) := tensorμ z a P Q
  let k0 : (z ⊗ a) ⊗ (P ⊗ Q) ⟶ z ⊗ (a ⊗ (P ⊗ Q)) :=
    (α_ z a (P ⊗ Q)).hom
  let shuffle : a ⊗ (P ⊗ Q) ⟶ P ⊗ (a ⊗ Q) :=
    (α_ a P Q).inv ≫ (β_ a P).hom ▷ Q ≫ (α_ P a Q).hom
  let r : (z ⊗ a) ⊗ (P ⊗ Q) ⟶ z ⊗ (P ⊗ b) :=
    S ≫ (𝟙 (z ⊗ P) ⊗ₘ p) ≫ (α_ z P b).hom
  have hShuffle : k0 ≫ z ◁ shuffle = S ≫ (α_ z P (a ⊗ Q)).hom := by
    dsimp only [k0, shuffle, S, tensorμ]
    monoidal
  have hk : k0 ≫ z ◁ (shuffle ≫ P ◁ p) = r := by
    calc
      _ = (k0 ≫ z ◁ shuffle) ≫ z ◁ P ◁ p := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
      _ = (S ≫ (α_ z P (a ⊗ Q)).hom) ≫ z ◁ P ◁ p :=
        congrArg (fun f => f ≫ z ◁ P ◁ p) hShuffle
      _ = _ := by
        simpa only [r, id_tensorHom, Category.assoc] using
          congrArg (fun f => S ≫ f) (associator_naturality_right z P p).symm
  have hMoveY :
      (𝟙 (z ⊗ P) ⊗ₘ p) ≫ (α_ z P b).hom ≫ z ◁ P ◁ theta' ≫
        (α_ z P L).inv ≫ (q ▷ L) = (q ⊗ₘ p) ≫ z' ◁ theta' := by
    rw [← associator_naturality_right_assoc, Iso.hom_inv_id_assoc]
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  have hActionY : z ◁ cY ≫ act = (α_ z P L).inv ≫ (q ▷ L) ≫ v :=
    action_comp F X.1 Y.1 B
  have hY :
      r ≫ z ◁ ((P ◁ theta') ≫ cY) ≫ act = S ≫ (q ⊗ₘ p) ≫ z' ◁ theta' ≫ v := by
    calc
      _ = r ≫ z ◁ P ◁ theta' ≫ (z ◁ cY ≫ act) := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
      _ = r ≫ z ◁ P ◁ theta' ≫ (α_ z P L).inv ≫ (q ▷ L) ≫ v := by
        rw [hActionY]
      _ = _ := by simpa only [r, Category.assoc] using congrArg (fun f => S ≫ f ≫ v) hMoveY
  have hTheta : (theta ⊗ₘ t) ≫ cX = shuffle ≫ P ◁ (p ≫ theta') ≫ cY := by
    simpa only [theta, theta', t, cX, cY, shuffle, a, P, Q, p, A, B,
      id_tensorHom, Category.assoc] using rightUnitHom_product_natural d X.1 Y.1 X.2 Y.2
  have hIndex :
      k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act = r ≫ z ◁ ((P ◁ theta') ≫ cY) ≫ act := by
    let b0 : a ⊗ (P ⊗ Q) ⟶ P ⊗ b := shuffle ≫ P ◁ p
    let b1 : P ⊗ b ⟶ (X.1 ⟶[V] B) := (P ◁ theta') ≫ cY
    have hI : (theta ⊗ₘ t) ≫ cX = b0 ≫ b1 := by
      simpa only [b0, b1, whiskerLeft_comp, Category.assoc] using hTheta
    have hW := congrArg
      (fun f : a ⊗ (P ⊗ Q) ⟶ (X.1 ⟶[V] B) => k0 ≫ z ◁ f ≫ act) hI
    have hF : k0 ≫ z ◁ (b0 ≫ b1) ≫ act =
        (k0 ≫ z ◁ b0) ≫ z ◁ b1 ≫ act := by
      simp only [whiskerLeft_comp, Category.assoc]
    have hK := congrArg
      (fun f : (z ⊗ a) ⊗ (P ⊗ Q) ⟶ z ⊗ (P ⊗ b) => f ≫ z ◁ b1 ≫ act) hk
    exact hW.trans (hF.trans hK)
  have hMoveX :
      k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (α_ z J M).inv ≫ (u ▷ M) =
        ((z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫ (𝟙 (F.obj A) ⊗ₘ t) := by
    have ha := associator_inv_naturality (𝟙 z) theta t
    simp only [id_tensorHom] at ha
    have h := congrArg (fun f => (α_ z a (P ⊗ Q)).hom ≫ f ≫ (u ▷ M)) ha
    simpa only [k0, Category.assoc, Iso.hom_inv_id_assoc, ← tensorHom_id,
      ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using h
  have hActionX : z ◁ cX ≫ act = (α_ z J M).inv ≫ (u ▷ M) ≫ w := action_comp F X.1 A B
  have hX :
      k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act =
        ((z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫ (𝟙 (F.obj A) ⊗ₘ t) ≫ w := by
    calc
      _ = k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (z ◁ cX ≫ act) := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
      _ = k0 ≫ z ◁ (theta ⊗ₘ t) ≫ (α_ z J M).inv ≫ (u ▷ M) ≫ w := by
        rw [hActionX]
      _ = _ := by simpa only [Category.assoc] using congrArg (fun f => f ≫ w) hMoveX
  have hExternal :
      MonoidalClosed.uncurry
        ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map X Y) = S ≫ (q ⊗ₘ p) := by
    rw [EnrichedFunctor.externalTensor_uncurry, GradedYoneda.representable_uncurry]
  have hTarget : MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V F).map X Y) =
      (𝟙 (F.obj A) ⊗ₘ t) ≫ w := by
    change MonoidalClosed.uncurry (t ≫ F.map A B) = _
    rw [MonoidalClosed.uncurry_natural_left, id_tensorHom]
  let sX : z ⊗ a ⟶ F.obj A := rightStrengthComponent d F X
  let sY : z' ⊗ b ⟶ F.obj B := rightStrengthComponent d F Y
  have hSX : sX = z ◁ theta ≫ u := rfl
  have hSY : sY = z' ◁ theta' ≫ v := rfl
  have hE := congrArg
    (fun f : (z ⊗ a) ⊗ (P ⊗ Q) ⟶ z' ⊗ b => f ≫ sY) hExternal
  have hT := congrArg
    (fun f : F.obj A ⊗ (P ⊗ Q) ⟶ F.obj B => (sX ⊗ₘ 𝟙 (P ⊗ Q)) ≫ f) hTarget
  have hWord :
      (S ≫ (q ⊗ₘ p)) ≫ sY =
        (sX ⊗ₘ 𝟙 (P ⊗ Q)) ≫ ((𝟙 (F.obj A) ⊗ₘ t) ≫ w) := by
    calc
      _ = S ≫ (q ⊗ₘ p) ≫ z' ◁ theta' ≫ v := by
        simpa only [Category.assoc] using
          congrArg (fun f => (S ≫ (q ⊗ₘ p)) ≫ f) hSY
      _ = r ≫ z ◁ ((P ◁ theta') ≫ cY) ≫ act := hY.symm
      _ = k0 ≫ z ◁ ((theta ⊗ₘ t) ≫ cX) ≫ act := hIndex.symm
      _ = ((z ◁ theta ≫ u) ⊗ₘ 𝟙 (P ⊗ Q)) ≫
          (𝟙 (F.obj A) ⊗ₘ t) ≫ w := hX
      _ = _ := congrArg
        (fun f => (f ⊗ₘ 𝟙 (P ⊗ Q)) ≫ (𝟙 (F.obj A) ⊗ₘ t) ≫ w) hSX.symm
  exact hE.trans (hWord.trans hT.symm)

/-- The actual full right strength is a genuine unit-graded transformation. -/
abbrev rightStrength (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F.externalTensor (GradedYoneda.representable (𝟙_ I)))
      (d.tensorEnrichedFunctor.comp V F) :=
  GradedNatTrans.unitOfComponents (rightStrengthComponent d F) (rightStrength_natural d F)

/-- The genuine right strength retains the literal ordinary component. -/
theorem rightStrength_component (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (X : I × I) :
    (eHomEquiv V).symm ((rightStrength d F).app X) = rightStrengthComponent d F X :=
  GradedNatTrans.unitOfComponents_component _ _ X

end RightStrengthFull

section RightFull

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- The original right generator is the genuine right strength followed by evaluation. -/
private theorem rightForwardGen_eq_strength (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    rightForwardGen d F k X =
      (𝟙 ((X.1 ⊗ X.2) ⟶[V] k) ⊗ₘ rightStrengthComponent d F X) ≫
        evaluationGen F k X := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let z : V := F.obj X.1
  let A : I := X.1 ⊗ X.2
  let H : V := X.1 ⟶[V] A
  let B : V := F.obj A
  let t : U ⟶ H := rightUnitHom d X.1 X.2
  let c : H ⊗ W ⟶ (X.1 ⟶[V] k) := eComp V X.1 A k
  let u : z ⊗ H ⟶ B := MonoidalClosed.uncurry (F.map X.1 A)
  let v : B ⊗ W ⟶ F.obj k := MonoidalClosed.uncurry (F.map A k)
  let w : z ⊗ (X.1 ⟶[V] k) ⟶ F.obj k := MonoidalClosed.uncurry (F.map X.1 k)
  let K : W ⊗ (z ⊗ U) ⟶ z ⊗ (H ⊗ W) :=
    (β_ W (z ⊗ U)).hom ≫ (α_ z U W).hom ≫ z ◁ (t ⊗ₘ 𝟙 W)
  have hK :
      K = (β_ W (z ⊗ U)).hom ≫ (z ◁ t) ▷ W ≫ (α_ z H W).hom := by
    simpa only [K, tensorHom_id, Category.assoc] using
      congrArg (fun f => (β_ W (z ⊗ U)).hom ≫ f)
        (associator_naturality_middle z t W).symm
  have hData :
      (show W ⊗ (z ⊗ U) ⟶ F.obj k from rightForwardGen d F k X) =
        (β_ W (z ⊗ U)).hom ≫ (α_ z U W).hom ≫
          z ◁ ((t ⊗ₘ 𝟙 W) ≫ c) ≫ w := rfl
  have hLeft :
      (show W ⊗ (z ⊗ U) ⟶ F.obj k from rightForwardGen d F k X) =
        K ≫ z ◁ c ≫ w := by
    exact hData.trans (by simp only [K, whiskerLeft_comp, Category.assoc])
  have hAction : z ◁ c ≫ w = (α_ z H W).inv ≫ (u ▷ W) ≫ v :=
    action_comp F X.1 A k
  calc
    _ = K ≫ z ◁ c ≫ w := hLeft
    _ = K ≫ (α_ z H W).inv ≫ (u ▷ W) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun f => K ≫ f) hAction
    _ = (β_ W (z ⊗ U)).hom ≫ (z ◁ t ≫ u) ▷ W ≫ v := by
      rw [hK]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]
    _ = _ := by
      let a : z ⊗ U ⟶ B := z ◁ t ≫ u
      have hB : (β_ W (z ⊗ U)).hom ≫ a ▷ W ≫ v =
          (𝟙 W ⊗ₘ a) ≫ (β_ W B).hom ≫ v := by
        simpa only [tensorHom_id] using (braiding_naturality_assoc (𝟙 W) a v).symm
      have hEnd :
          (𝟙 W ⊗ₘ a) ≫ (β_ W B).hom ≫ v =
            (𝟙 W ⊗ₘ rightStrengthComponent d F X) ≫ evaluationGen F k X := rfl
      exact hB.trans hEnd

/-- Full strength naturality and the actual evaluation cocone balance the original kernel. -/
theorem rightForwardGen_balanced (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) :
    EnrichedDayKernel.Balanced d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k (rightForwardGen d F k) := by
  intro X Y
  let W : V := (Y.1 ⊗ Y.2) ⟶[V] k
  let W' : V := (X.1 ⊗ X.2) ⟶[V] k
  let H : V := X ⟶[V] Y
  let A : V := F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2)
  let A' : V := F.obj Y.1 ⊗ (𝟙_ I ⟶[V] Y.2)
  let B : V := F.obj (X.1 ⊗ X.2)
  let B' : V := F.obj (Y.1 ⊗ Y.2)
  let s : A ⟶ B := rightStrengthComponent d F X
  let s' : A' ⟶ B' := rightStrengthComponent d F Y
  let m : W ⊗ H ⟶ W' := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map (Opposite.op Y) (Opposite.op X))
  let h : A ⊗ H ⟶ A' := MonoidalClosed.uncurry
    ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map X Y)
  let h' : B ⊗ H ⟶ B' := MonoidalClosed.uncurry
    ((d.tensorEnrichedFunctor.comp V F).map X Y)
  let r : W ⊗ (H ⊗ A) ⟶ W ⊗ (H ⊗ B) := W ◁ (𝟙 H ⊗ₘ s)
  have hWeight :
      ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫ (𝟙 W' ⊗ₘ s) =
        r ≫ (α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B) := by
    have ha :
        (𝟙 W ⊗ₘ (𝟙 H ⊗ₘ s)) ≫ (α_ W H B).inv =
          (α_ W H A).inv ≫ ((𝟙 W ⊗ₘ 𝟙 H) ⊗ₘ s) :=
      associator_inv_naturality (𝟙 W) (𝟙 H) s
    have h := congrArg (fun f => f ≫ (m ⊗ₘ 𝟙 B)) ha
    simp only [Category.assoc, tensorHom_comp_tensorHom, id_tensorHom_id,
      Category.id_comp, Category.comp_id] at h
    have hR : (α_ W H A).inv ≫ (m ⊗ₘ s) =
        r ≫ (α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B) := by
      simpa only [r, id_tensorHom, Category.assoc] using h.symm
    have hFactor : (m ⊗ₘ 𝟙 A) ≫ (𝟙 W' ⊗ₘ s) = m ⊗ₘ s := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact (Category.assoc (α_ W H A).inv (m ⊗ₘ 𝟙 A) (𝟙 W' ⊗ₘ s)).trans
      ((congrArg (fun f => (α_ W H A).inv ≫ f) hFactor).trans hR)
  have hNatural : h ≫ s' = (s ⊗ₘ 𝟙 H) ≫ h' :=
    rightStrength_natural d F X Y
  have hDiagram :
      (β_ H A).hom ≫ h ≫ s' =
        (𝟙 H ⊗ₘ s) ≫ (β_ H B).hom ≫ h' := by
    have hN : (β_ H A).hom ≫ h ≫ s' = (β_ H A).hom ≫ (s ⊗ₘ 𝟙 H) ≫ h' := by
      simpa only [Category.assoc] using
        congrArg (fun f => (β_ H A).hom ≫ f) hNatural
    exact hN.trans (braiding_naturality_assoc (𝟙 H) s h').symm
  have hEvaluation :
      ((α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X =
        W ◁ ((β_ H B).hom ≫ h') ≫ evaluationGen F k Y := by
    have hM : m =
        W ◁ d.tensorMap X.1 Y.1 X.2 Y.2 ≫
          (β_ W ((X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2))).hom ≫
          eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k := by
      exact EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k X Y
    calc
      _ = ((α_ W H B).inv ≫
          ((W ◁ d.tensorMap X.1 Y.1 X.2 Y.2 ≫
            (β_ W ((X.1 ⊗ X.2) ⟶[V] (Y.1 ⊗ Y.2))).hom ≫
            eComp V (X.1 ⊗ X.2) (Y.1 ⊗ Y.2) k) ⊗ₘ 𝟙 B)) ≫
            evaluationGen F k X :=
        congrArg (fun f : W ⊗ H ⟶ W' =>
          ((α_ W H B).inv ≫ (f ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X) hM
      _ = _ := evaluationGen_balanced d F k X Y
  change ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫ rightForwardGen d F k X =
    W ◁ ((β_ H A).hom ≫ h) ≫ rightForwardGen d F k Y
  rw [rightForwardGen_eq_strength, rightForwardGen_eq_strength]
  change ((α_ W H A).inv ≫ (m ⊗ₘ 𝟙 A)) ≫
      (𝟙 W' ⊗ₘ s) ≫ evaluationGen F k X =
    W ◁ ((β_ H A).hom ≫ h) ≫ (𝟙 W ⊗ₘ s') ≫ evaluationGen F k Y
  calc
    _ = r ≫ ((α_ W H B).inv ≫ (m ⊗ₘ 𝟙 B)) ≫ evaluationGen F k X := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ evaluationGen F k X) hWeight
    _ = r ≫ W ◁ ((β_ H B).hom ≫ h') ≫ evaluationGen F k Y := by
      simpa only [Category.assoc] using congrArg (fun f => r ≫ f) hEvaluation
    _ = _ := by
      simpa only [r, id_tensorHom, whiskerLeft_comp, Category.assoc] using
        congrArg (fun f => W ◁ f ≫ evaluationGen F k Y) hDiagram.symm

/-- The full relation moving the second coefficient index to the actual unit. -/
private def rightRelationOne (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k X ⟶
      EnrichedDayKernel.relations d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k ((X.1, 𝟙_ I), X) :=
  ((X.1 ⊗ X.2) ⟶[V] k) ◁
    ((β_ (F.obj X.1) (𝟙_ I ⟶[V] X.2)).hom ≫
      (((λ_ (𝟙_ I ⟶[V] X.2)).inv ≫ (eId V X.1 ⊗ₘ 𝟙 (𝟙_ I ⟶[V] X.2))) ⊗ₘ
        ((ρ_ (F.obj X.1)).inv ≫ (𝟙 (F.obj X.1) ⊗ₘ eId V (𝟙_ I)))))

/-- The full relation moving the first index to output through the actual rho. -/
private def rightRelationTwo (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (i k : I) :
    ((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ F.obj i ⟶
      EnrichedDayKernel.relations d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k ((i, 𝟙_ I), (k, 𝟙_ I)) :=
  (λ_ (((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ F.obj i)).inv ≫
    (eHomEquiv V (ρ_ k).hom ⊗ₘ
      (((ρ_ ((i ⊗ 𝟙_ I) ⟶[V] k)).inv ≫
          (eHomWhiskerRight V (ρ_ i).inv k ⊗ₘ eId V (𝟙_ I))) ⊗ₘ
        ((ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V (𝟙_ I)))))

/-- The actual second-coordinate collapse in the contravariant weight. -/
private def rightCollapseBase (d : EnrichedMonoidalCategoryData V I) (k : I) (X : I × I) :
    ((X.1 ⊗ X.2) ⟶[V] k) ⊗ (𝟙_ I ⟶[V] X.2) ⟶ ((X.1 ⊗ 𝟙_ I) ⟶[V] k) :=
  ((X.1 ⊗ X.2) ⟶[V] k) ◁ rightTensorHom d X.1 X.2 ≫
    (β_ ((X.1 ⊗ X.2) ⟶[V] k) ((X.1 ⊗ 𝟙_ I) ⟶[V] (X.1 ⊗ X.2))).hom ≫
    eComp V (X.1 ⊗ 𝟙_ I) (X.1 ⊗ X.2) k

/-- The second relation's literal whole-object evaluation. -/
private def rightContraction (F : EnrichedFunctor V I V) (i k : I) :
    ((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ F.obj i ⟶ F.obj k :=
  (β_ ((i ⊗ 𝟙_ I) ⟶[V] k) (F.obj i)).hom ≫
    F.obj i ◁ eHomWhiskerRight V (ρ_ i).inv k ≫ MonoidalClosed.uncurry (F.map i k)

/-- The complete right relation coefficient is restored by actual enriched identities. -/
private theorem rightRelationOne_coeffIdentity (F : EnrichedFunctor V I V) (i j : I) :
    (β_ (F.obj i) (𝟙_ I ⟶[V] j)).hom ≫
      (((λ_ (𝟙_ I ⟶[V] j)).inv ≫ (eId V i ⊗ₘ 𝟙 (𝟙_ I ⟶[V] j))) ⊗ₘ
        ((ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V (𝟙_ I)))) ≫
      (β_ ((i ⟶[V] i) ⊗ (𝟙_ I ⟶[V] j))
        (F.obj i ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).hom ≫
      MonoidalClosed.uncurry
        ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (i, 𝟙_ I) (i, j)) =
      𝟙 (F.obj i ⊗ (𝟙_ I ⟶[V] j)) := by
  let A : V := F.obj i
  let U : V := 𝟙_ I ⟶[V] j
  let H : V := i ⟶[V] i
  let E : V := 𝟙_ I ⟶[V] 𝟙_ I
  let p : U ⟶ H ⊗ U := (λ_ U).inv ≫ (eId V i ⊗ₘ 𝟙 U)
  let q : A ⟶ A ⊗ E := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let f : A ⊗ H ⟶ A := MonoidalClosed.uncurry (F.map i i)
  let g : E ⊗ U ⟶ U := eComp V (𝟙_ I) (𝟙_ I) j
  have hSwap :
      (β_ A U).hom ≫ (p ⊗ₘ q) ≫ (β_ (H ⊗ U) (A ⊗ E)).hom = q ⊗ₘ p := by
    simpa only [Category.assoc, SymmetricCategory.symmetry_assoc, Category.id_comp] using
      congrArg (fun v => (β_ A U).hom ≫ v) (braiding_naturality p q)
  have hExternal :
      MonoidalClosed.uncurry
          ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (i, 𝟙_ I) (i, j)) =
        tensorμ A E H U ≫ (f ⊗ₘ g) := by
    rw [EnrichedFunctor.externalTensor_uncurry, GradedYoneda.representable_uncurry]
  have hE := congrArg
    (fun v : (A ⊗ E) ⊗ (H ⊗ U) ⟶ A ⊗ U =>
      (β_ A U).hom ≫ (p ⊗ₘ q) ≫ (β_ (H ⊗ U) (A ⊗ E)).hom ≫ v) hExternal
  let pF : A ⟶ A ⊗ H := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V i)
  let pU : U ⟶ E ⊗ U := (λ_ U).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 U)
  have hF : pF ≫ f = 𝟙 A := by
    simpa only [pF, f, A, H, Category.assoc] using action_id F i
  have hU : pU ≫ g = 𝟙 U := by
    simpa only [pU, g, U, E, tensorHom_id, Category.assoc] using e_id_comp V (𝟙_ I) j
  have hMu : (q ⊗ₘ p) ≫ tensorμ A E H U = pF ⊗ₘ pU :=
    tensorMu_middle_insert (P := A) (Q := U) (eId V (𝟙_ I)) (eId V i)
  have hWord :
      (β_ A U).hom ≫ (p ⊗ₘ q) ≫ (β_ (H ⊗ U) (A ⊗ E)).hom ≫
          (tensorμ A E H U ≫ (f ⊗ₘ g)) = 𝟙 (A ⊗ U) := by
    calc
      _ = (q ⊗ₘ p) ≫ tensorμ A E H U ≫ (f ⊗ₘ g) := by
        simpa only [Category.assoc] using
          congrArg (fun v => v ≫ tensorμ A E H U ≫ (f ⊗ₘ g)) hSwap
      _ = (pF ⊗ₘ pU) ≫ (f ⊗ₘ g) := by
        exact (Category.assoc (q ⊗ₘ p) (tensorμ A E H U) (f ⊗ₘ g)).symm.trans
          (congrArg (fun v => v ≫ (f ⊗ₘ g)) hMu)
      _ = _ := by rw [tensorHom_comp_tensorHom, hF, hU, id_tensorHom_id]
  exact hE.trans hWord

/-- The full diagram leg of the first right relation is the original integrand identity. -/
private theorem rightRelationOne_diagramFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    rightRelationOne d F k X ≫ ((X.1 ⊗ X.2) ⟶[V] k) ◁
        ((β_ ((X.1 ⟶[V] X.1) ⊗ (𝟙_ I ⟶[V] X.2))
          (F.obj X.1 ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).hom ≫
          MonoidalClosed.uncurry
            ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (X.1, 𝟙_ I) X)) =
      𝟙 (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k X) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let A : V := F.obj X.1
  let U : V := 𝟙_ I ⟶[V] X.2
  let H : V := X.1 ⟶[V] X.1
  let E : V := 𝟙_ I ⟶[V] 𝟙_ I
  let p : U ⟶ H ⊗ U := (λ_ U).inv ≫ (eId V X.1 ⊗ₘ 𝟙 U)
  let q : A ⟶ A ⊗ E := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let l : A ⊗ U ⟶ (H ⊗ U) ⊗ (A ⊗ E) := (β_ A U).hom ≫ (p ⊗ₘ q)
  let c : (H ⊗ U) ⊗ (A ⊗ E) ⟶ A ⊗ U :=
    (β_ (H ⊗ U) (A ⊗ E)).hom ≫ MonoidalClosed.uncurry
      ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (X.1, 𝟙_ I) X)
  have hData : rightRelationOne d F k X = W ◁ l := rfl
  have hC : l ≫ c = 𝟙 (A ⊗ U) := by
    exact (Category.assoc (β_ A U).hom (p ⊗ₘ q) c).trans
      (rightRelationOne_coeffIdentity F X.1 X.2)
  have hW : W ◁ l ≫ W ◁ c = 𝟙 (W ⊗ (A ⊗ U)) :=
    (whiskerLeft_comp W l c).symm.trans
      ((congrArg (fun v => W ◁ v) hC).trans (whiskerLeft_id W (A ⊗ U)))
  exact (congrArg (fun v => v ≫ W ◁ c) hData).trans hW

/-- The first right weight leg is exactly the actual identity-inserting collapse. -/
private theorem rightRelationOne_weightFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    rightRelationOne d F k X ≫
        (α_ ((X.1 ⊗ X.2) ⟶[V] k) ((X.1 ⟶[V] X.1) ⊗ (𝟙_ I ⟶[V] X.2))
          (F.obj X.1 ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).inv ≫
        (MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op X) (Opposite.op (X.1, 𝟙_ I))) ⊗ₘ
          𝟙 (F.obj X.1 ⊗ (𝟙_ I ⟶[V] 𝟙_ I))) =
      (((X.1 ⊗ X.2) ⟶[V] k) ◁ (β_ (F.obj X.1) (𝟙_ I ⟶[V] X.2)).hom) ≫
        (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.2) (F.obj X.1)).inv ≫
        (rightCollapseBase d k X ⊗ₘ
          ((ρ_ (F.obj X.1)).inv ≫ (𝟙 (F.obj X.1) ⊗ₘ eId V (𝟙_ I)))) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let A : V := F.obj X.1
  let P : V := (X.1 ⟶[V] X.1) ⊗ U
  let C : V := A ⊗ (𝟙_ I ⟶[V] 𝟙_ I)
  let W₀ : V := (X.1 ⊗ 𝟙_ I) ⟶[V] k
  let H : V := (X.1 ⊗ 𝟙_ I) ⟶[V] (X.1 ⊗ X.2)
  let p : U ⟶ P := (λ_ U).inv ≫ (eId V X.1 ⊗ₘ 𝟙 U)
  let q : A ⟶ C := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let t : P ⟶ H := d.tensorMap X.1 X.1 (𝟙_ I) X.2
  let c : H ⊗ W ⟶ W₀ := eComp V (X.1 ⊗ 𝟙_ I) (X.1 ⊗ X.2) k
  let m : W ⊗ P ⟶ W₀ := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
      (Opposite.op X) (Opposite.op (X.1, 𝟙_ I)))
  have hM : m = W ◁ t ≫ (β_ W H).hom ≫ c :=
    EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k (X.1, 𝟙_ I) X
  have hT : p ≫ t = rightTensorHom d X.1 X.2 :=
    Category.assoc (λ_ U).inv (eId V X.1 ⊗ₘ 𝟙 U) t
  have hCollapse : W ◁ p ≫ m = rightCollapseBase d k X := by
    calc
      _ = W ◁ p ≫ W ◁ t ≫ (β_ W H).hom ≫ c := congrArg (fun f => W ◁ p ≫ f) hM
      _ = W ◁ (p ≫ t) ≫ (β_ W H).hom ≫ c := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (β_ W H).hom ≫ c) (whiskerLeft_comp W p t).symm
      _ = _ := congrArg (fun f => W ◁ f ≫ (β_ W H).hom ≫ c) hT
  let b : W ⊗ (A ⊗ U) ⟶ W ⊗ (U ⊗ A) := W ◁ (β_ A U).hom
  have hData : rightRelationOne d F k X = b ≫ W ◁ (p ⊗ₘ q) := by
    exact whiskerLeft_comp W (β_ A U).hom (p ⊗ₘ q)
  have hAlpha : W ◁ (p ⊗ₘ q) ≫ (α_ W P C).inv =
      (α_ W U A).inv ≫ ((W ◁ p) ⊗ₘ q) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 W) p q
  have hFactor : ((W ◁ p) ⊗ₘ q) ≫ (m ⊗ₘ 𝟙 C) =
      (W ◁ p ≫ m) ⊗ₘ q := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  let h := W ◁ (p ⊗ₘ q)
  let a₀ := (α_ W P C).inv
  let a₁ := (α_ W U A).inv
  let u := (W ◁ p) ⊗ₘ q
  let v := m ⊗ₘ 𝟙 C
  have h₁ : rightRelationOne d F k X ≫ a₀ ≫ v = b ≫ h ≫ a₀ ≫ v :=
    (congrArg (fun f => f ≫ a₀ ≫ v) hData).trans (Category.assoc b h (a₀ ≫ v))
  have h₂ : b ≫ h ≫ a₀ ≫ v = b ≫ a₁ ≫ u ≫ v :=
    (congrArg (fun f => b ≫ f) (Category.assoc h a₀ v).symm).trans
      ((congrArg (fun f => b ≫ f ≫ v) hAlpha).trans
        (congrArg (fun f => b ≫ f) (Category.assoc a₁ u v)))
  have h₃ : b ≫ a₁ ≫ u ≫ v = b ≫ a₁ ≫ ((W ◁ p ≫ m) ⊗ₘ q) :=
    congrArg (fun f => b ≫ a₁ ≫ f) hFactor
  have h₄ : b ≫ a₁ ≫ ((W ◁ p ≫ m) ⊗ₘ q) =
      b ≫ a₁ ≫ (rightCollapseBase d k X ⊗ₘ q) :=
    congrArg (fun f => b ≫ a₁ ≫ (f ⊗ₘ q)) hCollapse
  exact h₁.trans (h₂.trans (h₃.trans h₄))

omit [MonoidalClosed V] in
/-- Two actual right point insertions commute with the tensor interchange. -/
private theorem tensorMu_right_insert {A B R S : V}
    (e : 𝟙_ V ⟶ R) (f : 𝟙_ V ⟶ S) :
    (((ρ_ A).inv ≫ (𝟙 A ⊗ₘ e)) ⊗ₘ ((ρ_ B).inv ≫ (𝟙 B ⊗ₘ f))) ≫ tensorμ A R B S =
      (ρ_ (A ⊗ B)).inv ≫
        (𝟙 (A ⊗ B) ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ f))) := by
  have hUnit :
      ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫ tensorμ A (𝟙_ V) B (𝟙_ V) =
        (ρ_ (A ⊗ B)).inv ≫ (A ⊗ B) ◁ (λ_ (𝟙_ V)).inv := by
    apply (cancel_mono ((A ⊗ B) ◁ (λ_ (𝟙_ V)).hom ≫ (ρ_ (A ⊗ B)).hom)).1
    calc
      _ = ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫ ((ρ_ A).hom ⊗ₘ (ρ_ B).hom) := by
        simpa only [Category.assoc] using
          congrArg (fun v => ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫ v)
            (rightUnitor_monoidal A B).symm
      _ = 𝟙 (A ⊗ B) := by
        rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]
      _ = _ := by
        simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
          whiskerLeft_id, Category.id_comp]
  calc
    _ = ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫
        ((𝟙 A ⊗ₘ e) ⊗ₘ (𝟙 B ⊗ₘ f)) ≫ tensorμ A R B S := by
      simpa only [Category.assoc] using
        congrArg (fun v => v ≫ tensorμ A R B S)
          (tensorHom_comp_tensorHom (ρ_ A).inv (ρ_ B).inv
            (𝟙 A ⊗ₘ e) (𝟙 B ⊗ₘ f)).symm
    _ = ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫ tensorμ A (𝟙_ V) B (𝟙_ V) ≫
        (𝟙 (A ⊗ B) ⊗ₘ (e ⊗ₘ f)) := by
      simpa only [Category.assoc, id_tensorHom_id] using
        congrArg (fun v => ((ρ_ A).inv ⊗ₘ (ρ_ B).inv) ≫ v)
          (tensorμ_natural (𝟙 A) e (𝟙 B) f)
    _ = (ρ_ (A ⊗ B)).inv ≫ (A ⊗ B) ◁ (λ_ (𝟙_ V)).inv ≫
        (𝟙 (A ⊗ B) ⊗ₘ (e ⊗ₘ f)) := by
      simpa only [Category.assoc] using
        congrArg (fun v => v ≫ (𝟙 (A ⊗ B) ⊗ₘ (e ⊗ₘ f))) hUnit
    _ = _ := by rw [whiskerLeft_comp_tensorHom]

/-- The second right weight contraction is the actual whole-hom rho identity. -/
private theorem rightRelationTwo_weightBase (d : EnrichedMonoidalCategoryData V I) (i k : I) :
    (λ_ ((i ⊗ 𝟙_ I) ⟶[V] k)).inv ≫
        (eHomEquiv V (ρ_ k).hom ⊗ₘ
          ((ρ_ ((i ⊗ 𝟙_ I) ⟶[V] k)).inv ≫
            (eHomWhiskerRight V (ρ_ i).inv k ⊗ₘ eId V (𝟙_ I)))) ≫
        MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (k, 𝟙_ I)) (Opposite.op (i, 𝟙_ I))) =
      𝟙 ((i ⊗ 𝟙_ I) ⟶[V] k) := by
  let W : V := (i ⊗ 𝟙_ I) ⟶[V] k
  let H : V := i ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let Z : V := (k ⊗ 𝟙_ I) ⟶[V] k
  let P : V := (i ⊗ 𝟙_ I) ⟶[V] (k ⊗ 𝟙_ I)
  let m : W ⟶ H := eHomWhiskerRight V (ρ_ i).inv k
  let e : 𝟙_ V ⟶ Z := eHomEquiv V (ρ_ k).hom
  let p : W ⟶ H ⊗ U := (ρ_ W).inv ≫ (m ⊗ₘ eId V (𝟙_ I))
  let t : H ⊗ U ⟶ P := d.tensorMap i k (𝟙_ I) (𝟙_ I)
  let c : P ⊗ Z ⟶ W := eComp V (i ⊗ 𝟙_ I) (k ⊗ 𝟙_ I) k
  let a : Z ⊗ (H ⊗ U) ⟶ W := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
      (Opposite.op (k, 𝟙_ I)) (Opposite.op (i, 𝟙_ I)))
  have hM : a = Z ◁ t ≫ (β_ Z P).hom ≫ c :=
    EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k (i, 𝟙_ I) (k, 𝟙_ I)
  have hMap : p ≫ t = m ≫ rightUnitTensorMap d i k := by
    simpa only [rightUnitTensorMap, p, t, id_tensorHom, Category.assoc] using
      rightUnitor_inv_comp_tensorHom_assoc m (eId V (𝟙_ I)) t
  let q := m ≫ rightUnitTensorMap d i k
  have hTensor : (e ⊗ₘ p) ≫ Z ◁ t = e ⊗ₘ (p ≫ t) :=
    tensorHom_comp_whiskerLeft e p t
  have hBeta : (λ_ W).inv ≫ (e ⊗ₘ q) ≫ (β_ Z P).hom =
      (ρ_ W).inv ≫ (q ⊗ₘ e) := by
    simpa only [Category.assoc, leftUnitor_inv_braiding_assoc] using
      congrArg (fun f => (λ_ W).inv ≫ f) (braiding_naturality e q)
  have hLeft : (ρ_ W).inv ≫ (q ⊗ₘ e) ≫ c =
      q ≫ eHomWhiskerLeft V (i ⊗ 𝟙_ I) (ρ_ k).hom := by
    simpa only [eHomWhiskerLeft, e, id_tensorHom, Category.assoc] using
      rightUnitor_inv_comp_tensorHom_assoc q e c
  have hRight : m ≫ eHomWhiskerRight V (ρ_ i).hom k = 𝟙 W := by
    simp only [m, W, ← eHomWhiskerRight_comp, Iso.hom_inv_id, eHomWhiskerRight_id]
  have hPure : (λ_ W).inv ≫ (e ⊗ₘ p) ≫ (Z ◁ t ≫ (β_ Z P).hom ≫ c) = 𝟙 W := by
    calc
      _ = (λ_ W).inv ≫ (e ⊗ₘ (p ≫ t)) ≫ (β_ Z P).hom ≫ c := by
        simpa only [Category.assoc] using
          congrArg (fun f => (λ_ W).inv ≫ f ≫ (β_ Z P).hom ≫ c) hTensor
      _ = (λ_ W).inv ≫ (e ⊗ₘ q) ≫ (β_ Z P).hom ≫ c :=
        congrArg (fun f => (λ_ W).inv ≫ (e ⊗ₘ f) ≫ (β_ Z P).hom ≫ c) hMap
      _ = (ρ_ W).inv ≫ (q ⊗ₘ e) ≫ c := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ c) hBeta
      _ = q ≫ eHomWhiskerLeft V (i ⊗ 𝟙_ I) (ρ_ k).hom := hLeft
      _ = m ≫ eHomWhiskerRight V (ρ_ i).hom k := by
        simpa only [q, Category.assoc] using
          congrArg (fun f => m ≫ f) (rightUnitTensorMap_natural d i k)
      _ = _ := hRight
  exact (congrArg (fun f : Z ⊗ (H ⊗ U) ⟶ W =>
    (λ_ W).inv ≫ (e ⊗ₘ p) ≫ f) hM).trans hPure

/-- The complete second right coefficient relation inserts the original unit identity. -/
private theorem rightRelationTwo_coeffFace (F : EnrichedFunctor V I V)
    (i k : I) {W : V} (m : W ⟶ (i ⟶[V] k)) :
    (((ρ_ W).inv ≫ (m ⊗ₘ eId V (𝟙_ I))) ⊗ₘ
        ((ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V (𝟙_ I)))) ≫
      (β_ ((i ⟶[V] k) ⊗ (𝟙_ I ⟶[V] 𝟙_ I))
        (F.obj i ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).hom ≫
      MonoidalClosed.uncurry
        ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (i, 𝟙_ I) (k, 𝟙_ I)) =
      (ρ_ (W ⊗ F.obj i)).inv ≫
        (((β_ W (F.obj i)).hom ≫ F.obj i ◁ m ≫ MonoidalClosed.uncurry (F.map i k)) ⊗ₘ
          eId V (𝟙_ I)) := by
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let A : V := F.obj i
  let H : V := i ⟶[V] k
  let e : 𝟙_ V ⟶ U := eId V (𝟙_ I)
  let l : A ⟶ A ⊗ U := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ e)
  let lW : W ⟶ W ⊗ U := (ρ_ W).inv ≫ (𝟙 W ⊗ₘ e)
  let p : W ⟶ H ⊗ U := (ρ_ W).inv ≫ (m ⊗ₘ e)
  let c : U ⊗ U ⟶ U := eComp V (𝟙_ I) (𝟙_ I) (𝟙_ I)
  let q : A ⊗ H ⟶ F.obj k := MonoidalClosed.uncurry (F.map i k)
  let delta : 𝟙_ V ⟶ U ⊗ U := (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ e)
  have hId : delta ≫ c = e := by
    simpa only [delta, e, c, eHomEquiv_id, Category.id_comp, Category.assoc] using
      (eHomEquiv_comp V (𝟙 (𝟙_ I)) (𝟙 (𝟙_ I))).symm
  have hp : p = lW ≫ (m ⊗ₘ 𝟙 U) := by
    simp only [p, lW, tensorHom_comp_tensorHom, Category.assoc,
      Category.id_comp, Category.comp_id]
  let b := 𝟙 (A ⊗ U) ⊗ₘ (m ⊗ₘ 𝟙 U)
  let t := (𝟙 A ⊗ₘ m) ⊗ₘ 𝟙 (U ⊗ U)
  have hMu : b ≫ tensorμ A U H U = tensorμ A U W U ≫ t := by
    simpa only [b, t, id_tensorHom_id] using tensorμ_natural (𝟙 A) (𝟙 U) m (𝟙 U)
  have hFactor : l ⊗ₘ p = (l ⊗ₘ lW) ≫ b :=
    (congrArg (fun f => l ⊗ₘ f) hp).trans (by
      simpa only [b, Category.comp_id] using
        (tensorHom_comp_tensorHom l lW (𝟙 (A ⊗ U)) (m ⊗ₘ 𝟙 U)).symm)
  have hDouble : (l ⊗ₘ lW) ≫ tensorμ A U W U =
      (ρ_ (A ⊗ W)).inv ≫ (𝟙 (A ⊗ W) ⊗ₘ delta) := tensorMu_right_insert e e
  have hCollect : (𝟙 (A ⊗ W) ⊗ₘ delta) ≫ t ≫ (q ⊗ₘ c) =
      (((𝟙 A ⊗ₘ m) ≫ q) ⊗ₘ e) := by
    simp only [t, tensorHom_comp_tensorHom, Category.id_comp, hId]
  have hInsert : (l ⊗ₘ p) ≫ tensorμ A U H U ≫ (q ⊗ₘ c) =
      (ρ_ (A ⊗ W)).inv ≫ (((𝟙 A ⊗ₘ m) ≫ q) ⊗ₘ e) := by
    calc
      _ = (l ⊗ₘ lW) ≫ b ≫ tensorμ A U H U ≫ (q ⊗ₘ c) := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ tensorμ A U H U ≫ (q ⊗ₘ c)) hFactor
      _ = (l ⊗ₘ lW) ≫ tensorμ A U W U ≫ t ≫ (q ⊗ₘ c) := by
        simpa only [Category.assoc] using
          congrArg (fun f => (l ⊗ₘ lW) ≫ f ≫ (q ⊗ₘ c)) hMu
      _ = (ρ_ (A ⊗ W)).inv ≫ (𝟙 (A ⊗ W) ⊗ₘ delta) ≫ t ≫ (q ⊗ₘ c) := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ t ≫ (q ⊗ₘ c)) hDouble
      _ = _ := congrArg (fun f => (ρ_ (A ⊗ W)).inv ≫ f) hCollect
  have hExternal : MonoidalClosed.uncurry
      ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (i, 𝟙_ I) (k, 𝟙_ I)) =
        tensorμ A U H U ≫ (q ⊗ₘ c) := by
    rw [EnrichedFunctor.externalTensor_uncurry, GradedYoneda.representable_uncurry]
  have hE := congrArg
    (fun f : (A ⊗ U) ⊗ (H ⊗ U) ⟶ F.obj k ⊗ U =>
      (p ⊗ₘ l) ≫ (β_ (H ⊗ U) (A ⊗ U)).hom ≫ f) hExternal
  have hSwap : (p ⊗ₘ l) ≫ (β_ (H ⊗ U) (A ⊗ U)).hom =
      (β_ W A).hom ≫ (l ⊗ₘ p) := braiding_naturality p l
  let v := (𝟙 A ⊗ₘ m) ≫ q
  have hRho : (β_ W A).hom ≫ (ρ_ (A ⊗ W)).inv ≫ (v ⊗ₘ e) =
      (ρ_ (W ⊗ A)).inv ≫ (((β_ W A).hom ≫ v) ⊗ₘ e) := by
    simpa only [Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.id_comp] using
      congrArg (fun f => f ≫ (v ⊗ₘ e)) (rightUnitor_inv_naturality (β_ W A).hom)
  have hWord : (p ⊗ₘ l) ≫ (β_ (H ⊗ U) (A ⊗ U)).hom ≫
      (tensorμ A U H U ≫ (q ⊗ₘ c)) =
        (ρ_ (W ⊗ A)).inv ≫ (((β_ W A).hom ≫ A ◁ m ≫ q) ⊗ₘ e) := by
    calc
      _ = (β_ W A).hom ≫ (l ⊗ₘ p) ≫ tensorμ A U H U ≫ (q ⊗ₘ c) := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ tensorμ A U H U ≫ (q ⊗ₘ c)) hSwap
      _ = (β_ W A).hom ≫ (ρ_ (A ⊗ W)).inv ≫ (v ⊗ₘ e) :=
        congrArg (fun f => (β_ W A).hom ≫ f) hInsert
      _ = _ := by simpa only [v, id_tensorHom, Category.assoc] using hRho
  exact hE.trans hWord

/-- The second right diagram leg is the literal contraction followed by original insertion. -/
private theorem rightRelationTwo_diagramFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (i k : I) :
    rightRelationTwo d F i k ≫ ((k ⊗ 𝟙_ I) ⟶[V] k) ◁
        ((β_ ((i ⟶[V] k) ⊗ (𝟙_ I ⟶[V] 𝟙_ I))
          (F.obj i ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).hom ≫ MonoidalClosed.uncurry
            ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map
              (i, 𝟙_ I) (k, 𝟙_ I))) =
      rightContraction F i k ≫ (λ_ (F.obj k)).inv ≫
        (eHomEquiv V (ρ_ k).hom ⊗ₘ
          ((ρ_ (F.obj k)).inv ≫ (𝟙 (F.obj k) ⊗ₘ eId V (𝟙_ I)))) := by
  let W : V := (i ⊗ 𝟙_ I) ⟶[V] k
  let A : V := F.obj i
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let Z : V := (k ⊗ 𝟙_ I) ⟶[V] k
  let e : 𝟙_ V ⟶ Z := eHomEquiv V (ρ_ k).hom
  let f : 𝟙_ V ⟶ U := eId V (𝟙_ I)
  let m : W ⟶ (i ⟶[V] k) := eHomWhiskerRight V (ρ_ i).inv k
  let p : W ⟶ (i ⟶[V] k) ⊗ U := (ρ_ W).inv ≫ (m ⊗ₘ f)
  let q : A ⟶ A ⊗ U := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ f)
  let a : ((i ⟶[V] k) ⊗ U) ⊗ (A ⊗ U) ⟶ F.obj k ⊗ U :=
    (β_ ((i ⟶[V] k) ⊗ U) (A ⊗ U)).hom ≫ MonoidalClosed.uncurry
      ((F.externalTensor (GradedYoneda.representable (𝟙_ I))).map (i, 𝟙_ I) (k, 𝟙_ I))
  let c : W ⊗ A ⟶ F.obj k := rightContraction F i k
  let q' : F.obj k ⟶ F.obj k ⊗ U := (ρ_ (F.obj k)).inv ≫ (𝟙 (F.obj k) ⊗ₘ f)
  have hC : (p ⊗ₘ q) ≫ a = (ρ_ (W ⊗ A)).inv ≫ (c ⊗ₘ f) :=
    rightRelationTwo_coeffFace F i k m
  have hRight : (ρ_ (W ⊗ A)).inv ≫ (c ⊗ₘ f) = c ≫ q' := by
    simpa only [q', id_tensorHom, Category.assoc] using rightUnitor_inv_comp_tensorHom c f
  have hData : rightRelationTwo d F i k = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) := rfl
  have hTensor : (e ⊗ₘ (p ⊗ₘ q)) ≫ Z ◁ a = e ⊗ₘ ((p ⊗ₘ q) ≫ a) :=
    tensorHom_comp_whiskerLeft e (p ⊗ₘ q) a
  have hFinal : (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (c ≫ q')) =
      c ≫ (λ_ (F.obj k)).inv ≫ (e ⊗ₘ q') := by
    simpa only [tensorHom_comp_whiskerLeft, tensorHom_def, whiskerLeft_comp, Category.assoc] using
      congrArg (fun f => f ≫ Z ◁ q') (leftUnitor_inv_comp_tensorHom e c)
  calc
    _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) ≫ Z ◁ a :=
      (congrArg (fun f => f ≫ Z ◁ a) hData).trans
        (Category.assoc (λ_ (W ⊗ A)).inv (e ⊗ₘ (p ⊗ₘ q)) (Z ◁ a))
    _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ ((p ⊗ₘ q) ≫ a)) :=
      congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ f) hTensor
    _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ ((ρ_ (W ⊗ A)).inv ≫ (c ⊗ₘ f))) :=
      congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ f)) hC
    _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (c ≫ q')) :=
      congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ f)) hRight
    _ = _ := hFinal

/-- The second right weight face is precisely the original right-unit coefficient insertion. -/
private theorem rightRelationTwo_weightFace (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (i k : I) :
    rightRelationTwo d F i k ≫
        (α_ ((k ⊗ 𝟙_ I) ⟶[V] k) ((i ⟶[V] k) ⊗ (𝟙_ I ⟶[V] 𝟙_ I))
          (F.obj i ⊗ (𝟙_ I ⟶[V] 𝟙_ I))).inv ≫
        (MonoidalClosed.uncurry
          ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
            (Opposite.op (k, 𝟙_ I)) (Opposite.op (i, 𝟙_ I))) ⊗ₘ
          𝟙 (F.obj i ⊗ (𝟙_ I ⟶[V] 𝟙_ I))) =
      (𝟙 ((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ₘ
        ((ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V (𝟙_ I)))) := by
  let W : V := (i ⊗ 𝟙_ I) ⟶[V] k
  let A : V := F.obj i
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let Z : V := (k ⊗ 𝟙_ I) ⟶[V] k
  let P : V := (i ⟶[V] k) ⊗ U
  let C : V := A ⊗ U
  let e : 𝟙_ V ⟶ Z := eHomEquiv V (ρ_ k).hom
  let p : W ⟶ P := (ρ_ W).inv ≫ (eHomWhiskerRight V (ρ_ i).inv k ⊗ₘ eId V (𝟙_ I))
  let q : A ⟶ C := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let m : Z ⊗ P ⟶ W := MonoidalClosed.uncurry
    ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
      (Opposite.op (k, 𝟙_ I)) (Opposite.op (i, 𝟙_ I)))
  let n : W ⟶ Z ⊗ P := (λ_ W).inv ≫ (e ⊗ₘ p)
  have hData : rightRelationTwo d F i k = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) := rfl
  have hUnit : (λ_ (W ⊗ A)).inv ≫ (α_ (𝟙_ V) W A).inv = (λ_ W).inv ▷ A := by
    rw [leftUnitor_tensor_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hAlpha := congrArg (fun f => (λ_ (W ⊗ A)).inv ≫ f)
    (associator_inv_naturality e p q)
  have hU := congrArg (fun f => f ≫ ((e ⊗ₘ p) ⊗ₘ q)) hUnit
  have hTensor : (λ_ W).inv ▷ A ≫ ((e ⊗ₘ p) ⊗ₘ q) = n ⊗ₘ q := by
    simpa only [n, tensorHom_id, Category.id_comp] using
      tensorHom_comp_tensorHom (λ_ W).inv (𝟙 A) (e ⊗ₘ p) q
  have hFactor : rightRelationTwo d F i k ≫ (α_ Z P C).inv = n ⊗ₘ q := by
    calc
      _ = (λ_ (W ⊗ A)).inv ≫ (e ⊗ₘ (p ⊗ₘ q)) ≫ (α_ Z P C).inv :=
        (congrArg (fun f => f ≫ (α_ Z P C).inv) hData).trans
          (Category.assoc (λ_ (W ⊗ A)).inv (e ⊗ₘ (p ⊗ₘ q)) (α_ Z P C).inv)
      _ = (λ_ (W ⊗ A)).inv ≫ (α_ (𝟙_ V) W A).inv ≫ ((e ⊗ₘ p) ⊗ₘ q) := hAlpha
      _ = (λ_ W).inv ▷ A ≫ ((e ⊗ₘ p) ⊗ₘ q) := by
        simpa only [Category.assoc] using hU
      _ = _ := hTensor
  have hBase : n ≫ m = 𝟙 W :=
    (Category.assoc (λ_ W).inv (e ⊗ₘ p) m).trans (rightRelationTwo_weightBase d i k)
  have hCollect : (n ⊗ₘ q) ≫ (m ⊗ₘ 𝟙 C) = 𝟙 W ⊗ₘ q := by
    rw [tensorHom_comp_tensorHom, hBase, Category.comp_id]
  exact (Category.assoc (rightRelationTwo d F i k) (α_ Z P C).inv (m ⊗ₘ 𝟙 C)).symm.trans
    ((congrArg (fun f => f ≫ (m ⊗ₘ 𝟙 C)) hFactor).trans hCollect)

/-- The descended right component uses the actual original balanced family. -/
def rightComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k)] :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k ⟶ F.obj k :=
  EnrichedDayKernel.desc d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k
    (rightForwardGen d F k) (rightForwardGen_balanced d F k)

/-- Every generator has exactly the original right unitor formula. -/
@[reassoc]
theorem gen_rightComponent (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k)] (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k X ≫ rightComponent d F k =
      rightForwardGen d F k X :=
  EnrichedDayKernel.gen_desc d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k _ (rightForwardGen_balanced d F k) X

/-- The original right forward formula is the actual collapse followed by rho evaluation. -/
private theorem rightForwardGen_eq_contraction (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k : I) (X : I × I) :
    rightForwardGen d F k X =
      (((X.1 ⊗ X.2) ⟶[V] k) ◁ (β_ (F.obj X.1) (𝟙_ I ⟶[V] X.2)).hom) ≫
        (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.2) (F.obj X.1)).inv ≫
        (rightCollapseBase d k X ⊗ₘ 𝟙 (F.obj X.1)) ≫ rightContraction F X.1 k := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let A : V := F.obj X.1
  let B : I := X.1 ⊗ X.2
  let B₀ : I := X.1 ⊗ 𝟙_ I
  let P : V := B₀ ⟶[V] B
  let Q : V := X.1 ⟶[V] B
  let W₀ : V := B₀ ⟶[V] k
  let H : V := X.1 ⟶[V] k
  let t : U ⟶ P := rightTensorHom d X.1 X.2
  let m : W₀ ⟶ H := eHomWhiskerRight V (ρ_ X.1).inv k
  let m₀ : P ⟶ Q := eHomWhiskerRight V (ρ_ X.1).inv B
  let z : W ⊗ U ⟶ W₀ := rightCollapseBase d k X
  let c₀ : P ⊗ W ⟶ W₀ := eComp V B₀ B k
  let c₁ : Q ⊗ W ⟶ H := eComp V X.1 B k
  let theta : U ⟶ Q := rightUnitHom d X.1 X.2
  let c : U ⊗ W ⟶ H := (theta ⊗ₘ 𝟙 W) ≫ c₁
  let v : A ⊗ H ⟶ F.obj k := MonoidalClosed.uncurry (F.map X.1 k)
  let K : W ⊗ (A ⊗ U) ⟶ (W ⊗ U) ⊗ A :=
    W ◁ (β_ A U).hom ≫ (α_ W U A).inv
  have hComp : c₀ ≫ m = (m₀ ⊗ₘ 𝟙 W) ≫ c₁ := by
    simpa only [tensorHom_id] using eComp_eHomWhiskerRight V (ρ_ X.1).inv B k
  have hBraid : (β_ W P).hom ≫ (m₀ ⊗ₘ 𝟙 W) =
      W ◁ m₀ ≫ (β_ W Q).hom := by
    simpa only [id_tensorHom] using (braiding_naturality (𝟙 W) m₀).symm
  have hTheta : theta = t ≫ m₀ := rfl
  have hZ : z = W ◁ t ≫ (β_ W P).hom ≫ c₀ := rfl
  have hBase : z ≫ m = (β_ W U).hom ≫ c := by
    calc
      _ = W ◁ t ≫ (β_ W P).hom ≫ (c₀ ≫ m) := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ m) hZ
      _ = W ◁ t ≫ (β_ W P).hom ≫ (m₀ ⊗ₘ 𝟙 W) ≫ c₁ :=
        congrArg (fun f => W ◁ t ≫ (β_ W P).hom ≫ f) hComp
      _ = W ◁ t ≫ W ◁ m₀ ≫ (β_ W Q).hom ≫ c₁ := by
        simpa only [Category.assoc] using
          congrArg (fun f => W ◁ t ≫ f ≫ c₁) hBraid
      _ = W ◁ (t ≫ m₀) ≫ (β_ W Q).hom ≫ c₁ := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (β_ W Q).hom ≫ c₁) (whiskerLeft_comp W t m₀).symm
      _ = (β_ W U).hom ≫ ((t ≫ m₀) ⊗ₘ 𝟙 W) ≫ c₁ := by
        simpa only [id_tensorHom, Category.assoc] using
          congrArg (fun f => f ≫ c₁) (braiding_naturality (𝟙 W) (t ≫ m₀))
      _ = _ := congrArg (fun f => (β_ W U).hom ≫ (f ⊗ₘ 𝟙 W) ≫ c₁) hTheta.symm
  have hExpand :
      (α_ W U A).inv ≫ (β_ W U).hom ▷ A ≫ (β_ (U ⊗ W) A).hom =
        (β_ W (U ⊗ A)).hom ≫ (β_ U A).hom ▷ W ≫ (α_ A U W).hom := by
    rw [braiding_tensor_left_hom U W A]
    rw [← braiding_tensor_right_hom_assoc W U A]
  have hNatural : W ◁ (β_ A U).hom ≫ (β_ W (U ⊗ A)).hom =
      (β_ W (A ⊗ U)).hom ≫ (β_ A U).hom ▷ W := by
    simpa only [id_tensorHom, tensorHom_id] using braiding_naturality (𝟙 W) (β_ A U).hom
  have hShuffle :
      K ≫ (β_ W U).hom ▷ A ≫ (β_ (U ⊗ W) A).hom =
        (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom := by
    calc
      _ = W ◁ (β_ A U).hom ≫ (β_ W (U ⊗ A)).hom ≫
          (β_ U A).hom ▷ W ≫ (α_ A U W).hom := by
        simpa only [K, Category.assoc] using
          congrArg (fun f => W ◁ (β_ A U).hom ≫ f) hExpand
      _ = (β_ W (A ⊗ U)).hom ≫ (β_ A U).hom ▷ W ≫
          (β_ U A).hom ▷ W ≫ (α_ A U W).hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (β_ U A).hom ▷ W ≫ (α_ A U W).hom) hNatural
      _ = _ := by
        simp only [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
          id_whiskerRight, Category.id_comp]
  let g : W₀ ⊗ A ⟶ F.obj k := rightContraction F X.1 k
  have hG : g = (β_ W₀ A).hom ≫ A ◁ m ≫ v := rfl
  have hSwap : (β_ W₀ A).hom ≫ A ◁ m =
      (m ⊗ₘ 𝟙 A) ≫ (β_ H A).hom := by
    simpa only [id_tensorHom] using (braiding_naturality m (𝟙 A)).symm
  have hJoin : (z ⊗ₘ 𝟙 A) ≫ (β_ W₀ A).hom ≫ A ◁ m =
      ((z ≫ m) ⊗ₘ 𝟙 A) ≫ (β_ H A).hom := by
    rw [hSwap]
    simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]
  have hSplit : ((z ≫ m) ⊗ₘ 𝟙 A) = (β_ W U).hom ▷ A ≫ (c ⊗ₘ 𝟙 A) :=
    (congrArg (fun f => f ⊗ₘ 𝟙 A) hBase).trans (by
      simpa only [tensorHom_id, Category.id_comp] using
        (tensorHom_comp_tensorHom (β_ W U).hom (𝟙 A) c (𝟙 A)).symm)
  have hMove : (c ⊗ₘ 𝟙 A) ≫ (β_ H A).hom = (β_ (U ⊗ W) A).hom ≫ A ◁ c := by
    simpa only [id_tensorHom] using braiding_naturality c (𝟙 A)
  have hFData : rightForwardGen d F k X =
      (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom ≫ A ◁ c ≫ v := rfl
  have hWord : K ≫ (z ⊗ₘ 𝟙 A) ≫ g =
      (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom ≫ A ◁ c ≫ v := by
    calc
      _ = K ≫ (z ⊗ₘ 𝟙 A) ≫ (β_ W₀ A).hom ≫ A ◁ m ≫ v :=
        congrArg (fun f : W₀ ⊗ A ⟶ F.obj k => K ≫ (z ⊗ₘ 𝟙 A) ≫ f) hG
      _ = K ≫ ((z ≫ m) ⊗ₘ 𝟙 A) ≫ (β_ H A).hom ≫ v := by
        simpa only [Category.assoc] using congrArg (fun f => K ≫ f ≫ v) hJoin
      _ = K ≫ (β_ W U).hom ▷ A ≫ (c ⊗ₘ 𝟙 A) ≫ (β_ H A).hom ≫ v := by
        simpa only [Category.assoc] using congrArg (fun f => K ≫ f ≫ (β_ H A).hom ≫ v) hSplit
      _ = K ≫ (β_ W U).hom ▷ A ≫ (β_ (U ⊗ W) A).hom ≫ A ◁ c ≫ v := by
        simpa only [Category.assoc] using
          congrArg (fun f => K ≫ (β_ W U).hom ▷ A ≫ f ≫ v) hMove
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ A ◁ c ≫ v) hShuffle
  exact hFData.trans (hWord.symm.trans
    (Category.assoc (W ◁ (β_ A U).hom) (α_ W U A).inv ((z ⊗ₘ 𝟙 A) ≫ g)))

section RightParticularKernel

variable (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]

/-- The canonical unit-second generator retains the original identity insertion. -/
private def rightCanonicalGen (i : I) :
    ((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ F.obj i ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k :=
  (𝟙 ((i ⊗ 𝟙_ I) ⟶[V] k) ⊗ₘ
    ((ρ_ (F.obj i)).inv ≫ (𝟙 (F.obj i) ⊗ₘ eId V (𝟙_ I)))) ≫
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k (i, 𝟙_ I)

/-- The first actual right relation reduces every full generator to unit-second form. -/
private theorem rightGen_first_reduction (X : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k X =
      (((X.1 ⊗ X.2) ⟶[V] k) ◁ (β_ (F.obj X.1) (𝟙_ I ⟶[V] X.2)).hom) ≫
        (α_ ((X.1 ⊗ X.2) ⟶[V] k) (𝟙_ I ⟶[V] X.2) (F.obj X.1)).inv ≫
        (rightCollapseBase d k X ⊗ₘ 𝟙 (F.obj X.1)) ≫ rightCanonicalGen d F k X.1 := by
  let T := d.tensorEnrichedFunctor
  let R := GradedYoneda.representable (V := V) (𝟙_ I)
  let B : I × I := (X.1, 𝟙_ I)
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let A : V := F.obj X.1
  let W₀ : V := (X.1 ⊗ 𝟙_ I) ⟶[V] k
  let Q : V := EnrichedDayKernel.relations T F R k (B, X)
  let g₀ := EnrichedDayKernel.gen T F R k B
  let g := EnrichedDayKernel.gen T F R k X
  let r := rightRelationOne d F k X
  let w : Q ⟶ EnrichedDayKernel.objects T F R k B :=
    (α_ ((EnrichedDayKernel.weight T k).obj (Opposite.op X)) (B ⟶[V] X)
      ((F.externalTensor R).obj B)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight T k).map
        (Opposite.op X) (Opposite.op B)) ⊗ₘ 𝟙 ((F.externalTensor R).obj B))
  let q : Q ⟶ EnrichedDayKernel.objects T F R k X :=
    (EnrichedDayKernel.weight T k).obj (Opposite.op X) ◁
      ((β_ (B ⟶[V] X) ((F.externalTensor R).obj B)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor R).map B X))
  let c := rightCollapseBase d k X
  let i : A ⟶ A ⊗ (𝟙_ I ⟶[V] 𝟙_ I) :=
    (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let b : W ⊗ (A ⊗ U) ⟶ W ⊗ (U ⊗ A) := W ◁ (β_ A U).hom
  let a := (α_ W U A).inv
  let t₁ := c ⊗ₘ 𝟙 A
  let t₂ := 𝟙 W₀ ⊗ₘ i
  have h : r ≫ (w ≫ g₀) = r ≫ (q ≫ g) :=
    congrArg (fun f => r ≫ f) (EnrichedDayKernel.gen_balanced T F R k B X)
  have hGrouped : (r ≫ w) ≫ g₀ = (r ≫ q) ≫ g :=
    (Category.assoc r w g₀).trans (h.trans (Category.assoc r q g).symm)
  have hWeight : r ≫ w = b ≫ a ≫ (c ⊗ₘ i) :=
    rightRelationOne_weightFace d F k X
  have hDiagram : r ≫ q = 𝟙 (EnrichedDayKernel.objects T F R k X) :=
    rightRelationOne_diagramFace d F k X
  have hReduced : (b ≫ a ≫ (c ⊗ₘ i)) ≫ g₀ = g :=
    (congrArg (fun f => f ≫ g₀) hWeight).symm.trans
      (hGrouped.trans ((congrArg (fun f => f ≫ g) hDiagram).trans (Category.id_comp g)))
  have hFactor : c ⊗ₘ i = t₁ ≫ t₂ := by
    exact ((tensorHom_comp_tensorHom c (𝟙 A) (𝟙 W₀) i).trans
      ((congrArg (fun q => q ⊗ₘ (𝟙 A ≫ i)) (Category.comp_id c)).trans
        (congrArg (fun q => c ⊗ₘ q) (Category.id_comp i)))).symm
  have hFinal : (b ≫ a ≫ (c ⊗ₘ i)) ≫ g₀ =
      b ≫ a ≫ (rightCollapseBase d k X ⊗ₘ 𝟙 A) ≫ rightCanonicalGen d F k X.1 :=
    (Category.assoc b (a ≫ (c ⊗ₘ i)) g₀).trans
      (congrArg (fun f => b ≫ f)
        ((Category.assoc a (c ⊗ₘ i) g₀).trans
          ((congrArg (fun f => a ≫ (f ≫ g₀)) hFactor).trans
            (congrArg (fun f => a ≫ f) (Category.assoc t₁ t₂ g₀)))))
  exact hReduced.symm.trans hFinal

/-- The second actual right relation identifies its chosen generator with the original inverse. -/
private theorem rightGen_second_reduction (i : I) :
    rightCanonicalGen d F k i = rightContraction F i k ≫ rightInvComponent d F k := by
  let T := d.tensorEnrichedFunctor
  let R := GradedYoneda.representable (V := V) (𝟙_ I)
  let B : I × I := (i, 𝟙_ I)
  let C : I × I := (k, 𝟙_ I)
  let W : V := (i ⊗ 𝟙_ I) ⟶[V] k
  let A : V := F.obj i
  let Q : V := EnrichedDayKernel.relations T F R k (B, C)
  let g₀ := EnrichedDayKernel.gen T F R k B
  let g₁ := EnrichedDayKernel.gen T F R k C
  let r := rightRelationTwo d F i k
  let w : Q ⟶ EnrichedDayKernel.objects T F R k B :=
    (α_ ((EnrichedDayKernel.weight T k).obj (Opposite.op C)) (B ⟶[V] C)
      ((F.externalTensor R).obj B)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight T k).map
        (Opposite.op C) (Opposite.op B)) ⊗ₘ 𝟙 ((F.externalTensor R).obj B))
  let q : Q ⟶ EnrichedDayKernel.objects T F R k C :=
    (EnrichedDayKernel.weight T k).obj (Opposite.op C) ◁
      ((β_ (B ⟶[V] C) ((F.externalTensor R).obj B)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor R).map B C))
  let l : A ⟶ A ⊗ (𝟙_ I ⟶[V] 𝟙_ I) :=
    (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V (𝟙_ I))
  let c := rightContraction F i k
  let p := eHomEquiv V (ρ_ k).hom ⊗ₘ
    ((ρ_ (F.obj k)).inv ≫ (𝟙 (F.obj k) ⊗ₘ eId V (𝟙_ I)))
  let n := (λ_ (F.obj k)).inv ≫ p
  have h : r ≫ (w ≫ g₀) = r ≫ (q ≫ g₁) :=
    congrArg (fun f => r ≫ f) (EnrichedDayKernel.gen_balanced T F R k B C)
  have hGrouped : (r ≫ w) ≫ g₀ = (r ≫ q) ≫ g₁ :=
    (Category.assoc r w g₀).trans (h.trans (Category.assoc r q g₁).symm)
  have hWeight : r ≫ w = 𝟙 W ⊗ₘ l := rightRelationTwo_weightFace d F i k
  have hDiagram : r ≫ q = c ≫ n := rightRelationTwo_diagramFace d F i k
  have hFlow : (𝟙 W ⊗ₘ l) ≫ g₀ = (c ≫ n) ≫ g₁ :=
    (congrArg (fun f => f ≫ g₀) hWeight).symm.trans
      (hGrouped.trans (congrArg (fun f => f ≫ g₁) hDiagram))
  exact hFlow.trans ((Category.assoc c n g₁).trans
    (congrArg (fun f => c ≫ f) (Category.assoc (λ_ (F.obj k)).inv p g₁)))

/-- The right forward/inverse composite is proved by the two complete relations. -/
theorem rightComponent_hom_inv_id :
    rightComponent d F k ≫ rightInvComponent d F k =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor F
        (GradedYoneda.representable (𝟙_ I)) k) := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k
  intro X
  let g := EnrichedDayKernel.gen d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k X
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let A : V := F.obj X.1
  let a := W ◁ (β_ A U).hom ≫ (α_ W U A).inv
  let c := rightCollapseBase d k X ⊗ₘ 𝟙 A
  let t := rightContraction F X.1 k
  let i := rightInvComponent d F k
  have h₀ := congrArg (fun f => f ≫ i) (gen_rightComponent d F k X)
  have hForward : rightForwardGen d F k X = a ≫ c ≫ t :=
    (rightForwardGen_eq_contraction d F k X).trans
      (Category.assoc (W ◁ (β_ A U).hom) (α_ W U A).inv (c ≫ t)).symm
  have h₁ : rightForwardGen d F k X ≫ i = (a ≫ c ≫ t) ≫ i :=
    congrArg (fun f => f ≫ i) hForward
  have hAssoc : (a ≫ c ≫ t) ≫ i = a ≫ c ≫ (t ≫ i) :=
    (Category.assoc a (c ≫ t) i).trans
      (congrArg (fun f => a ≫ f) (Category.assoc c t i))
  have h₂ := congrArg (fun f => a ≫ c ≫ f) (rightGen_second_reduction d F k X.1).symm
  have h₃ : a ≫ c ≫ rightCanonicalGen d F k X.1 = g :=
    (Category.assoc (W ◁ (β_ A U).hom) (α_ W U A).inv
      (c ≫ rightCanonicalGen d F k X.1)).trans (rightGen_first_reduction d F k X).symm
  exact (Category.assoc g (rightComponent d F k) i).symm.trans
    (h₀.trans (h₁.trans (hAssoc.trans
      (h₂.trans (h₃.trans (Category.comp_id g).symm)))))

end RightParticularKernel

omit [MonoidalClosed V] in
/-- The actual mixed left/right unit insertion reverses to the literal right point pair. -/
private theorem rightUnitInsert_reverse {W U A : V}
    (e : 𝟙_ V ⟶ W) (f : 𝟙_ V ⟶ U) :
    (λ_ A).inv ≫ (e ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ f))) ≫
        (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ e))) := by
  let l : A ⟶ A ⊗ U := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ f)
  have hBeta : (λ_ A).inv ≫ (e ⊗ₘ l) ≫ (β_ W (A ⊗ U)).hom =
      l ≫ (ρ_ (A ⊗ U)).inv ≫ (𝟙 (A ⊗ U) ⊗ₘ e) := by
    have hB := congrArg (fun v => (λ_ A).inv ≫ v) (braiding_naturality e l)
    have hFirst : (λ_ A).inv ≫ (e ⊗ₘ l) ≫ (β_ W (A ⊗ U)).hom =
        (ρ_ A).inv ≫ (l ⊗ₘ e) := by
      simpa only [Category.assoc, leftUnitor_inv_braiding_assoc] using hB
    have hSecond : (ρ_ A).inv ≫ (l ⊗ₘ e) =
        l ≫ (ρ_ (A ⊗ U)).inv ≫ (𝟙 (A ⊗ U) ⊗ₘ e) := by
      simpa only [id_tensorHom] using rightUnitor_inv_comp_tensorHom l e
    exact hFirst.trans hSecond
  have hAssoc :
      (ρ_ (A ⊗ U)).inv ≫ (𝟙 (A ⊗ U) ⊗ₘ e) ≫ (α_ A U W).hom =
        A ◁ ((ρ_ U).inv ≫ (𝟙 U ⊗ₘ e)) := by
    calc
      _ = A ◁ (ρ_ U).inv ≫ (α_ A U (𝟙_ V)).inv ≫
          (A ⊗ U) ◁ e ≫ (α_ A U W).hom := by
        simpa only [id_tensorHom, Category.assoc] using
          congrArg (fun v => v ≫ (A ⊗ U) ◁ e ≫ (α_ A U W).hom)
            (rightUnitor_tensor_inv A U)
      _ = A ◁ (ρ_ U).inv ≫ (α_ A U (𝟙_ V)).inv ≫
          (α_ A U (𝟙_ V)).hom ≫ A ◁ U ◁ e :=
        congrArg (fun v => A ◁ (ρ_ U).inv ≫ (α_ A U (𝟙_ V)).inv ≫ v)
          (associator_naturality_right A U e)
      _ = _ := by
        simp only [Iso.inv_hom_id_assoc, id_tensorHom, whiskerLeft_comp]
  have hCollect : f ≫ (ρ_ U).inv ≫ (𝟙 U ⊗ₘ e) =
      (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ e) := by
    simpa only [id_tensorHom, unitors_inv_equal] using
      (rightUnitor_inv_comp_tensorHom f e).symm
  calc
    _ = l ≫ (ρ_ (A ⊗ U)).inv ≫ (𝟙 (A ⊗ U) ⊗ₘ e) ≫ (α_ A U W).hom := by
      simpa only [l, Category.assoc] using congrArg (fun v => v ≫ (α_ A U W).hom) hBeta
    _ = l ≫ A ◁ ((ρ_ U).inv ≫ (𝟙 U ⊗ₘ e)) := by
      simpa only [Category.assoc] using congrArg (fun v => l ≫ v) hAssoc
    _ = (ρ_ A).inv ≫ A ◁ (f ≫ (ρ_ U).inv ≫ (𝟙 U ⊗ₘ e)) := by
      simp only [l, id_tensorHom, whiskerLeft_comp, Category.assoc]
    _ = _ := by
      simpa only [id_tensorHom] using congrArg (fun v => (ρ_ A).inv ≫ A ◁ v) hCollect

omit [MonoidalClosed V] in
/-- The actual unit identity and rho inverse/hom pair contract to the output identity. -/
private theorem rightUnitPoint_contraction (d : EnrichedMonoidalCategoryData V I) (k : I) :
    (λ_ (𝟙_ V)).inv ≫ (eId V (𝟙_ I) ⊗ₘ eHomEquiv V (ρ_ k).hom) ≫
      (rightUnitHom d k (𝟙_ I) ⊗ₘ 𝟙 ((k ⊗ 𝟙_ I) ⟶[V] k)) ≫
      eComp V k (k ⊗ 𝟙_ I) k = eId V k := by
  rw [tensorHom_comp_tensorHom_assoc, rightUnitHom_id]
  simp only [Category.comp_id]
  rw [← eHomEquiv_comp, Iso.inv_hom_id, eHomEquiv_id]

section RightParticularInverse

variable (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]

/-- The original right generator insertion followed by its contraction is the identity. -/
theorem rightComponent_inv_hom_id :
    rightInvComponent d F k ≫ rightComponent d F k = 𝟙 (F.obj k) := by
  let A : V := F.obj k
  let U : V := 𝟙_ I ⟶[V] 𝟙_ I
  let W : V := (k ⊗ 𝟙_ I) ⟶[V] k
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k
  let Q : V := W ⊗ (A ⊗ U)
  let e : 𝟙_ V ⟶ W := eHomEquiv V (ρ_ k).hom
  let f : 𝟙_ V ⟶ U := eId V (𝟙_ I)
  let delta : 𝟙_ V ⟶ U ⊗ W := (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ e)
  let c : U ⊗ W ⟶ (k ⟶[V] k) :=
    (rightUnitHom d k (𝟙_ I) ⊗ₘ 𝟙 W) ≫ eComp V k (k ⊗ 𝟙_ I) k
  let x : (𝟙_ V) ⊗ A ⟶ Q := e ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ f))
  let n : A ⟶ Q := (λ_ A).inv ≫ x
  let g : Q ⟶ E := EnrichedDayKernel.gen d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k (k, 𝟙_ I)
  let h : Q ⟶ A := rightForwardGen d F k (k, 𝟙_ I)
  let b := (β_ W (A ⊗ U)).hom
  let a := (α_ A U W).hom
  let v := MonoidalClosed.uncurry (F.map k k)
  have hContract : delta ≫ c = eId V k :=
    (Category.assoc (λ_ (𝟙_ V)).inv (f ⊗ₘ e) c).trans (rightUnitPoint_contraction d k)
  have hInv₀ : rightInvComponent d F k = (λ_ A).inv ≫ x ≫ g := rfl
  have hInv : rightInvComponent d F k = n ≫ g :=
    hInv₀.trans (Category.assoc (λ_ A).inv x g).symm
  have hGen : g ≫ rightComponent d F k = h := gen_rightComponent d F k (k, 𝟙_ I)
  have hData : h = b ≫ a ≫ A ◁ c ≫ v := rfl
  have hReverse : n ≫ b ≫ a = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ delta) := by
    simpa only [n, x, b, a, delta, Category.assoc] using rightUnitInsert_reverse e f
  have hCollect : (𝟙 A ⊗ₘ delta) ≫ A ◁ c = 𝟙 A ⊗ₘ eId V k := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, hContract]
    simp only [Category.id_comp]
  calc
    _ = (n ≫ g) ≫ rightComponent d F k := congrArg (fun q => q ≫ rightComponent d F k) hInv
    _ = n ≫ h := (Category.assoc n g (rightComponent d F k)).trans
      (congrArg (fun q => n ≫ q) hGen)
    _ = n ≫ b ≫ a ≫ A ◁ c ≫ v := congrArg (fun q => n ≫ q) hData
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ delta) ≫ A ◁ c ≫ v := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ A ◁ c ≫ v) hReverse
    _ = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ eId V k) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun q => (ρ_ A).inv ≫ q ≫ v) hCollect
    _ = _ := action_id F k

/-- Both actual full relations and the actual identity insertion give a right component iso. -/
def rightComponentIso :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k ≅ F.obj k where
  hom := rightComponent d F k
  inv := rightInvComponent d F k
  hom_inv_id := rightComponent_hom_inv_id d F k
  inv_hom_id := rightComponent_inv_hom_id d F k

end RightParticularInverse

/-- The full right forward family intertwines the actual output hom action. -/
private theorem rightForwardGen_output_natural (d : EnrichedMonoidalCategoryData V I)
    (F : EnrichedFunctor V I V) (k k' : I) (X : I × I) :
    Output.outputAction (X.1 ⊗ X.2) k k'
        (F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2)) ≫ rightForwardGen d F k' X =
      (k ⟶[V] k') ◁ rightForwardGen d F k X ≫
        (β_ (k ⟶[V] k') (F.obj k)).hom ≫ MonoidalClosed.uncurry (F.map k k') := by
  let R : V := k ⟶[V] k'
  let H : V := (X.1 ⊗ X.2) ⟶[V] k
  let H' : V := (X.1 ⊗ X.2) ⟶[V] k'
  let A : V := F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2)
  let B : V := F.obj (X.1 ⊗ X.2)
  let s : A ⟶ B := rightStrengthComponent d F X
  let b : R ⊗ F.obj k ⟶ F.obj k ⊗ R := (β_ R (F.obj k)).hom
  let a : F.obj k ⊗ R ⟶ F.obj k' := MonoidalClosed.uncurry (F.map k k')
  have hX : (show H ⊗ A ⟶ F.obj k from rightForwardGen d F k X) =
      (𝟙 H ⊗ₘ s) ≫ evaluationGen F k X := rightForwardGen_eq_strength d F k X
  have hX' : (show H' ⊗ A ⟶ F.obj k' from rightForwardGen d F k' X) =
      (𝟙 H' ⊗ₘ s) ≫ evaluationGen F k' X := rightForwardGen_eq_strength d F k' X
  change (show R ⊗ (H ⊗ A) ⟶ F.obj k' from
      Output.outputAction (X.1 ⊗ X.2) k k' A ≫ rightForwardGen d F k' X) =
    (show R ⊗ (H ⊗ A) ⟶ F.obj k' from R ◁ rightForwardGen d F k X ≫ b ≫ a)
  calc
    _ = Output.outputAction (X.1 ⊗ X.2) k k' A ≫
        (𝟙 H' ⊗ₘ s) ≫ evaluationGen F k' X :=
      congrArg (fun f : H' ⊗ A ⟶ F.obj k' =>
        Output.outputAction (X.1 ⊗ X.2) k k' A ≫ f) hX'
    _ = R ◁ (𝟙 H ⊗ₘ s) ≫ Output.outputAction (X.1 ⊗ X.2) k k' B ≫
        evaluationGen F k' X := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ evaluationGen F k' X)
          (outputAction_coefficient (X.1 ⊗ X.2) k k' s)
    _ = R ◁ (𝟙 H ⊗ₘ s) ≫ R ◁ evaluationGen F k X ≫ b ≫ a :=
      congrArg (fun f => R ◁ (𝟙 H ⊗ₘ s) ≫ f)
        (evaluationGen_output_natural F k k' X)
    _ = R ◁ ((𝟙 H ⊗ₘ s) ≫ evaluationGen F k X) ≫ b ≫ a := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ b ≫ a)
          (whiskerLeft_comp R (𝟙 H ⊗ₘ s) (evaluationGen F k X)).symm
    _ = _ := congrArg (fun f : H ⊗ A ⟶ F.obj k => R ◁ f ≫ b ≫ a) hX.symm

section RightParticularNaturality

variable (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (𝟙_ I)) k)]

/-- The actual descended right component retains full output-hom naturality. -/
theorem rightComponent_natural (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        F (GradedYoneda.representable (𝟙_ I)) k')] :
    MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor
        F (GradedYoneda.representable (𝟙_ I)) k k') ≫ rightComponent d F k' =
      (rightComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫ MonoidalClosed.uncurry (F.map k k') := by
  let R : V := k ⟶[V] k'
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k
  let E' : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k'
  let a : E ⟶ F.obj k := rightComponent d F k
  let b : E' ⟶ F.obj k' := rightComponent d F k'
  let u : E ⊗ R ⟶ E' := MonoidalClosed.uncurry
    (Output.map d.tensorEnrichedFunctor F (GradedYoneda.representable (𝟙_ I)) k k')
  let v : F.obj k ⊗ R ⟶ F.obj k' := MonoidalClosed.uncurry (F.map k k')
  let l : R ⊗ E ⟶ F.obj k' := (β_ R E).hom ≫ u ≫ b
  let r : R ⊗ E ⟶ F.obj k' := (β_ R E).hom ≫ (a ⊗ₘ 𝟙 R) ≫ v
  have h : l = r := by
    apply MonoidalClosed.curry_injective
    apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k
    intro X
    rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
    apply congrArg (MonoidalClosed.curry (A := R))
    let Q : V := EnrichedDayKernel.objects d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k X
    let g : Q ⟶ E := EnrichedDayKernel.gen d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k X
    have hLeft :
        R ◁ g ≫ l = Output.outputAction (X.1 ⊗ X.2) k k'
          (F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2)) ≫ rightForwardGen d F k' X := by
      let g' := EnrichedDayKernel.gen d.tensorEnrichedFunctor
        F (GradedYoneda.representable (𝟙_ I)) k' X
      let t := Output.outputAction (X.1 ⊗ X.2) k k'
        (F.obj X.1 ⊗ (𝟙_ I ⟶[V] X.2))
      have hAG : Output.actionGenerator d.tensorEnrichedFunctor
          F (GradedYoneda.representable (𝟙_ I)) k k' X = t ≫ g' := rfl
      have hg : (β_ R Q).hom ≫ (g ⊗ₘ 𝟙 R) ≫ u = t ≫ g' :=
        (Output.gen_naturality d.tensorEnrichedFunctor
          F (GradedYoneda.representable (𝟙_ I)) k k' X).trans hAG
      have hG' : g' ≫ b = rightForwardGen d F k' X := gen_rightComponent d F k' X
      have hBraid : (R ◁ g) ≫ (β_ R E).hom = (β_ R Q).hom ≫ (g ⊗ₘ 𝟙 R) := by
        simpa only [id_tensorHom] using braiding_naturality (𝟙 R) g
      have hA : R ◁ g ≫ l = ((R ◁ g ≫ (β_ R E).hom) ≫ u) ≫ b :=
        (Category.assoc (R ◁ g) (β_ R E).hom (u ≫ b)).symm.trans
          (Category.assoc (R ◁ g ≫ (β_ R E).hom) u b).symm
      have hB := congrArg (fun f => (f ≫ u) ≫ b) hBraid
      have hC := congrArg (fun f => f ≫ b) hg
      exact hA.trans (hB.trans
        ((congrArg (fun f => f ≫ b) (Category.assoc (β_ R Q).hom (g ⊗ₘ 𝟙 R) u)).trans
          (hC.trans ((Category.assoc t g' b).trans (congrArg (fun f => t ≫ f) hG')))))
    have hRight :
        R ◁ g ≫ r = R ◁ rightForwardGen d F k X ≫ (β_ R (F.obj k)).hom ≫ v := by
      calc
        _ = R ◁ (g ≫ a) ≫ (β_ R (F.obj k)).hom ≫ v := by
          simpa only [r, id_tensorHom, whiskerLeft_comp, Category.assoc] using
            congrArg (fun f => R ◁ g ≫ f ≫ v) (braiding_naturality (𝟙 R) a).symm
        _ = _ := by
          dsimp only [a, g]
          rw [gen_rightComponent]
    exact hLeft.trans ((rightForwardGen_output_natural d F k k' X).trans hRight.symm)
  have h' := congrArg (fun f => (β_ R E).inv ≫ f) h
  simpa only [l, r, Category.assoc, Iso.inv_hom_id_assoc] using h'

/-- The actual inverse components retain full output-hom naturality. -/
theorem rightInvComponent_natural (k' : I)
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k')
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
        F (GradedYoneda.representable (𝟙_ I)) k')] :
    MonoidalClosed.uncurry (F.map k k') ≫ rightInvComponent d F k' =
      (rightInvComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (Output.map d.tensorEnrichedFunctor
          F (GradedYoneda.representable (𝟙_ I)) k k') := by
  have h := congrArg
    (fun f => (rightInvComponent d F k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
      f ≫ rightInvComponent d F k') (rightComponent_natural d F k k')
  simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    rightComponent_hom_inv_id, rightComponent_inv_hom_id,
    id_tensorHom_id, Category.id_comp, Category.comp_id] using h.symm

end RightParticularNaturality

end RightFull

section RightFamily

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F : EnrichedFunctor V I V)
  [∀ k, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)]
  [∀ k, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)]
  [∀ k, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- The right unitor is a genuine unit-graded transformation on the constructed output functor. -/
abbrev rightUnitorHom :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (Output.functor d.tensorEnrichedFunctor F (GradedYoneda.representable (𝟙_ I))) F :=
  GradedNatTrans.unitOfComponents (fun k => rightComponent d F k)
    (fun k k' => rightComponent_natural d F k k')

/-- The original identity-inserting inverses form a genuine unit-graded transformation. -/
abbrev rightUnitorInv :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F
      (Output.functor d.tensorEnrichedFunctor F (GradedYoneda.representable (𝟙_ I))) :=
  GradedNatTrans.unitOfComponents (fun k => rightInvComponent d F k)
    (fun k k' => rightInvComponent_natural d F k k')

/-- The genuine unitor's components are the actual descended maps. -/
theorem rightUnitorHom_component (k : I) :
    (eHomEquiv V).symm ((rightUnitorHom d F).app k) = rightComponent d F k :=
  GradedNatTrans.unitOfComponents_component (V := V)
    (F' := Output.functor d.tensorEnrichedFunctor F (GradedYoneda.representable (𝟙_ I)))
    (G' := F) (fun k => rightComponent d F k)
    (fun k k' => rightComponent_natural d F k k') k

/-- The genuine inverse's components are the original chosen generators. -/
theorem rightUnitorInv_component (k : I) :
    (eHomEquiv V).symm ((rightUnitorInv d F).app k) = rightInvComponent d F k :=
  GradedNatTrans.unitOfComponents_component (V := V) (F' := F)
    (G' := Output.functor d.tensorEnrichedFunctor F (GradedYoneda.representable (𝟙_ I)))
    (fun k => rightInvComponent d F k)
    (fun k k' => rightInvComponent_natural d F k k') k

/-- The right Day unitor is an actual isomorphism of genuine enriched functors. -/
def rightUnitor :
    (⟨Output.functor d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I))⟩ : EnrichedFunctorCat V I) ≅ ⟨F⟩ where
  hom := rightUnitorHom d F
  inv := rightUnitorInv d F
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((rightUnitorHom d F).app k) ≫
      (eHomEquiv V).symm ((rightUnitorInv d F).app k) = _
    rw [rightUnitorHom_component, rightUnitorInv_component]
    exact rightComponent_hom_inv_id d F k
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((rightUnitorInv d F).app k) ≫
      (eHomEquiv V).symm ((rightUnitorHom d F).app k) = _
    rw [rightUnitorInv_component, rightUnitorHom_component]
    exact rightComponent_inv_hom_id d F k

/-- The isomorphism keeps the literal genuine forward transformation. -/
@[simp]
theorem rightUnitor_hom : (rightUnitor d F).hom = rightUnitorHom d F := rfl

/-- The isomorphism keeps the literal genuine inverse transformation. -/
@[simp]
theorem rightUnitor_inv : (rightUnitor d F).inv = rightUnitorInv d F := rfl

end RightFamily

section RightInputGeneratorNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- A genuine input transformation retains the entire original right generator formula. -/
theorem rightForwardGen_input_natural (d : EnrichedMonoidalCategoryData V I)
    {F G : EnrichedFunctor V I V}
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) (k : I) (X : I × I) :
    (((X.1 ⊗ X.2) ⟶[V] k) ◁
        ((eHomEquiv V).symm (a.app X.1) ⊗ₘ 𝟙 (𝟙_ I ⟶[V] X.2))) ≫
        rightForwardGen d G k X =
      rightForwardGen d F k X ≫ (eHomEquiv V).symm (a.app k) := by
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let H : V := X.1 ⟶[V] k
  let A : V := F.obj X.1
  let B : V := G.obj X.1
  let c : U ⊗ W ⟶ H :=
    (rightUnitHom d X.1 X.2 ⊗ₘ 𝟙 W) ≫ eComp V X.1 (X.1 ⊗ X.2) k
  let f : A ⟶ B := (eHomEquiv V).symm (a.app X.1)
  let g : F.obj k ⟶ G.obj k := (eHomEquiv V).symm (a.app k)
  let u : A ⊗ H ⟶ F.obj k := MonoidalClosed.uncurry (F.map X.1 k)
  let v : B ⊗ H ⟶ G.obj k := MonoidalClosed.uncurry (G.map X.1 k)
  let s : W ⊗ (A ⊗ U) ⟶ W ⊗ (B ⊗ U) := W ◁ (f ⊗ₘ 𝟙 U)
  let m : W ⊗ (A ⊗ U) ⟶ A ⊗ H :=
    (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom ≫ A ◁ c
  let m' : W ⊗ (B ⊗ U) ⟶ B ⊗ H :=
    (β_ W (B ⊗ U)).hom ≫ (α_ B U W).hom ≫ B ◁ c
  have hAction : (f ⊗ₘ 𝟙 H) ≫ v = u ≫ g := by
    simpa only [f, g, H, u, v] using (a.uncurriedNaturality X.1 k).symm
  have hBeta : s ≫ (β_ W (B ⊗ U)).hom =
      (β_ W (A ⊗ U)).hom ≫ ((f ⊗ₘ 𝟙 U) ⊗ₘ 𝟙 W) := by
    simpa only [s, id_tensorHom] using braiding_naturality (𝟙 W) (f ⊗ₘ 𝟙 U)
  have hAssoc : ((f ⊗ₘ 𝟙 U) ⊗ₘ 𝟙 W) ≫ (α_ B U W).hom =
      (α_ A U W).hom ≫ (f ⊗ₘ 𝟙 (U ⊗ W)) := by
    simpa only [tensorHom_id] using associator_naturality_left f U W
  have hExchange : (f ⊗ₘ 𝟙 (U ⊗ W)) ≫ B ◁ c =
      A ◁ c ≫ (f ⊗ₘ 𝟙 H) := by
    simpa only [tensorHom_id] using (whisker_exchange f c).symm
  have hMove : s ≫ m' = m ≫ (f ⊗ₘ 𝟙 H) := by
    simp only [m, m', Category.assoc]
    rw [← Category.assoc, hBeta]
    simp only [Category.assoc]
    rw [← Category.assoc ((f ⊗ₘ 𝟙 U) ⊗ₘ 𝟙 W), hAssoc]
    simp only [Category.assoc]
    rw [hExchange]
  have hFData : rightForwardGen d F k X =
      (β_ W (A ⊗ U)).hom ≫ (α_ A U W).hom ≫ A ◁ c ≫ u := rfl
  have hGData : rightForwardGen d G k X =
      (β_ W (B ⊗ U)).hom ≫ (α_ B U W).hom ≫ B ◁ c ≫ v := rfl
  have hF : rightForwardGen d F k X = m ≫ u :=
    hFData.trans
      ((congrArg (fun v => (β_ W (A ⊗ U)).hom ≫ v)
        (Category.assoc (α_ A U W).hom (A ◁ c) u).symm).trans
        (Category.assoc (β_ W (A ⊗ U)).hom ((α_ A U W).hom ≫ A ◁ c) u).symm)
  have hG : rightForwardGen d G k X = m' ≫ v :=
    hGData.trans
      ((congrArg (fun x => (β_ W (B ⊗ U)).hom ≫ x)
        (Category.assoc (α_ B U W).hom (B ◁ c) v).symm).trans
        (Category.assoc (β_ W (B ⊗ U)).hom ((α_ B U W).hom ≫ B ◁ c) v).symm)
  calc
    _ = s ≫ (m' ≫ v) := congrArg (fun q => s ≫ q) hG
    _ = (m ≫ (f ⊗ₘ 𝟙 H)) ≫ v :=
      (Category.assoc s m' v).symm.trans (congrArg (fun q => q ≫ v) hMove)
    _ = m ≫ (u ≫ g) :=
      (Category.assoc m (f ⊗ₘ 𝟙 H) v).trans (congrArg (fun q => m ≫ q) hAction)
    _ = _ := (Category.assoc m u g).symm.trans (congrArg (fun q => q ≫ g) hF.symm)

end RightInputGeneratorNaturality

section RightInputComponentNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) {F G : EnrichedFunctor V I V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) (k : I)
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      F (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    G (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    G (GradedYoneda.representable (𝟙_ I)) k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    G (GradedYoneda.representable (𝟙_ I)) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      G (GradedYoneda.representable (𝟙_ I)) k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- Input naturality needs only the particular source and target unit kernels. -/
theorem rightComponent_input_natural :
    Input.mapAt d.tensorEnrichedFunctor
        a (GradedNatTrans.unitId (GradedYoneda.representable (𝟙_ I))) k ≫
        rightComponent d G k =
      rightComponent d F k ≫ (eHomEquiv V).symm (a.app k) := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
    F (GradedYoneda.representable (𝟙_ I)) k
  intro X
  let W : V := (X.1 ⊗ X.2) ⟶[V] k
  let U : V := 𝟙_ I ⟶[V] X.2
  let R := GradedYoneda.representable (V := V) (𝟙_ I)
  let f := (eHomEquiv V).symm (a.app X.1)
  let g := (eHomEquiv V).symm (a.app k)
  let c := Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId R) k
  let p := EnrichedDayKernel.gen d.tensorEnrichedFunctor F R k X
  let q := EnrichedDayKernel.gen d.tensorEnrichedFunctor G R k X
  let s : W ⊗ (F.obj X.1 ⊗ U) ⟶ W ⊗ (G.obj X.1 ⊗ U) :=
    𝟙 W ⊗ₘ (f ⊗ₘ 𝟙 U)
  let u := (eHomEquiv V).symm ((GradedNatTrans.unitId R).app X.2)
  let s₀ := 𝟙 W ⊗ₘ (f ⊗ₘ u)
  have hId : u = 𝟙 U := GradedNatTrans.unitId_component R X.2
  have hMap₀ : p ≫ c = s₀ ≫ q :=
    Input.gen_mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId R) k X
  have hS : s₀ = s := congrArg (fun v => 𝟙 W ⊗ₘ (f ⊗ₘ v)) hId
  have hMap : p ≫ c = s ≫ q := hMap₀.trans (congrArg (fun v => v ≫ q) hS)
  have hG : q ≫ rightComponent d G k = rightForwardGen d G k X := gen_rightComponent d G k X
  have hF : p ≫ rightComponent d F k = rightForwardGen d F k X := gen_rightComponent d F k X
  have hNat : s ≫ rightForwardGen d G k X = rightForwardGen d F k X ≫ g := by
    simpa only [s, id_tensorHom, f, g, W, U] using rightForwardGen_input_natural d a k X
  exact (Category.assoc p c (rightComponent d G k)).symm.trans
    ((congrArg (fun v => v ≫ rightComponent d G k) hMap).trans
      ((Category.assoc s q (rightComponent d G k)).trans
        ((congrArg (fun v => s ≫ v) hG).trans
          (hNat.trans ((congrArg (fun v => v ≫ g) hF.symm).trans
            (Category.assoc p (rightComponent d F k) g))))))

end RightInputComponentNaturality

section RightUnitEndofunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
      (GradedYoneda.representable (V := V) (𝟙_ I)) k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
      (GradedYoneda.representable (V := V) (𝟙_ I)) k)]
  [∀ (F : EnrichedFunctor V I V) k,
    HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (GradedYoneda.representable (V := V) (𝟙_ I)) k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
        (GradedYoneda.representable (V := V) (𝟙_ I)) k)]

open scoped MonoidalClosed

attribute [local instance] Enriched.prodCategory

/-- Tensoring by the actual unit on the right needs only the fixed-second-unit kernels. -/
def rightUnitEndofunctor : EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I where
  obj F := ⟨Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor
    (GradedYoneda.representable (V := V) (𝟙_ I))⟩
  map a := Input.natTrans d.tensorEnrichedFunctor a
    (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm
      ((Input.natTrans d.tensorEnrichedFunctor (GradedNatTrans.unitId F.toEnrichedFunctor)
        (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))).app k) = _
    rw [Input.natTrans_component, Input.mapAt_id]
  map_comp a b := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp]
    change (eHomEquiv V).symm
      ((Input.natTrans d.tensorEnrichedFunctor (GradedNatTrans.unitComp a b)
        (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))).app k) =
      (eHomEquiv V).symm
        ((Input.natTrans d.tensorEnrichedFunctor a
          (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))).app k) ≫
      (eHomEquiv V).symm
        ((Input.natTrans d.tensorEnrichedFunctor b
          (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))).app k)
    rw [Input.natTrans_component, Input.natTrans_component, Input.natTrans_component]
    have hUnit :
        GradedNatTrans.unitComp
            (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))
            (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I))) =
          GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)) := by
      exact Category.id_comp
        (𝟙 (⟨GradedYoneda.representable (V := V) (𝟙_ I)⟩ : EnrichedFunctorCat V I))
    simpa only [hUnit] using Input.mapAt_comp d.tensorEnrichedFunctor a b
      (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I)))
      (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I))) k

/-- The actual fixed-second-unit functor acts by its actual genuine input maps. -/
@[simp]
theorem rightUnitEndofunctor_map_component {F G : EnrichedFunctorCat V I}
    (a : F ⟶ G) (k : I) :
    EnrichedFunctorCat.component ((rightUnitEndofunctor d).map a) k =
      Input.mapAt d.tensorEnrichedFunctor a
        (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I))) k :=
  Input.natTrans_component d.tensorEnrichedFunctor a _ k

/-- The actual right enriched unitors are natural in every genuine input transformation. -/
def rightUnitorNatIso : rightUnitEndofunctor d ≅ 𝟭 (EnrichedFunctorCat V I) :=
  NatIso.ofComponents (fun F => rightUnitor d F.toEnrichedFunctor) (by
    intro F G a
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      rightUnitEndofunctor_map_component]
    change Input.mapAt d.tensorEnrichedFunctor a
        (GradedNatTrans.unitId (GradedYoneda.representable (V := V) (𝟙_ I))) k ≫
        (eHomEquiv V).symm ((rightUnitorHom d G.toEnrichedFunctor).app k) =
      (eHomEquiv V).symm ((rightUnitorHom d F.toEnrichedFunctor).app k) ≫
        (eHomEquiv V).symm (a.app k)
    rw [rightUnitorHom_component, rightUnitorHom_component]
    exact rightComponent_input_natural d a k)

end RightUnitEndofunctor

end CategoryTheory.EnrichedDayKernel.Unitors
