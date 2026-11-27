/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedProductInclusions
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Associator
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendTransport
public import MathlibExt.CategoryTheory.Enriched.GradedRestriction

/-!
# Associator Comparison

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK uI vI uE uA uB vK
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorTensor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

section Unit
variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The unit-graded transformation from the external tensor to the pullback of its Day
  convolution, with components given by the coend unit generators. -/
def unitGraded : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (F.externalTensor G) (T.comp V (Output.functor T F G)) :=
  GradedNatTrans.unitOfComponents (fun a => AssociatorUnit.unitGenerator T F G a) (by
    intro a b
    change MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
      AssociatorUnit.unitGenerator T F G b =
      (AssociatorUnit.unitGenerator T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (T.map a b ≫ Output.map T F G (T.obj a) (T.obj b))
    rw [MonoidalClosed.uncurry_natural_left]
    exact AssociatorUnit.unitGenerator_naturality T F G a b)

theorem unitGraded_app (a : C × D) :
    (unitGraded T F G).app a = eHomEquiv V (AssociatorUnit.unitGenerator T F G a) :=
  GradedNatTrans.unitOfComponents_app _ _ a

end Unit

section Pullback
variable (T : EnrichedFunctor V C K) (Q : EnrichedFunctor V K V)
  (H : EnrichedFunctor V D V)

theorem externalTensor_comp : (T.comp V Q).externalTensor H =
    (prodEnrichedFunctor T (EnrichedFunctor.id V D)).comp V (Q.externalTensor H) := by
  refine EnrichedFunctor.ext V (F := (T.comp V Q).externalTensor H)
    (G := (prodEnrichedFunctor T (EnrichedFunctor.id V D)).comp V (Q.externalTensor H))
    (fun _ => rfl) ?_
  intro X Y
  have hm : ((T.comp V Q).externalTensor H).map X Y =
      ((prodEnrichedFunctor T (EnrichedFunctor.id V D)).comp V
        (Q.externalTensor H)).map X Y := by
    change ((T.map X.1 Y.1 ≫ Q.map (T.obj X.1) (T.obj Y.1)) ⊗ₘ H.map X.2 Y.2) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          (Q.obj (T.obj X.1)) (Q.obj (T.obj Y.1)) (H.obj X.2) (H.obj Y.2) =
      (T.map X.1 Y.1 ⊗ₘ 𝟙 (X.2 ⟶[V] Y.2)) ≫
        (Q.map (T.obj X.1) (T.obj Y.1) ⊗ₘ H.map X.2 Y.2) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
          (Q.obj (T.obj X.1)) (Q.obj (T.obj Y.1)) (H.obj X.2) (H.obj Y.2)
    rw [tensorHom_comp_tensorHom_assoc, Category.id_comp]
  change ((T.comp V Q).externalTensor H).map X Y ≫ 𝟙 _ =
    ((prodEnrichedFunctor T (EnrichedFunctor.id V D)).comp V (Q.externalTensor H)).map X Y
  exact (Category.comp_id _).trans hm

end Pullback

section Coefficients

variable {E : Type uE} [EnrichedCategory V E]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- Insert the Day unit generator for the first two coefficients and retain the identity
  of the third coefficient. -/
abbrev leftCoefficientMap (X : (C × D) × E) :
    ((F.externalTensor G).externalTensor H).obj X ⟶
      ((Output.functor T F G).externalTensor H).obj
        ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj X) :=
  AssociatorUnit.unitGenerator T F G X.1 ⊗ₘ 𝟙 (H.obj X.2)

theorem leftCoefficientMap_naturality (X Y : (C × D) × E) :
    MonoidalClosed.uncurry (((F.externalTensor G).externalTensor H).map X Y) ≫
        leftCoefficientMap T F G H Y =
      (leftCoefficientMap T F G H X ⊗ₘ
        (prodEnrichedFunctor T (EnrichedFunctor.id V E)).map X Y) ≫
        MonoidalClosed.uncurry (((Output.functor T F G).externalTensor H).map
          ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj X)
          ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj Y)) := by
  let A := F.obj X.1.1 ⊗ G.obj X.1.2
  let A' := F.obj Y.1.1 ⊗ G.obj Y.1.2
  let B := H.obj X.2
  let B' := H.obj Y.2
  let P : V := X.1 ⟶[V] Y.1
  let S : V := X.2 ⟶[V] Y.2
  let R : V := T.obj X.1 ⟶[V] T.obj Y.1
  let U := EnrichedDayKernel.obj T F G (T.obj X.1)
  let U' := EnrichedDayKernel.obj T F G (T.obj Y.1)
  let ua : A ⟶ U := AssociatorUnit.unitGenerator T F G X.1
  let ub : A' ⟶ U' := AssociatorUnit.unitGenerator T F G Y.1
  let t : P ⟶ R := T.map X.1 Y.1
  let f : A ⊗ P ⟶ A' := MonoidalClosed.uncurry ((F.externalTensor G).map X.1 Y.1)
  let g : B ⊗ S ⟶ B' := MonoidalClosed.uncurry (H.map X.2 Y.2)
  let o : U ⊗ R ⟶ U' := MonoidalClosed.uncurry (Output.map T F G (T.obj X.1) (T.obj Y.1))
  have hu : f ≫ ub = (ua ⊗ₘ t) ≫ o := by
    have h := AssociatorUnit.unitGenerator_naturality T F G X.1 Y.1
    change f ≫ ub = (ua ⊗ₘ 𝟙 P) ≫ U ◁ t ≫ o at h
    simpa only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id] using h
  rw [EnrichedFunctor.externalTensor_uncurry (F.externalTensor G) H X Y,
    EnrichedFunctor.externalTensor_uncurry (Output.functor T F G) H
      ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj X)
      ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj Y)]
  change (tensorμ A B P S ≫ (f ⊗ₘ g)) ≫ (ub ⊗ₘ 𝟙 B') =
    ((ua ⊗ₘ 𝟙 B) ⊗ₘ (t ⊗ₘ 𝟙 S)) ≫ tensorμ U B R S ≫ (o ⊗ₘ g)
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.comp_id, hu]
  have hm := tensorμ_natural_assoc ua (𝟙 B) t (𝟙 S) (o ⊗ₘ g)
  simpa only [id_tensorHom_id, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using hm.symm

end Coefficients

section Tensor
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

/-- The enriched partial tensor `(i, j, k) ↦ (i ⊗ j, k)`. -/
abbrev leftProduct : EnrichedFunctor V ((I × I) × I) (I × I) :=
  prodEnrichedFunctor d.tensorEnrichedFunctor (EnrichedFunctor.id V I)

/-- The enriched partial tensor `(i, j, k) ↦ (i, j ⊗ k)` on `I × (I × I)`. -/
abbrev rightProduct : EnrichedFunctor V (I × (I × I)) (I × I) :=
  prodEnrichedFunctor (EnrichedFunctor.id V I) d.tensorEnrichedFunctor

/-- The enriched tensor of three indices with parenthesization `(i ⊗ j) ⊗ k`. -/
abbrev leftTensor : EnrichedFunctor V ((I × I) × I) I :=
  (leftProduct d).comp V d.tensorEnrichedFunctor

/-- The enriched tensor of three indices with parenthesization `i ⊗ (j ⊗ k)`. -/
abbrev rightTensor : EnrichedFunctor V (I × (I × I)) I :=
  (rightProduct d).comp V d.tensorEnrichedFunctor

omit [MonoidalClosed V] in
theorem leftTensor_original : leftTensor d = AssociatorIndex.leftIndex d := rfl

omit [MonoidalClosed V] in
theorem rightTensor_original :
    (Associator.productAssociator (V := V) (A := I) (B := I) (C := I)).comp V
      (rightTensor d) = AssociatorIndex.rightIndex d := by
  refine EnrichedFunctor.ext V
    (F := (Associator.productAssociator (V := V) (A := I) (B := I) (C := I)).comp V
      (rightTensor d)) (G := AssociatorIndex.rightIndex d) (fun _ => rfl) ?_
  intro X Y
  have h : ((Associator.productAssociator (V := V) (A := I) (B := I) (C := I)).comp V
      (rightTensor d)).map X Y = (AssociatorIndex.rightIndex d).map X Y := by
    change (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (𝟙 (X.1.1 ⟶[V] Y.1.1) ⊗ₘ d.tensorMap X.1.2 Y.1.2 X.2 Y.2) ≫
        d.tensorMap X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2) =
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (X.1.1 ⟶[V] Y.1.1) ◁ d.tensorMap X.1.2 Y.1.2 X.2 Y.2 ≫
        d.tensorMap X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
    rw [id_tensorHom]
  change ((Associator.productAssociator (V := V) (A := I) (B := I) (C := I)).comp V
      (rightTensor d)).map X Y ≫ 𝟙 _ = (AssociatorIndex.rightIndex d).map X Y
  exact (Category.comp_id _).trans h

variable (m : I)

/-- The identity identification of the flat left weight with the outer Day weight after
  partially tensoring the first two indices. -/
abbrev leftWeightMap (X : (I × I) × I) :
    (AssociatorIndex.leftWeight d m).obj (op X) ⟶
      (weight d.tensorEnrichedFunctor m).obj (op ((leftProduct d).obj X)) := 𝟙 _

theorem leftWeightMap_naturality (X Y : (I × I) × I) :
    MonoidalClosed.uncurry ((AssociatorIndex.leftWeight d m).map (op Y) (op X)) ≫
        leftWeightMap d m X =
      (leftWeightMap d m Y ⊗ₘ (leftProduct d).map X Y) ≫
        MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
          (op ((leftProduct d).obj Y)) (op ((leftProduct d).obj X))) := by
  rw [EnrichedDayKernel.weight_uncurry_map (AssociatorIndex.leftIndex d) m X Y,
    EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor m
      ((leftProduct d).obj X) ((leftProduct d).obj Y)]
  let LX := (X.1.1 ⊗ X.1.2) ⊗ X.2
  let LY := (Y.1.1 ⊗ Y.1.2) ⊗ Y.2
  let WX : V := LX ⟶[V] m
  let WY : V := LY ⟶[V] m
  let P : V := X ⟶[V] Y
  let Q : V := ((X.1.1 ⊗ X.1.2) ⟶[V] (Y.1.1 ⊗ Y.1.2)) ⊗ (X.2 ⟶[V] Y.2)
  let l : P ⟶ (LX ⟶[V] LY) := (AssociatorIndex.leftIndex d).map X Y
  let s : P ⟶ Q := (leftProduct d).map X Y
  let u : Q ⟶ (LX ⟶[V] LY) := d.tensorEnrichedFunctor.map
    ((leftProduct d).obj X) ((leftProduct d).obj Y)
  have hl : l = s ≫ u := rfl
  change (WY ◁ l ≫ (β_ WY (LX ⟶[V] LY)).hom ≫ eComp V LX LY m) ≫ 𝟙 WX =
    (𝟙 WY ⊗ₘ s) ≫ WY ◁ u ≫ (β_ WY (LX ⟶[V] LY)).hom ≫ eComp V LX LY m
  simp only [id_tensorHom, ← whiskerLeft_comp_assoc]
  rw [hl]
  exact Category.comp_id _

end Tensor
end CategoryTheory.EnrichedDayKernel.AssociatorTensor


namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)

attribute [local instance] Enriched.prodCategory

variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H m)]

/-- The map from the flat left coend to the left nested Day value induced by the partial
  index tensor and the inner Day unit generators. -/
def flatToNested : AssociatorFlat.leftPoint d F G H m ⟶
    EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H m :=
  Enriched.weightedCoend.Transport.map (AssociatorTensor.leftProduct d)
    (AssociatorIndex.leftWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.leftCoefficients F G H)
    ((Output.functor d.tensorEnrichedFunctor F G).externalTensor H)
    (AssociatorTensor.leftWeightMap d m)
    (fun X => AssociatorTensor.leftCoefficientMap d.tensorEnrichedFunctor F G H X)
    (AssociatorTensor.leftWeightMap_naturality d m)
    (AssociatorTensor.leftCoefficientMap_naturality d.tensorEnrichedFunctor F G H)

theorem leftGenerator_flatToNested (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ flatToNested d F G H m =
      (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] m) ⊗ₘ
        (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2))) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (Output.functor d.tensorEnrichedFunctor F G) H m
          ((AssociatorTensor.leftProduct d).obj X) := by
  exact Enriched.weightedCoend.Transport.ι_map (AssociatorTensor.leftProduct d)
    (AssociatorIndex.leftWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.leftCoefficients F G H)
    ((Output.functor d.tensorEnrichedFunctor F G).externalTensor H)
    (AssociatorTensor.leftWeightMap d m)
    (fun X => AssociatorTensor.leftCoefficientMap d.tensorEnrichedFunctor F G H X)
    (AssociatorTensor.leftWeightMap_naturality d m)
    (AssociatorTensor.leftCoefficientMap_naturality d.tensorEnrichedFunctor F G H) X

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorInclusion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]

attribute [local instance] Enriched.prodCategory

/-- The original fixed-right Day inclusion, provided by the canonical product inclusion. -/
def rightInclusion (e : E) : EnrichedFunctor V C (C × E) :=
  EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e

/-- The original fixed-right inclusion has its unchanged object formula. -/
theorem rightInclusion_obj (e : E) (i : C) :
    (rightInclusion (V := V) (C := C) e).obj i = (i, e) :=
  EnrichedFunctor.prodLeftInclusion_obj (V := V) (A := C) e i

/-- The original fixed-right inclusion retains the complete enriched Hom map. -/
theorem rightInclusion_map (e : E) (i j : C) :
    (rightInclusion (V := V) (C := C) e).map i j =
      (ρ_ (i ⟶[V] j)).inv ≫ (𝟙 (i ⟶[V] j) ⊗ₘ eId V e) :=
  EnrichedFunctor.prodLeftInclusion_map (V := V) (A := C) e i j

/-- The original fixed-left Day inclusion, provided by the canonical product inclusion. -/
def leftInclusion (e : E) : EnrichedFunctor V C (E × C) :=
  EnrichedFunctor.prodRightInclusion (V := V) (B := C) e

/-- The original fixed-left inclusion has its unchanged object formula. -/
@[simp]
theorem leftInclusion_obj (e : E) (i : C) :
    (leftInclusion (V := V) (C := C) e).obj i = (e, i) :=
  EnrichedFunctor.prodRightInclusion_obj (V := V) (B := C) e i

/-- The original fixed-left inclusion retains the complete enriched Hom map. -/
theorem leftInclusion_map (e : E) (i j : C) :
    (leftInclusion (V := V) (C := C) e).map i j =
      (λ_ (i ⟶[V] j)).inv ≫ (eId V e ⊗ₘ 𝟙 (i ⟶[V] j)) :=
  EnrichedFunctor.prodRightInclusion_map (V := V) (B := C) e i j

attribute [deprecated "Use EnrichedFunctor.prodLeftInclusion (A := C)."
  (since := "2026-11-05")] rightInclusion
attribute [deprecated "Use EnrichedFunctor.prodLeftInclusion_obj (A := C)."
  (since := "2026-11-05")] rightInclusion_obj
attribute [deprecated "Use EnrichedFunctor.prodLeftInclusion_map (A := C)."
  (since := "2026-11-05")] rightInclusion_map
attribute [deprecated "Use EnrichedFunctor.prodRightInclusion (B := C)."
  (since := "2026-11-05")] leftInclusion
attribute [deprecated "Use EnrichedFunctor.prodRightInclusion_obj (B := C)."
  (since := "2026-11-05")] leftInclusion_obj
attribute [deprecated "Use EnrichedFunctor.prodRightInclusion_map (B := C)."
  (since := "2026-11-05")] leftInclusion_map

end CategoryTheory.EnrichedDayKernel.AssociatorInclusion




namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
private theorem interchange (R S X Y : V) :
    (β_ (R ⊗ S) (X ⊗ Y)).hom ≫ tensorμ X Y R S =
      tensorμ R S X Y ≫ ((β_ R X).hom ⊗ₘ (β_ S Y).hom) := by
  simp only [tensorμ, BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, tensorHom_def, Category.assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding R Y]
  monoidal
  simp only [whiskerLeftIso_refl, whiskerRightIso_refl, Iso.trans_refl, Iso.refl_trans,
    whiskerLeftIso_hom,
    Iso.symm_hom, Iso.symm_self_id_assoc, Iso.trans_hom, whiskerLeft_hom_inv, Category.id_comp,
      cancelIso,
    whiskerLeft_inv_hom_assoc]

omit [MonoidalClosed V] in
private theorem productAction {X X' Y Y' Z Z' : V} (R S : V)
    (g : X ⟶ X') (h : Y ⟶ Y') (a : X' ⊗ R ⟶ Z) (b : Y' ⊗ S ⟶ Z') :
    (R ⊗ S) ◁ (g ⊗ₘ h) ≫ (β_ (R ⊗ S) (X' ⊗ Y')).hom ≫
        tensorμ X' Y' R S ≫ (a ⊗ₘ b) =
      tensorμ R S X Y ≫
        (((β_ R X).hom ≫ g ▷ R ≫ a) ⊗ₘ ((β_ S Y).hom ≫ h ▷ S ≫ b)) := by
  rw [BraidedCategory.braiding_naturality_right_assoc, tensorμ_natural_left_assoc,
    interchange_assoc]
  simp only [tensorHom_comp_tensorHom]

omit [MonoidalClosed V] in
private theorem unitMu (R X H : V) :
    (ρ_ R).inv ▷ (X ⊗ H) ≫ tensorμ R (𝟙_ V) X H =
      (α_ R X H).inv ≫ (R ⊗ X) ◁ (λ_ H).inv := by
  simp only [tensorμ, braiding_tensorUnit_left]
  monoidal

omit [MonoidalClosed V] in
private theorem unitActionTensor (R X H S Y : V) (q : 𝟙_ V ⟶ S)
    (a : R ⊗ X ⟶ Y) (b : S ⊗ H ⟶ H)
    (hb : (λ_ H).inv ≫ (q ⊗ₘ 𝟙 H) ≫ b = 𝟙 H) :
    (((ρ_ R).inv ≫ (𝟙 R ⊗ₘ q)) ⊗ₘ 𝟙 (X ⊗ H)) ≫
        tensorμ R S X H ≫ (a ⊗ₘ b) =
      (α_ R X H).inv ≫ (a ⊗ₘ 𝟙 H) := by
  have hm := tensorμ_natural_assoc (𝟙 R) q (𝟙 X) (𝟙 H) (a ⊗ₘ b)
  simp only [id_tensorHom_id] at hm
  rw [tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [← tensorHom_id (𝟙 R ⊗ₘ q) (X ⊗ H), hm]
  rw [← Category.assoc, unitMu, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [hb]


variable {E : Type uE} [EnrichedCategory V E]

private theorem rightAction_id (H : EnrichedFunctor V E V) (e : E) :
    (λ_ (H.obj e)).inv ≫ (eId V e ⊗ₘ 𝟙 (H.obj e)) ≫
        (β_ (e ⟶[V] e) (H.obj e)).hom ≫ MonoidalClosed.uncurry (H.map e e) =
      𝟙 (H.obj e) := by
  have h := congrArg MonoidalClosed.uncurry (H.map_id e)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality]
  simp only [Category.assoc]
  rw [leftUnitor_inv_braiding_assoc, id_tensorHom, h]
  simp only [Iso.inv_hom_id]


variable {C : Type uC} [EnrichedCategory V C]
attribute [local instance] Enriched.prodCategory

theorem rightSlice_action (Q : EnrichedFunctor V C V) (H : EnrichedFunctor V E V)
    (e : E) (a b : C) {A : V} (q : A ⟶ Q.obj a) :
    ((EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b ⊗ₘ
        (q ⊗ₘ 𝟙 (H.obj e))) ≫
        (β_ ((a, e) ⟶[V] (b, e)) (Q.obj a ⊗ H.obj e)).hom ≫
        MonoidalClosed.uncurry ((Q.externalTensor H).map (a, e) (b, e)) =
      (α_ (a ⟶[V] b) A (H.obj e)).inv ≫
        (((a ⟶[V] b) ◁ q ≫ (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
          MonoidalClosed.uncurry (Q.map a b)) ⊗ₘ 𝟙 (H.obj e)) := by
  let R : V := a ⟶[V] b
  let S : V := e ⟶[V] e
  let B := H.obj e
  let X := Q.obj a
  let Y := Q.obj b
  let i : R ⟶ R ⊗ S := (ρ_ R).inv ≫ (𝟙 R ⊗ₘ eId V e)
  let f : X ⊗ R ⟶ Y := MonoidalClosed.uncurry (Q.map a b)
  let g : B ⊗ S ⟶ B := MonoidalClosed.uncurry (H.map e e)
  let aq : R ⊗ A ⟶ Y := (β_ R A).hom ≫ q ▷ R ≫ f
  let bh : S ⊗ B ⟶ B := (β_ S B).hom ≫ g
  have h := productAction R S q (𝟙 B) f g
  simp only [id_whiskerRight, Category.id_comp] at h
  have hp := congrArg (fun z => (i ⊗ₘ 𝟙 (A ⊗ B)) ≫ z) h
  have hw : (i ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫ (β_ (R ⊗ S) (X ⊗ B)).hom ≫
      tensorμ X B R S ≫ (f ⊗ₘ g) =
      (i ⊗ₘ 𝟙 (A ⊗ B)) ≫ tensorμ R S A B ≫ (aq ⊗ₘ bh) := by
    simpa only [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id] using hp
  have hu : (i ⊗ₘ 𝟙 (A ⊗ B)) ≫ tensorμ R S A B ≫ (aq ⊗ₘ bh) =
      (α_ R A B).inv ≫ (aq ⊗ₘ 𝟙 B) :=
    unitActionTensor R A B S Y (eId V e) aq bh (rightAction_id H e)
  have ha : aq = R ◁ q ≫ (β_ R X).hom ≫ f :=
    (BraidedCategory.braiding_naturality_right_assoc R q f).symm
  let o : (X ⊗ B) ⊗ (R ⊗ S) ⟶ Y ⊗ B :=
    MonoidalClosed.uncurry ((Q.externalTensor H).map (a, e) (b, e))
  have ho : o = tensorμ X B R S ≫ (f ⊗ₘ g) :=
    EnrichedFunctor.externalTensor_uncurry Q H (a, e) (b, e)
  change (i ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫ (β_ (R ⊗ S) (X ⊗ B)).hom ≫ o =
    (α_ R A B).inv ≫ ((R ◁ q ≫ (β_ R X).hom ≫ f) ⊗ₘ 𝟙 B)
  rw [ho]
  exact hw.trans (hu.trans (congrArg (fun z => (α_ R A B).inv ≫ (z ⊗ₘ 𝟙 B)) ha))


section Coend
variable (W : EnrichedFunctor V (C × E)ᵒᵖ V)
  (Q : EnrichedFunctor V C V) (H : EnrichedFunctor V E V)
  [HasCoproduct (Enriched.weightedCoend.objects W (Q.externalTensor H))]
  [HasCoproduct (Enriched.weightedCoend.relations W (Q.externalTensor H))]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W (Q.externalTensor H))
    (Enriched.weightedCoend.rightMap W (Q.externalTensor H))]

theorem rightSlice_condition (e : E) (a b : C) {X : V} (q : X ⟶ Q.obj a) :
    W.obj (op (b, e)) ◁ (α_ (a ⟶[V] b) X (H.obj e)).hom ≫
        (α_ (W.obj (op (b, e))) (a ⟶[V] b) (X ⊗ H.obj e)).inv ≫
        ((W.obj (op (b, e)) ◁
            (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b ≫
          MonoidalClosed.uncurry (W.map (op (b, e)) (op (a, e)))) ⊗ₘ
          (q ⊗ₘ 𝟙 (H.obj e))) ≫ Enriched.weightedCoend.ι W (Q.externalTensor H) (a, e) =
      W.obj (op (b, e)) ◁
          (((a ⟶[V] b) ◁ q ≫ (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
            MonoidalClosed.uncurry (Q.map a b)) ⊗ₘ 𝟙 (H.obj e)) ≫
        Enriched.weightedCoend.ι W (Q.externalTensor H) (b, e) := by
  let R : V := a ⟶[V] b
  let S : V := (a, e) ⟶[V] (b, e)
  let B := H.obj e
  let A := Q.obj a ⊗ B
  let A' := Q.obj b ⊗ B
  let U := W.obj (op (b, e))
  let U' := W.obj (op (a, e))
  let Y := Enriched.weightedCoend W (Q.externalTensor H)
  let j : R ⟶ S := (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b
  let v : X ⊗ B ⟶ A := q ⊗ₘ 𝟙 B
  let w : U ⊗ S ⟶ U' := MonoidalClosed.uncurry (W.map (op (b, e)) (op (a, e)))
  let act : S ⊗ A ⟶ A' := (β_ S A).hom ≫
    MonoidalClosed.uncurry ((Q.externalTensor H).map (a, e) (b, e))
  let aq : R ⊗ X ⟶ Q.obj b := R ◁ q ≫ (β_ R (Q.obj a)).hom ≫
    MonoidalClosed.uncurry (Q.map a b)
  let l : U ⊗ (S ⊗ A) ⟶ U' ⊗ A := (α_ U S A).inv ≫ (w ⊗ₘ 𝟙 A)
  let r : U ⊗ (S ⊗ A) ⟶ U ⊗ A' := U ◁ act
  let ga : U' ⊗ A ⟶ Y := Enriched.weightedCoend.ι W (Q.externalTensor H) (a, e)
  let gb : U ⊗ A' ⟶ Y := Enriched.weightedCoend.ι W (Q.externalTensor H) (b, e)
  let pre : U ⊗ (R ⊗ (X ⊗ B)) ⟶ U ⊗ (S ⊗ A) := U ◁ (j ⊗ₘ v)
  let k : U ⊗ R ⟶ U' := U ◁ j ≫ w
  have hb : l ≫ ga = r ≫ gb := Enriched.weightedCoend.condition W (Q.externalTensor H) (a, e) (b, e)
  have h0 : pre ≫ l = (α_ U R (X ⊗ B)).inv ≫ (k ⊗ₘ v) := by
    have hα := associator_inv_naturality (𝟙 U) j v
    have hα' := congrArg (fun z => z ≫ (w ⊗ₘ 𝟙 A)) hα
    simpa only [pre, l, k, id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, Category.assoc] using hα'
  have hs : (j ⊗ₘ v) ≫ act = (α_ R X B).inv ≫ (aq ⊗ₘ 𝟙 B) :=
    rightSlice_action Q H e a b q
  have h1 : pre ≫ r = U ◁ ((α_ R X B).inv ≫ (aq ⊗ₘ 𝟙 B)) := by
    change U ◁ (j ⊗ₘ v) ≫ U ◁ act = _
    rw [← whiskerLeft_comp, hs]
  have h0' := congrArg (fun z => z ≫ ga) h0
  have h1' := congrArg (fun z => z ≫ gb) h1
  have hb' := congrArg (fun z => pre ≫ z) hb
  simp only [Category.assoc] at h0' h1' hb'
  have hc := h0'.symm.trans (hb'.trans h1')
  have hc' := congrArg (fun z => U ◁ (α_ R X B).hom ≫ z) hc
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv_assoc] at hc'
  change U ◁ (α_ R X B).hom ≫ (α_ U R (X ⊗ B)).inv ≫
      (k ⊗ₘ v) ≫ ga = U ◁ (aq ⊗ₘ 𝟙 B) ≫ gb
  exact hc'

end Coend

end CategoryTheory.EnrichedDayKernel.AssociatorContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)

attribute [local instance] Enriched.prodCategory

/-- Contract the inner represented Hom against the outer weight, holding the final index
  fixed through the enriched right inclusion. -/
abbrev sliceBase (p : I × I) (a : I × I) :
    (weight d.tensorEnrichedFunctor m).obj (op p) ⊗
        (d.tensorEnrichedFunctor.obj a ⟶[V] p.1) ⟶
      (weight d.tensorEnrichedFunctor m).obj (op (d.tensorEnrichedFunctor.obj a, p.2)) :=
  (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) p.2).map
        (d.tensorEnrichedFunctor.obj a) p.1 ≫
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
      (op p) (op (d.tensorEnrichedFunctor.obj a, p.2)))

/-- Reassociate a left nested coefficient word and contract its inner represented Hom
  into the flat left weight. -/
abbrev contractWord (p : I × I) (a : I × I) :
    AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a ⟶
      AssociatorFlat.leftObjects d F G H m (a, p.2) :=
  (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      (α_ (d.tensorEnrichedFunctor.obj a ⟶[V] p.1)
        (F.obj a.1 ⊗ G.obj a.2) (H.obj p.2)).hom ≫
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op p))
      (d.tensorEnrichedFunctor.obj a ⟶[V] p.1)
      ((F.obj a.1 ⊗ G.obj a.2) ⊗ H.obj p.2)).inv ≫
    (sliceBase d m p a ⊗ₘ 𝟙 ((F.obj a.1 ⊗ G.obj a.2) ⊗ H.obj p.2))

variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H m)]

theorem contractWord_generator_factorization (p : I × I) (a : I × I) :
    contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (a, p.2) ≫
        flatToNested d F G H m =
      AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor F G H m p a := by
  let x := d.tensorEnrichedFunctor.obj a
  let B := H.obj p.2
  let A := F.obj a.1 ⊗ G.obj a.2
  let R : V := x ⟶[V] p.1
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G p.1
  let X := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G x
  let u : A ⟶ X := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G a
  let g : R ⊗ A ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor F G p.1 a
  let o : X ⊗ R ⟶ Y := MonoidalClosed.uncurry
    (Output.map d.tensorEnrichedFunctor F G x p.1)
  have hd : R ◁ u ≫ (β_ R X).hom ≫ o = g := by
    have hm := Output.map_uncurry d.tensorEnrichedFunctor F G x p.1
    change o = (β_ R X).inv ≫
      MonoidalClosed.uncurry (Output.actionDesc d.tensorEnrichedFunctor F G x p.1) at hm
    rw [hm]
    simp only [Iso.hom_inv_id_assoc]
    exact AssociatorUnit.unitGenerator_action d.tensorEnrichedFunctor F G a p.1
  have hc := AssociatorContraction.rightSlice_condition
    (weight d.tensorEnrichedFunctor m) (Output.functor d.tensorEnrichedFunctor F G)
    H p.2 x p.1 u
  rw [leftGenerator_flatToNested]
  let Wb := (weight d.tensorEnrichedFunctor m).obj (op p)
  let Wa := (weight d.tensorEnrichedFunctor m).obj (op (x, p.2))
  let k : Wb ⊗ R ⟶ Wa := sliceBase d m p a
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m
  let ga : Wa ⊗ (X ⊗ B) ⟶ N := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m (x, p.2)
  let gb : Wb ⊗ (Y ⊗ B) ⟶ N := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m p
  change (Wb ◁ (α_ R A B).hom ≫ (α_ Wb R (A ⊗ B)).inv ≫
      (k ⊗ₘ 𝟙 (A ⊗ B))) ≫ (𝟙 Wa ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫ ga =
    Wb ◁ (g ▷ B) ≫ gb
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  have h := hc
  change (weight d.tensorEnrichedFunctor m).obj (op p) ◁ (α_ R A B).hom ≫
      (α_ ((weight d.tensorEnrichedFunctor m).obj (op p)) R (A ⊗ B)).inv ≫
      (sliceBase d m p a ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫
      EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H m (x, p.2) =
    (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      ((R ◁ u ≫ (β_ R X).hom ≫ o) ⊗ₘ 𝟙 B) ≫
      EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H m p at h
  rw [hd] at h
  simpa only [tensorHom_id] using h

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uC} [EnrichedCategory V A]

-- The private scalar calculation in WeightedCoend is repeated here until the reviewed
-- prerequisite snapshot can expose that general API.
omit [SymmetricCategory V] in
private theorem uncurryComposition {P Q R S T : V}
    (p : S ⟶ (ihom P).obj Q) (q : T ⟶ (ihom Q).obj R) :
    MonoidalClosed.uncurry ((p ⊗ₘ q) ≫ eComp V P Q R) =
      (α_ P S T).inv ≫ MonoidalClosed.uncurry p ▷ T ≫
        MonoidalClosed.uncurry q := by
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_comp, MonoidalClosed.comp_eq,
    MonoidalClosed.uncurry_curry, MonoidalClosed.compTranspose_eq]
  have hTensor : P ◁ (p ⊗ₘ q) ≫
      (α_ P ((ihom P).obj Q) ((ihom Q).obj R)).inv =
    (α_ P S T).inv ≫ ((P ◁ p) ▷ T) ≫ (P ⊗ (ihom P).obj Q) ◁ q := by
    simpa only [id_tensorHom, tensorHom_def, id_whiskerRight, Category.id_comp,
      comp_whiskerRight] using associator_inv_naturality (𝟙 P) p q
  rw [← Category.assoc, hTensor]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    ← MonoidalClosed.uncurry_eq]
  dsimp
  rw [← MonoidalClosed.uncurry_eq]

omit [SymmetricCategory V] in
@[reassoc]
theorem action_comp (F : EnrichedFunctor V A V) (a b c : A) :
    (α_ (F.obj a) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
      MonoidalClosed.uncurry (F.map a b) ▷ (b ⟶[V] c) ≫
      MonoidalClosed.uncurry (F.map b c) =
    F.obj a ◁ eComp V a b c ≫ MonoidalClosed.uncurry (F.map a c) := by
  have h := congrArg MonoidalClosed.uncurry (F.map_comp a b c)
  rw [MonoidalClosed.uncurry_natural_left, uncurryComposition] at h
  exact h.symm

@[reassoc]
theorem weightAction_comp (W : EnrichedFunctor V Aᵒᵖ V) (a b c : A) :
    (α_ (W.obj (op c)) (b ⟶[V] c) (a ⟶[V] b)).inv ≫
      MonoidalClosed.uncurry (W.map (op c) (op b)) ▷ (a ⟶[V] b) ≫
      MonoidalClosed.uncurry (W.map (op b) (op a)) =
    W.obj (op c) ◁ ((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫ eComp V a b c) ≫
      MonoidalClosed.uncurry (W.map (op c) (op a)) := by
  have h := action_comp W (op c) (op b) (op a)
  change (α_ (W.obj (op c)) (b ⟶[V] c) (a ⟶[V] b)).inv ≫
      MonoidalClosed.uncurry (W.map (op c) (op b)) ▷ (a ⟶[V] b) ≫
      MonoidalClosed.uncurry (W.map (op b) (op a)) =
    W.obj (op c) ◁ eComp V (op c) (op b) (op a) ≫
      MonoidalClosed.uncurry (W.map (op c) (op a)) at h
  rw [eComp_op_eq] at h
  exact h

@[reassoc]
theorem weightAction_comp_maps (W : EnrichedFunctor V Aᵒᵖ V) (a b c : A)
    {P Q : V} (f : P ⟶ (b ⟶[V] c)) (g : Q ⟶ (a ⟶[V] b)) :
    (α_ (W.obj (op c)) P Q).inv ≫
      ((W.obj (op c) ◁ f ≫ MonoidalClosed.uncurry (W.map (op c) (op b))) ⊗ₘ g) ≫
      MonoidalClosed.uncurry (W.map (op b) (op a)) =
    W.obj (op c) ◁ ((f ⊗ₘ g) ≫ (β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫
        eComp V a b c) ≫ MonoidalClosed.uncurry (W.map (op c) (op a)) := by
  let U := W.obj (op c)
  let R : V := b ⟶[V] c
  let S : V := a ⟶[V] b
  let v : U ⊗ R ⟶ W.obj (op b) :=
    MonoidalClosed.uncurry (W.map (op c) (op b))
  let w : W.obj (op b) ⊗ S ⟶ W.obj (op a) :=
    MonoidalClosed.uncurry (W.map (op b) (op a))
  have hn : U ◁ (f ⊗ₘ g) ≫ (α_ U R S).inv =
      (α_ U P Q).inv ≫ ((U ◁ f) ⊗ₘ g) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 U) f g
  have ht : ((U ◁ f) ⊗ₘ g) ≫ v ▷ S = (U ◁ f ≫ v) ⊗ₘ g := by
    rw [← tensorHom_id]
    exact (tensorHom_comp_tensorHom (U ◁ f) g v (𝟙 S)).trans
      (congrArg (fun z : Q ⟶ S => (U ◁ f ≫ v) ⊗ₘ z) (Category.comp_id g))
  have hm : (α_ U P Q).inv ≫ ((U ◁ f ≫ v) ⊗ₘ g) ≫ w =
      U ◁ (f ⊗ₘ g) ≫ (α_ U R S).inv ≫ v ▷ S ≫ w := by
    rw [← ht]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ v ▷ S ≫ w) hn.symm
  change (α_ U P Q).inv ≫ ((U ◁ f ≫ v) ⊗ₘ g) ≫ w = _
  rw [hm]
  have h := weightAction_comp W a b c
  change (α_ U R S).inv ≫ v ▷ S ≫ w =
    U ◁ ((β_ R S).hom ≫ eComp V a b c) ≫
      MonoidalClosed.uncurry (W.map (op c) (op a)) at h
  rw [h]
  exact (whiskerLeft_comp_assoc U (f ⊗ₘ g)
    ((β_ R S).hom ≫ eComp V a b c) _).symm

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorInclusion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- The actual fixed-second inclusion commutes with the full map of a product functor. -/
theorem rightInclusion_product_map (T : EnrichedFunctor V C K) (e : E) (a b : C) :
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b ≫
      (prodEnrichedFunctor T (EnrichedFunctor.id V E)).map (a, e) (b, e) =
    T.map a b ≫
      (EnrichedFunctor.prodLeftInclusion (V := V) (A := K) e).map (T.obj a) (T.obj b) := by
  let R : V := a ⟶[V] b
  let S : V := T.obj a ⟶[V] T.obj b
  let P : V := e ⟶[V] e
  let t : R ⟶ S := T.map a b
  let q : 𝟙_ V ⟶ P := eId V e
  unfold EnrichedFunctor.prodLeftInclusion prodEnrichedFunctor EnrichedFunctor.id
  change ((ρ_ R).inv ≫ (𝟙 R ⊗ₘ q)) ≫ (t ⊗ₘ 𝟙 P) =
    t ≫ (ρ_ S).inv ≫ (𝟙 S ⊗ₘ q)
  simp only [Category.assoc]
  have ht : (𝟙 R ⊗ₘ q) ≫ (t ⊗ₘ 𝟙 P) = t ⊗ₘ q := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hu : t ▷ (𝟙_ V) ≫ (𝟙 S ⊗ₘ q) = t ⊗ₘ q := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [ht, ← hu, rightUnitor_inv_naturality_assoc]

/-- Lift the original full precomposition word through the actual fixed-second inclusion. -/
@[reassoc]
theorem rightInclusion_precomposition (e : E) (a b c : C)
    {P : V} (t : P ⟶ (a ⟶[V] b)) :
    ((EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map b c ⊗ₘ
        (t ≫ (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b)) ≫
      (β_ ((b, e) ⟶[V] (c, e)) ((a, e) ⟶[V] (b, e))).hom ≫
      eComp V (a, e) (b, e) (c, e) =
    (b ⟶[V] c) ◁ t ≫ (β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫
      eComp V a b c ≫ (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a c := by
  let J := EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e
  let R : V := b ⟶[V] c
  let S : V := a ⟶[V] b
  let j1 : R ⟶ (J.obj b ⟶[V] J.obj c) := J.map b c
  let j2 : S ⟶ (J.obj a ⟶[V] J.obj b) := J.map a b
  let k := eComp V (J.obj a) (J.obj b) (J.obj c)
  have hn := BraidedCategory.braiding_naturality_assoc j1 (t ≫ j2) k
  have hc : (j2 ⊗ₘ j1) ≫ k = eComp V a b c ≫ J.map a c :=
    (J.map_comp a b c).symm
  change (j1 ⊗ₘ (t ≫ j2)) ≫
      (β_ (J.obj b ⟶[V] J.obj c) (J.obj a ⟶[V] J.obj b)).hom ≫ k =
    R ◁ t ≫ (β_ R S).hom ≫ eComp V a b c ≫ J.map a c
  rw [hn]
  have ht : ((t ≫ j2) ⊗ₘ j1) = (t ⊗ₘ 𝟙 R) ≫ (j2 ⊗ₘ j1) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht]
  simp only [Category.assoc]
  rw [hc]
  let z : S ⊗ R ⟶ (J.obj a ⟶[V] J.obj c) :=
    eComp V a b c ≫ J.map a c
  rw [tensorHom_id]
  change (β_ R P).hom ≫ t ▷ R ≫ z = R ◁ t ≫ (β_ R S).hom ≫ z
  exact (BraidedCategory.braiding_naturality_right_assoc R t z).symm

end CategoryTheory.EnrichedDayKernel.AssociatorInclusion

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- The full weight action after the original fixed-second enriched inclusion. -/
abbrev rightSliceWeight (W : EnrichedFunctor V (C × E)ᵒᵖ V) (e : E) (a b : C) :
    W.obj (op (b, e)) ⊗ (a ⟶[V] b) ⟶ W.obj (op (a, e)) :=
  W.obj (op (b, e)) ◁ (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map a b ≫
    MonoidalClosed.uncurry (W.map (op (b, e)) (op (a, e)))

/-- Composition of the full slice-weight action preserves the original input map. -/
@[reassoc]
theorem rightSliceWeight_comp (W : EnrichedFunctor V (C × E)ᵒᵖ V)
    (e : E) (a b c : C) {P : V} (t : P ⟶ (a ⟶[V] b)) :
    (α_ (W.obj (op (c, e))) (b ⟶[V] c) P).inv ≫
      (rightSliceWeight W e b c ⊗ₘ t) ≫ rightSliceWeight W e a b =
    W.obj (op (c, e)) ◁ ((b ⟶[V] c) ◁ t ≫
      (β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫ eComp V a b c) ≫
      rightSliceWeight W e a c := by
  let J := EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e
  let R : V := b ⟶[V] c
  let S : V := a ⟶[V] b
  let U := W.obj (op (J.obj c))
  let Y := W.obj (op (J.obj b))
  let X := W.obj (op (J.obj a))
  let j1 : R ⟶ (J.obj b ⟶[V] J.obj c) := J.map b c
  let j2 : S ⟶ (J.obj a ⟶[V] J.obj b) := J.map a b
  let v : U ⊗ (J.obj b ⟶[V] J.obj c) ⟶ Y :=
    MonoidalClosed.uncurry (W.map (op (J.obj c)) (op (J.obj b)))
  let w : Y ⊗ (J.obj a ⟶[V] J.obj b) ⟶ X :=
    MonoidalClosed.uncurry (W.map (op (J.obj b)) (op (J.obj a)))
  let k : U ⊗ R ⟶ Y := U ◁ j1 ≫ v
  let z : U ⊗ (J.obj a ⟶[V] J.obj c) ⟶ X :=
    MonoidalClosed.uncurry (W.map (op (J.obj c)) (op (J.obj a)))
  have hf : (k ⊗ₘ t) ≫ Y ◁ j2 = k ⊗ₘ (t ≫ j2) := by
    rw [← id_tensorHom]
    exact (tensorHom_comp_tensorHom k t (𝟙 Y) j2).trans
      (congrArg (fun u : U ⊗ R ⟶ Y => u ⊗ₘ (t ≫ j2)) (Category.comp_id k))
  have hm := weightAction_comp_maps W (J.obj a) (J.obj b) (J.obj c) j1 (t ≫ j2)
  change (α_ U R P).inv ≫ (k ⊗ₘ (t ≫ j2)) ≫ w =
    U ◁ ((j1 ⊗ₘ (t ≫ j2)) ≫
      (β_ (J.obj b ⟶[V] J.obj c) (J.obj a ⟶[V] J.obj b)).hom ≫
      eComp V (J.obj a) (J.obj b) (J.obj c)) ≫ z at hm
  have hc := AssociatorInclusion.rightInclusion_precomposition e a b c t
  change (j1 ⊗ₘ (t ≫ j2)) ≫
      (β_ (J.obj b ⟶[V] J.obj c) (J.obj a ⟶[V] J.obj b)).hom ≫
      eComp V (J.obj a) (J.obj b) (J.obj c) =
    R ◁ t ≫ (β_ R S).hom ≫ eComp V a b c ≫ J.map a c at hc
  change (α_ U R P).inv ≫ (k ⊗ₘ t) ≫ Y ◁ j2 ≫ w =
    U ◁ (R ◁ t ≫ (β_ R S).hom ≫ eComp V a b c) ≫ U ◁ J.map a c ≫ z
  have hf' : (k ⊗ₘ t) ≫ Y ◁ j2 ≫ w = (k ⊗ₘ (t ≫ j2)) ≫ w := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ w) hf
  rw [hf', hm, hc]
  simp only [whiskerLeft_comp, Category.assoc]

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The full flat weight action along the original fixed-second triple inclusion. -/
abbrev flatInnerSlice (e : I) (a b : I × I) :
    (AssociatorIndex.leftWeight d m).obj (op (b, e)) ⊗ (a ⟶[V] b) ⟶
      (AssociatorIndex.leftWeight d m).obj (op (a, e)) :=
  (AssociatorIndex.leftWeight d m).obj (op (b, e)) ◁
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I × I) e).map a b ≫
      MonoidalClosed.uncurry ((AssociatorIndex.leftWeight d m).map (op (b, e)) (op (a, e)))

/-- The complete flat Hom action is precisely the original tensor map followed by the slice. -/
theorem flatInnerSlice_original (e : I) (a b : I × I) :
    flatInnerSlice d m e a b =
      (AssociatorIndex.leftWeight d m).obj (op (b, e)) ◁ d.tensorEnrichedFunctor.map a b ≫
        AssociatorContraction.rightSliceWeight (weight d.tensorEnrichedFunctor m) e
          (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b) := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let Q := AssociatorIndex.leftWeight d m
  let S := AssociatorTensor.leftProduct d
  let U := Q.obj (op (b, e))
  let P : V := a ⟶[V] b
  let R : V := T.obj a ⟶[V] T.obj b
  let j : P ⟶ ((a, e) ⟶[V] (b, e)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I × I) e).map a b
  let k : R ⟶ ((T.obj a, e) ⟶[V] (T.obj b, e)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) e).map (T.obj a) (T.obj b)
  let t : P ⟶ R := T.map a b
  let s : ((a, e) ⟶[V] (b, e)) ⟶ ((T.obj a, e) ⟶[V] (T.obj b, e)) :=
    S.map (a, e) (b, e)
  let v : U ⊗ ((a, e) ⟶[V] (b, e)) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (Q.map (op (b, e)) (op (a, e)))
  let w : U ⊗ ((T.obj a, e) ⟶[V] (T.obj b, e)) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (W.map (op (T.obj b, e)) (op (T.obj a, e)))
  have hv : v = U ◁ s ≫ w := by
    have h := AssociatorTensor.leftWeightMap_naturality d m (a, e) (b, e)
    change v ≫ 𝟙 (Q.obj (op (a, e))) = (𝟙 U ⊗ₘ s) ≫ w at h
    simpa only [Category.comp_id, id_tensorHom] using h
  have hj : j ≫ s = t ≫ k := AssociatorInclusion.rightInclusion_product_map T e a b
  change U ◁ j ≫ v = U ◁ t ≫ U ◁ k ≫ w
  calc
    _ = U ◁ (j ≫ s) ≫ w := by
      rw [hv]
      exact (whiskerLeft_comp_assoc U j s w).symm
    _ = U ◁ (t ≫ k) ≫ w := congrArg (fun z => U ◁ z ≫ w) hj
    _ = _ := whiskerLeft_comp_assoc U t k w

/-- Both original inner weight legs contract to the full flat inner Hom action. -/
@[reassoc]
theorem sliceBase_inner (p : I × I) (a b : I × I) :
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op p))
        (d.tensorEnrichedFunctor.obj b ⟶[V] p.1) (a ⟶[V] b)).inv ≫
      (sliceBase d m p b ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ flatInnerSlice d m p.2 a b =
    (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor p.1).map (op b) (op a)) ≫
      sliceBase d m p a := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let U := W.obj (op p)
  let Y := W.obj (op (T.obj b, p.2))
  let R : V := T.obj b ⟶[V] p.1
  let P : V := a ⟶[V] b
  let S : V := T.obj a ⟶[V] T.obj b
  let t : P ⟶ S := T.map a b
  let k : U ⊗ R ⟶ Y := AssociatorContraction.rightSliceWeight W p.2 (T.obj b) p.1
  let l : Y ⊗ S ⟶ W.obj (op (T.obj a, p.2)) :=
    AssociatorContraction.rightSliceWeight W p.2 (T.obj a) (T.obj b)
  let z : U ⊗ (T.obj a ⟶[V] p.1) ⟶ W.obj (op (T.obj a, p.2)) :=
    AssociatorContraction.rightSliceWeight W p.2 (T.obj a) p.1
  have hf : (k ⊗ₘ 𝟙 P) ≫ Y ◁ t = k ⊗ₘ t := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id k) (Category.id_comp t)
  have h := AssociatorContraction.rightSliceWeight_comp W p.2 (T.obj a) (T.obj b) p.1 t
  change (α_ U R P).inv ≫ (k ⊗ₘ t) ≫ l =
    U ◁ (R ◁ t ≫ (β_ R S).hom ≫ eComp V (T.obj a) (T.obj b) p.1) ≫ z at h
  rw [flatInnerSlice_original, weight_uncurry_map]
  change (α_ U R P).inv ≫ (k ⊗ₘ 𝟙 P) ≫ Y ◁ t ≫ l =
    U ◁ (R ◁ t ≫ (β_ R S).hom ≫ eComp V (T.obj a) (T.obj b) p.1) ≫ z
  have hf' : (k ⊗ₘ 𝟙 P) ≫ Y ◁ t ≫ l = (k ⊗ₘ t) ≫ l := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ l) hf
  rw [hf']
  exact h

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- Reassociate the original nested coefficient word before applying its weight contraction. -/
abbrev contract {W R T : V} (k : W ⊗ R ⟶ T) (A B : V) :
    W ⊗ ((R ⊗ A) ⊗ B) ⟶ T ⊗ (A ⊗ B) :=
  W ◁ (α_ R A B).hom ≫ (α_ W R (A ⊗ B)).inv ≫ (k ⊗ₘ 𝟙 (A ⊗ B))

/-- This reassociation respects the complete two coefficient maps. -/
@[reassoc]
theorem contract_naturality {W R T A A' B B' : V} (k : W ⊗ R ⟶ T)
    (f : A ⟶ A') (g : B ⟶ B') :
    W ◁ ((R ◁ f) ⊗ₘ g) ≫ contract k A' B' =
      contract k A B ≫ T ◁ (f ⊗ₘ g) := by
  have hα : ((R ◁ f) ⊗ₘ g) ≫ (α_ R A' B').hom =
      (α_ R A B).hom ≫ R ◁ (f ⊗ₘ g) := by
    simpa only [id_tensorHom] using associator_naturality (𝟙 R) f g
  simp only [contract, Category.assoc]
  rw [← whiskerLeft_comp_assoc, hα, whiskerLeft_comp_assoc,
    associator_inv_naturality_right_assoc]
  simp only [tensorHom_id]
  rw [whisker_exchange]

/-- The actual inner weight equality contracts with the same complete coefficient word. -/
@[reassoc]
theorem contract_inner_weight {W R S P X Y A B : V}
    (v : R ⊗ P ⟶ S) (k : W ⊗ S ⟶ X) (l : W ⊗ R ⟶ Y) (q : Y ⊗ P ⟶ X)
    (h : (α_ W R P).inv ≫ (l ⊗ₘ 𝟙 P) ≫ q = W ◁ v ≫ k) :
    W ◁ (((α_ R P A).inv ≫ (v ⊗ₘ 𝟙 A)) ▷ B) ≫ contract k A B =
    contract l (P ⊗ A) B ≫ Y ◁ (α_ P A B).hom ≫
      (α_ Y P (A ⊗ B)).inv ≫ (q ⊗ₘ 𝟙 (A ⊗ B)) := by
  let C := A ⊗ B
  let D := (P ⊗ A) ⊗ B
  have hn : W ◁ (v ▷ A ▷ B) ≫ W ◁ (α_ S A B).hom =
      W ◁ (α_ (R ⊗ P) A B).hom ≫ W ◁ (v ▷ C) := by
    rw [← whiskerLeft_comp, associator_naturality_left, whiskerLeft_comp]
  have hn' : W ◁ (v ▷ A ▷ B) ≫ W ◁ (α_ S A B).hom ≫
      (α_ W S C).inv ≫ k ▷ C =
    W ◁ (α_ (R ⊗ P) A B).hom ≫ W ◁ (v ▷ C) ≫
      (α_ W S C).inv ≫ k ▷ C := by
    simpa only [Category.assoc] using
      congrArg (fun z => z ≫ (α_ W S C).inv ≫ k ▷ C) hn
  have hw : (W ◁ v ≫ k) ▷ C =
      ((α_ W R P).inv ≫ l ▷ P ≫ q) ▷ C := by
    simpa only [tensorHom_id] using congrArg (fun z => z ▷ C) h.symm
  simp only [contract, Category.assoc, tensorHom_id, comp_whiskerRight, whiskerLeft_comp]
  change W ◁ ((α_ R P A).inv ▷ B) ≫ W ◁ (v ▷ A ▷ B) ≫
      W ◁ (α_ S A B).hom ≫ (α_ W S C).inv ≫ k ▷ C =
    W ◁ (α_ R (P ⊗ A) B).hom ≫ (α_ W R D).inv ≫ l ▷ D ≫
      Y ◁ (α_ P A B).hom ≫ (α_ Y P C).inv ≫ q ▷ C
  rw [hn', associator_inv_naturality_middle_assoc, ← comp_whiskerRight, hw]
  simp only [comp_whiskerRight]
  rw [← whisker_exchange_assoc l (α_ P A B).hom,
    associator_inv_naturality_left_assoc]
  have hp : W ◁ ((α_ R P A).inv ▷ B) ≫ W ◁ (α_ (R ⊗ P) A B).hom ≫
      (α_ W (R ⊗ P) C).inv ≫ (α_ W R P).inv ▷ C =
    W ◁ (α_ R (P ⊗ A) B).hom ≫ (α_ W R D).inv ≫
      (W ⊗ R) ◁ (α_ P A B).hom ≫ (α_ (W ⊗ R) P C).inv := by monoidal
  simpa only [Category.assoc, C] using
    congrArg (fun z => z ≫ l ▷ P ▷ C ≫ q ▷ C) hp

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]

/-- Contraction identifies both complete original inner relation faces after the flat projection. -/
@[reassoc]
theorem contractWord_inner (p : I × I) (a b : I × I) :
    AssociatorFaces.Left.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a b ≫
      contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (a, p.2) =
    AssociatorFaces.Left.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a b ≫
      contractWord d F G H m p b ≫ AssociatorFlat.leftGenerator d F G H m (b, p.2) := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let Q := AssociatorIndex.leftWeight d m
  let U := W.obj (op p)
  let A := F.obj a.1 ⊗ G.obj a.2
  let A' := F.obj b.1 ⊗ G.obj b.2
  let B := H.obj p.2
  let R : V := T.obj b ⟶[V] p.1
  let S : V := T.obj a ⟶[V] p.1
  let P : V := a ⟶[V] b
  let X := Q.obj (op (a, p.2))
  let Y := Q.obj (op (b, p.2))
  let v : R ⊗ P ⟶ S := MonoidalClosed.uncurry ((weight T p.1).map (op b) (op a))
  let k : U ⊗ S ⟶ X := sliceBase d m p a
  let l : U ⊗ R ⟶ Y := sliceBase d m p b
  let q : Y ⊗ P ⟶ X := flatInnerSlice d m p.2 a b
  let f : P ⊗ A ⟶ A' := (β_ P A).hom ≫ MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  let Z := AssociatorFlat.leftPoint d F G H m
  let ga : X ⊗ (A ⊗ B) ⟶ Z := AssociatorFlat.leftGenerator d F G H m (a, p.2)
  let gb : Y ⊗ (A' ⊗ B) ⟶ Z := AssociatorFlat.leftGenerator d F G H m (b, p.2)
  let pre := AssociatorContraction.contract l (P ⊗ A) B
  have h0 := AssociatorContraction.contract_inner_weight (A := A) (B := B)
    v k l q (sliceBase_inner d m p a b)
  have h0' : U ◁ (((α_ R P A).inv ≫ (v ⊗ₘ 𝟙 A)) ▷ B) ≫
      AssociatorContraction.contract k A B ≫ ga =
    pre ≫ Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga := by
    simpa only [pre, AssociatorContraction.contract, Category.assoc] using
      congrArg (fun z => z ≫ ga) h0
  have hb := AssociatorContraction.rightSlice_condition Q (F.externalTensor G) H p.2 a b (𝟙 A)
  change Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) ≫ ga =
    Y ◁ ((P ◁ 𝟙 A ≫ f) ⊗ₘ 𝟙 B) ≫ gb at hb
  rw [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hb
  have hb' : pre ≫ Y ◁ (α_ P A B).hom ≫ (α_ Y P (A ⊗ B)).inv ≫
      (q ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga = pre ≫ Y ◁ (f ⊗ₘ 𝟙 B) ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => pre ≫ z) hb
  have h1 := AssociatorContraction.contract_naturality l f (𝟙 B)
  have h1' : U ◁ ((R ◁ f) ▷ B) ≫ AssociatorContraction.contract l A' B ≫ gb =
      pre ≫ Y ◁ (f ⊗ₘ 𝟙 B) ≫ gb := by
    simpa only [pre, AssociatorContraction.contract, Category.assoc, tensorHom_id] using
      congrArg (fun z => z ≫ gb) h1
  change U ◁ (((α_ R P A).inv ≫ (v ⊗ₘ 𝟙 A)) ▷ B) ≫
      AssociatorContraction.contract k A B ≫ ga =
    U ◁ ((R ◁ f) ▷ B) ≫ AssociatorContraction.contract l A' B ≫ gb
  simpa only [Category.assoc] using h0'.trans (hb'.trans h1'.symm)

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening



namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
/-- Move the full inner Hom to the weight side while preserving the ordered coefficients. -/
abbrev frontHomIso (R B A : V) : B ⊗ (R ⊗ A) ≅ R ⊗ (B ⊗ A) :=
  (α_ B R A).symm ≪≫ tensorIso (β_ B R) (Iso.refl A) ≪≫ α_ R B A

omit [MonoidalClosed V] in
@[reassoc]
private theorem interchange (R S X Y : V) :
    (β_ (R ⊗ S) (X ⊗ Y)).hom ≫ tensorμ X Y R S =
      tensorμ R S X Y ≫ ((β_ R X).hom ⊗ₘ (β_ S Y).hom) := by
  simp only [tensorμ, BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, tensorHom_def, Category.assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding R Y]
  monoidal
  simp only [whiskerLeftIso_refl, whiskerRightIso_refl, Iso.trans_refl, Iso.refl_trans,
    whiskerLeftIso_hom,
    Iso.symm_hom, Iso.symm_self_id_assoc, Iso.trans_hom, whiskerLeft_hom_inv, Category.id_comp,
      cancelIso,
    whiskerLeft_inv_hom_assoc]

omit [MonoidalClosed V] in
private theorem productAction {X X' Y Y' Z Z' : V} (R S : V)
    (g : X ⟶ X') (h : Y ⟶ Y') (a : X' ⊗ R ⟶ Z) (b : Y' ⊗ S ⟶ Z') :
    (R ⊗ S) ◁ (g ⊗ₘ h) ≫ (β_ (R ⊗ S) (X' ⊗ Y')).hom ≫
        tensorμ X' Y' R S ≫ (a ⊗ₘ b) =
      tensorμ R S X Y ≫
        (((β_ R X).hom ≫ g ▷ R ≫ a) ⊗ₘ ((β_ S Y).hom ≫ h ▷ S ≫ b)) := by
  rw [BraidedCategory.braiding_naturality_right_assoc, tensorμ_natural_left_assoc,
    interchange_assoc]
  simp only [tensorHom_comp_tensorHom]

omit [MonoidalClosed V] in
private theorem unitMuLeft (R B A : V) :
    (λ_ R).inv ▷ (B ⊗ A) ≫ tensorμ (𝟙_ V) R B A =
      (frontHomIso R B A).inv ≫ (λ_ B).inv ▷ (R ⊗ A) := by
  simp only [tensorμ, frontHomIso, Iso.trans_inv, Iso.symm_inv,
    tensorIso_inv, Iso.refl_inv, Category.assoc]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding B R]
  have hp : (λ_ R).inv ▷ (B ⊗ A) ≫ (α_ (𝟙_ V) R (B ⊗ A)).hom =
      (λ_ (R ⊗ (B ⊗ A))).inv := by monoidal
  slice_lhs 1 2 => rw [hp]
  simp only [tensorHom_id, Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc, ← leftUnitor_inv_naturality_assoc,
    ← leftUnitor_inv_naturality_assoc]
  have ht : (λ_ (B ⊗ (R ⊗ A))).inv ≫ (α_ (𝟙_ V) B (R ⊗ A)).inv =
      (λ_ B).inv ▷ (R ⊗ A) := by monoidal
  rw [ht]

omit [MonoidalClosed V] in
private theorem unitActionTensorLeft (R B A S Y : V) (q : 𝟙_ V ⟶ S)
    (b : S ⊗ B ⟶ B) (a : R ⊗ A ⟶ Y)
    (hb : (λ_ B).inv ≫ (q ⊗ₘ 𝟙 B) ≫ b = 𝟙 B) :
    (((λ_ R).inv ≫ (q ⊗ₘ 𝟙 R)) ⊗ₘ 𝟙 (B ⊗ A)) ≫
        tensorμ S R B A ≫ (b ⊗ₘ a) =
      (frontHomIso R B A).inv ≫ B ◁ a := by
  have hm := tensorμ_natural_assoc q (𝟙 R) (𝟙 B) (𝟙 A) (b ⊗ₘ a)
  simp only [id_tensorHom_id] at hm
  rw [tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [← tensorHom_id (q ⊗ₘ 𝟙 R) (B ⊗ A), hm]
  rw [← Category.assoc, unitMuLeft, Category.assoc]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [hb]
  exact congrArg (fun f => (frontHomIso R B A).inv ≫ f) (id_tensorHom B a)

variable {E : Type uE} [EnrichedCategory V E]
private theorem leftAction_id (F : EnrichedFunctor V E V) (e : E) :
    (λ_ (F.obj e)).inv ≫ (eId V e ⊗ₘ 𝟙 (F.obj e)) ≫
        (β_ (e ⟶[V] e) (F.obj e)).hom ≫ MonoidalClosed.uncurry (F.map e e) =
      𝟙 (F.obj e) := by
  have h := congrArg MonoidalClosed.uncurry (F.map_id e)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality]
  simp only [Category.assoc]
  rw [leftUnitor_inv_braiding_assoc, id_tensorHom, h]
  simp only [Iso.inv_hom_id]

variable {C : Type uC} [EnrichedCategory V C]
attribute [local instance] Enriched.prodCategory

/-- The full external action along the fixed first input contracts its actual identity. -/
theorem leftSlice_action (F : EnrichedFunctor V E V) (Q : EnrichedFunctor V C V)
    (e : E) (a b : C) {A : V} (q : A ⟶ Q.obj a) :
    ((EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a b ⊗ₘ
        (𝟙 (F.obj e) ⊗ₘ q)) ≫
        (β_ ((e, a) ⟶[V] (e, b)) (F.obj e ⊗ Q.obj a)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor Q).map (e, a) (e, b)) =
      (frontHomIso (a ⟶[V] b) (F.obj e) A).inv ≫ F.obj e ◁
        ((a ⟶[V] b) ◁ q ≫ (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
          MonoidalClosed.uncurry (Q.map a b)) := by
  let R : V := a ⟶[V] b
  let S : V := e ⟶[V] e
  let B := F.obj e
  let X := Q.obj a
  let Y := Q.obj b
  let i : R ⟶ S ⊗ R := (λ_ R).inv ≫ (eId V e ⊗ₘ 𝟙 R)
  let f : B ⊗ S ⟶ B := MonoidalClosed.uncurry (F.map e e)
  let g : X ⊗ R ⟶ Y := MonoidalClosed.uncurry (Q.map a b)
  let bf : S ⊗ B ⟶ B := (β_ S B).hom ≫ f
  let aq : R ⊗ A ⟶ Y := (β_ R A).hom ≫ q ▷ R ≫ g
  have h := productAction S R (𝟙 B) q f g
  simp only [id_whiskerRight, Category.id_comp] at h
  have hp := congrArg (fun z => (i ⊗ₘ 𝟙 (B ⊗ A)) ≫ z) h
  have hw : (i ⊗ₘ (𝟙 B ⊗ₘ q)) ≫ (β_ (S ⊗ R) (B ⊗ X)).hom ≫
      tensorμ B X S R ≫ (f ⊗ₘ g) =
      (i ⊗ₘ 𝟙 (B ⊗ A)) ≫ tensorμ S R B A ≫ (bf ⊗ₘ aq) := by
    simpa only [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id] using hp
  have hu : (i ⊗ₘ 𝟙 (B ⊗ A)) ≫ tensorμ S R B A ≫ (bf ⊗ₘ aq) =
      (frontHomIso R B A).inv ≫ B ◁ aq :=
    unitActionTensorLeft R B A S Y (eId V e) bf aq (leftAction_id F e)
  have ha : aq = R ◁ q ≫ (β_ R X).hom ≫ g :=
    (BraidedCategory.braiding_naturality_right_assoc R q g).symm
  let o : (B ⊗ X) ⊗ (S ⊗ R) ⟶ B ⊗ Y :=
    MonoidalClosed.uncurry ((F.externalTensor Q).map (e, a) (e, b))
  have ho : o = tensorμ B X S R ≫ (f ⊗ₘ g) :=
    EnrichedFunctor.externalTensor_uncurry F Q (e, a) (e, b)
  change (i ⊗ₘ (𝟙 B ⊗ₘ q)) ≫ (β_ (S ⊗ R) (B ⊗ X)).hom ≫ o =
    (frontHomIso R B A).inv ≫ B ◁ (R ◁ q ≫ (β_ R X).hom ≫ g)
  rw [ho]
  exact hw.trans (hu.trans (congrArg (fun z => (frontHomIso R B A).inv ≫ B ◁ z) ha))

section Coend
variable (W : EnrichedFunctor V (E × C)ᵒᵖ V)
  (F : EnrichedFunctor V E V) (Q : EnrichedFunctor V C V)
  [HasCoproduct (Enriched.weightedCoend.objects W (F.externalTensor Q))]
  [HasCoproduct (Enriched.weightedCoend.relations W (F.externalTensor Q))]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W (F.externalTensor Q))
    (Enriched.weightedCoend.rightMap W (F.externalTensor Q))]

/-- The original outer full relation contracts on the slice with its fixed first identity. -/
@[reassoc]
theorem leftSlice_condition (e : E) (a b : C) {X : V} (q : X ⟶ Q.obj a) :
    W.obj (op (e, b)) ◁ (frontHomIso (a ⟶[V] b) (F.obj e) X).hom ≫
        (α_ (W.obj (op (e, b))) (a ⟶[V] b) (F.obj e ⊗ X)).inv ≫
        ((W.obj (op (e, b)) ◁
            (EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a b ≫
          MonoidalClosed.uncurry (W.map (op (e, b)) (op (e, a)))) ⊗ₘ
          (𝟙 (F.obj e) ⊗ₘ q)) ≫ Enriched.weightedCoend.ι W (F.externalTensor Q) (e, a) =
      W.obj (op (e, b)) ◁ (F.obj e ◁
          ((a ⟶[V] b) ◁ q ≫ (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
            MonoidalClosed.uncurry (Q.map a b))) ≫
        Enriched.weightedCoend.ι W (F.externalTensor Q) (e, b) := by
  let R : V := a ⟶[V] b
  let S : V := (e, a) ⟶[V] (e, b)
  let B := F.obj e
  let A := B ⊗ Q.obj a
  let A' := B ⊗ Q.obj b
  let U := W.obj (op (e, b))
  let U' := W.obj (op (e, a))
  let Y := Enriched.weightedCoend W (F.externalTensor Q)
  let j : R ⟶ S := (EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a b
  let v : B ⊗ X ⟶ A := 𝟙 B ⊗ₘ q
  let w : U ⊗ S ⟶ U' := MonoidalClosed.uncurry (W.map (op (e, b)) (op (e, a)))
  let act : S ⊗ A ⟶ A' := (β_ S A).hom ≫
    MonoidalClosed.uncurry ((F.externalTensor Q).map (e, a) (e, b))
  let aq : R ⊗ X ⟶ Q.obj b := R ◁ q ≫ (β_ R (Q.obj a)).hom ≫
    MonoidalClosed.uncurry (Q.map a b)
  let l : U ⊗ (S ⊗ A) ⟶ U' ⊗ A := (α_ U S A).inv ≫ (w ⊗ₘ 𝟙 A)
  let r : U ⊗ (S ⊗ A) ⟶ U ⊗ A' := U ◁ act
  let ga : U' ⊗ A ⟶ Y := Enriched.weightedCoend.ι W (F.externalTensor Q) (e, a)
  let gb : U ⊗ A' ⟶ Y := Enriched.weightedCoend.ι W (F.externalTensor Q) (e, b)
  let pre : U ⊗ (R ⊗ (B ⊗ X)) ⟶ U ⊗ (S ⊗ A) := U ◁ (j ⊗ₘ v)
  let k : U ⊗ R ⟶ U' := U ◁ j ≫ w
  have hb : l ≫ ga = r ≫ gb := Enriched.weightedCoend.condition W (F.externalTensor Q) (e, a) (e, b)
  have h0 : pre ≫ l = (α_ U R (B ⊗ X)).inv ≫ (k ⊗ₘ v) := by
    have hα := associator_inv_naturality (𝟙 U) j v
    have hα' := congrArg (fun z => z ≫ (w ⊗ₘ 𝟙 A)) hα
    simpa only [pre, l, k, id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, Category.assoc] using hα'
  have hs : (j ⊗ₘ v) ≫ act = (frontHomIso R B X).inv ≫ B ◁ aq :=
    leftSlice_action F Q e a b q
  have h1 : pre ≫ r = U ◁ ((frontHomIso R B X).inv ≫ B ◁ aq) := by
    change U ◁ (j ⊗ₘ v) ≫ U ◁ act = _
    rw [← whiskerLeft_comp, hs]
  have h0' := congrArg (fun z => z ≫ ga) h0
  have h1' := congrArg (fun z => z ≫ gb) h1
  have hb' := congrArg (fun z => pre ≫ z) hb
  simp only [Category.assoc] at h0' h1' hb'
  have hc := h0'.symm.trans (hb'.trans h1')
  have hc' := congrArg (fun z => U ◁ (frontHomIso R B X).hom ≫ z) hc
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv_assoc] at hc'
  change U ◁ (frontHomIso R B X).hom ≫ (α_ U R (B ⊗ X)).inv ≫
      (k ⊗ₘ v) ≫ ga = U ◁ (B ◁ aq) ≫ gb
  exact hc'
end Coend
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
/-- Compose the actual fixed-second inclusion with a full product-enriched Hom. -/
@[reassoc]
theorem rightInclusion_full_comp (x y z : C) (e f : E) :
    ((EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map x y ⊗ₘ
      𝟙 (((y, e) : C × E) ⟶[V] (z, f))) ≫
      eComp V ((x, e) : C × E) (y, e) (z, f) =
    (α_ (x ⟶[V] y) (y ⟶[V] z) (e ⟶[V] f)).inv ≫
      (eComp V x y z ⊗ₘ 𝟙 (e ⟶[V] f)) := by
  let R : V := x ⟶[V] y
  let L : V := y ⟶[V] z
  let M : V := e ⟶[V] f
  let S : V := e ⟶[V] e
  let X : V := x ⟶[V] z
  let q : 𝟙_ V ⟶ S := eId V e
  let a : R ⊗ L ⟶ X := eComp V x y z
  let b : S ⊗ M ⟶ M := eComp V e e f
  have hb : (λ_ M).inv ≫ (q ⊗ₘ 𝟙 M) ≫ b = 𝟙 M := by
    simpa only [tensorHom_id] using e_id_comp V e f
  have h := unitActionTensor R L M S X q a b hb
  change (((ρ_ R).inv ≫ (𝟙 R ⊗ₘ q)) ⊗ₘ 𝟙 (L ⊗ M)) ≫
      tensorμ R S L M ≫ (a ⊗ₘ b) =
    (α_ R L M).inv ≫ (a ⊗ₘ 𝟙 M)
  exact h

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
/-- Compose the actual fixed-first inclusion with a full product-enriched Hom. -/
@[reassoc]
theorem leftInclusion_full_comp (x y : C) (e f g : E) :
    ((EnrichedFunctor.prodRightInclusion (V := V) (B := E) x).map e f ⊗ₘ
      𝟙 (((x, f) : C × E) ⟶[V] (y, g))) ≫
      eComp V ((x, e) : C × E) (x, f) (y, g) =
    (frontHomIso (e ⟶[V] f) (x ⟶[V] y) (f ⟶[V] g)).inv ≫
      (x ⟶[V] y) ◁ eComp V e f g := by
  let R : V := e ⟶[V] f
  let B : V := x ⟶[V] y
  let A : V := f ⟶[V] g
  let S : V := x ⟶[V] x
  let Y : V := e ⟶[V] g
  let q : 𝟙_ V ⟶ S := eId V x
  let b : S ⊗ B ⟶ B := eComp V x x y
  let a : R ⊗ A ⟶ Y := eComp V e f g
  have hb : (λ_ B).inv ≫ (q ⊗ₘ 𝟙 B) ≫ b = 𝟙 B := by
    simpa only [tensorHom_id] using e_id_comp V x y
  have h := unitActionTensorLeft R B A S Y q b a hb
  change (((λ_ R).inv ≫ (q ⊗ₘ 𝟙 R)) ⊗ₘ 𝟙 (B ⊗ A)) ≫
      tensorμ S R B A ≫ (b ⊗ₘ a) =
    (frontHomIso R B A).inv ≫ B ◁ a
  exact h

end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontHomIso_naturality (R B : V) {A A' : V} (f : A ⟶ A') :
    B ◁ R ◁ f ≫ (frontHomIso R B A').hom =
      (frontHomIso R B A).hom ≫ R ◁ B ◁ f := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontHomIso_inv_naturality (R B : V) {A A' : V} (f : A ⟶ A') :
    R ◁ B ◁ f ≫ (frontHomIso R B A').inv =
      (frontHomIso R B A).inv ≫ B ◁ R ◁ f := by
  apply (cancel_mono (frontHomIso R B A').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [frontHomIso_naturality]
  simp only [Iso.inv_hom_id_assoc]

variable {E : Type uE} [EnrichedCategory V E]

omit [MonoidalClosed V] in
/-- Contract the original right identity after moving the full Hom past a coefficient. -/
@[reassoc]
theorem leftIdentity_comp (e f : E) (R : V) :
    (e ⟶[V] f) ◁ ((ρ_ R).inv ≫ (𝟙 R ⊗ₘ eId V f)) ≫
      (frontHomIso (e ⟶[V] f) R (f ⟶[V] f)).inv ≫ R ◁ eComp V e f f =
    (β_ (e ⟶[V] f) R).hom := by
  let M : V := e ⟶[V] f
  let S : V := f ⟶[V] f
  let q : 𝟙_ V ⟶ S := eId V f
  let c : M ⊗ S ⟶ M := eComp V e f f
  have hc : M ◁ q ≫ c = (ρ_ M).hom := by
    apply (cancel_epi (ρ_ M).inv).1
    simpa only [Category.assoc, Iso.inv_hom_id] using e_comp_id V e f
  change M ◁ ((ρ_ R).inv ≫ (𝟙 R ⊗ₘ q)) ≫ (frontHomIso M R S).inv ≫ R ◁ c =
    (β_ M R).hom
  rw [id_tensorHom, whiskerLeft_comp, Category.assoc, frontHomIso_inv_naturality_assoc,
    ← whiskerLeft_comp, hc]
  simp only [frontHomIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
    Category.assoc, tensorHom_id]
  have h1 : M ◁ (ρ_ R).inv ≫ (α_ M R (𝟙_ V)).inv = (ρ_ (M ⊗ R)).inv := by monoidal
  have h2 : (α_ R M (𝟙_ V)).hom ≫ R ◁ (ρ_ M).hom = (ρ_ (R ⊗ M)).hom := by monoidal
  rw [h2]
  have h1' : M ◁ (ρ_ R).inv ≫ (α_ M R (𝟙_ V)).inv ≫
      (β_ R M).inv ▷ (𝟙_ V) ≫ (ρ_ (R ⊗ M)).hom =
    (ρ_ (M ⊗ R)).inv ≫ (β_ R M).inv ▷ (𝟙_ V) ≫ (ρ_ (R ⊗ M)).hom := by
    simpa only [Category.assoc] using
      congrArg (fun z => z ≫ (β_ R M).inv ▷ (𝟙_ V) ≫ (ρ_ (R ⊗ M)).hom) h1
  rw [h1', ← rightUnitor_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding R M).symm

end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

omit [SymmetricCategory V] [MonoidalClosed V] in
/-- Contract the original right enriched identity with a complete coefficient parameter. -/
@[reassoc]
theorem rightIdentity_comp (x y : C) (M : V) :
    (x ⟶[V] y) ◁ ((λ_ M).inv ≫ (eId V y ⊗ₘ 𝟙 M)) ≫
      (α_ (x ⟶[V] y) (y ⟶[V] y) M).inv ≫
      (eComp V x y y ⊗ₘ 𝟙 M) = 𝟙 ((x ⟶[V] y) ⊗ M) := by
  let R : V := x ⟶[V] y
  let S : V := y ⟶[V] y
  let q : 𝟙_ V ⟶ S := eId V y
  let c : R ⊗ S ⟶ R := eComp V x y y
  change R ◁ ((λ_ M).inv ≫ (q ⊗ₘ 𝟙 M)) ≫ (α_ R S M).inv ≫ (c ⊗ₘ 𝟙 M) = 𝟙 (R ⊗ M)
  rw [tensorHom_id, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc]
  have hu : R ◁ (λ_ M).inv ≫ (α_ R (𝟙_ V) M).inv = (ρ_ R).inv ▷ M := by monoidal
  simp only [tensorHom_id]
  have hu' : R ◁ (λ_ M).inv ≫ (α_ R (𝟙_ V) M).inv ≫ (R ◁ q) ▷ M ≫ c ▷ M =
      (ρ_ R).inv ▷ M ≫ (R ◁ q) ▷ M ≫ c ▷ M := by
    simpa only [Category.assoc] using
      congrArg (fun z => z ≫ (R ◁ q) ▷ M ≫ c ▷ M) hu
  rw [hu']
  have h := congrArg (fun z => z ▷ M) (e_comp_id V x y)
  simpa only [comp_whiskerRight, Category.assoc, id_whiskerRight] using h

omit [MonoidalClosed V] in
/-- The two actual one-variable inclusion paths compose without altering either Hom parameter. -/
@[reassoc]
theorem rightThenLeft_comp (x y : C) (e f : E) :
    ((EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map x y ⊗ₘ
      (EnrichedFunctor.prodRightInclusion (V := V) (B := E) y).map e f) ≫
      eComp V ((x, e) : C × E) (y, e) (y, f) =
    𝟙 ((x ⟶[V] y) ⊗ (e ⟶[V] f)) := by
  let R : V := x ⟶[V] y
  let L : V := y ⟶[V] y
  let M : V := e ⟶[V] f
  let j : R ⟶ R ⊗ (e ⟶[V] e) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map x y
  let k : M ⟶ L ⊗ M :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) y).map e f
  let c : (R ⊗ (e ⟶[V] e)) ⊗ (L ⊗ M) ⟶ R ⊗ M :=
    eComp V ((x, e) : C × E) (y, e) (y, f)
  have h := rightInclusion_full_comp (V := V) x y y e f
  change (j ⊗ₘ 𝟙 (L ⊗ M)) ≫ c = (α_ R L M).inv ≫ (eComp V x y y ⊗ₘ 𝟙 M) at h
  have ht : (j ⊗ₘ k) = R ◁ k ≫ (j ⊗ₘ 𝟙 (L ⊗ M)) := by
    have ht' := tensorHom_def' j k
    change (j ⊗ₘ k) = R ◁ k ≫ j ▷ (L ⊗ M) at ht'
    rw [tensorHom_id]
    exact ht'
  change (j ⊗ₘ k) ≫ c = 𝟙 (R ⊗ M)
  rw [ht, Category.assoc, h]
  exact rightIdentity_comp (V := V) x y M

omit [MonoidalClosed V] in
/-- The opposite inclusion order preserves the actual Hom braid required by product composition. -/
@[reassoc]
theorem leftThenRight_comp (x y : C) (e f : E) :
    ((EnrichedFunctor.prodRightInclusion (V := V) (B := E) x).map e f ⊗ₘ
      (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) f).map x y) ≫
      eComp V ((x, e) : C × E) (x, f) (y, f) =
    (β_ (e ⟶[V] f) (x ⟶[V] y)).hom := by
  let R : V := x ⟶[V] y
  let M : V := e ⟶[V] f
  let S : V := f ⟶[V] f
  let j : M ⟶ (x ⟶[V] x) ⊗ M :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) x).map e f
  let k : R ⟶ R ⊗ S :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) f).map x y
  let c : ((x ⟶[V] x) ⊗ M) ⊗ (R ⊗ S) ⟶ R ⊗ M :=
    eComp V ((x, e) : C × E) (x, f) (y, f)
  have h := AssociatorRightContraction.leftInclusion_full_comp (V := V) x y e f f
  change (j ⊗ₘ 𝟙 (R ⊗ S)) ≫ c =
    (AssociatorRightContraction.frontHomIso M R S).inv ≫ R ◁ eComp V e f f at h
  have ht : (j ⊗ₘ k) = M ◁ k ≫ (j ⊗ₘ 𝟙 (R ⊗ S)) := by
    have ht' := tensorHom_def' j k
    change (j ⊗ₘ k) = M ◁ k ≫ j ▷ (R ⊗ S) at ht'
    rw [tensorHom_id]
    exact ht'
  change (j ⊗ₘ k) ≫ c = (β_ M R).hom
  rw [ht, Category.assoc, h]
  exact AssociatorRightContraction.leftIdentity_comp (V := V) e f R

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- The full weight action along the actual fixed-first enriched inclusion. -/
abbrev leftSliceWeight (W : EnrichedFunctor V (C × E)ᵒᵖ V) (x : C) (e f : E) :
    W.obj (op (x, f)) ⊗ (e ⟶[V] f) ⟶ W.obj (op (x, e)) :=
  W.obj (op (x, f)) ◁ (EnrichedFunctor.prodRightInclusion (V := V) (B := E) x).map e f ≫
    MonoidalClosed.uncurry (W.map (op (x, f)) (op (x, e)))

/-- Both complete slice actions compose to the original full product Hom action. -/
@[reassoc]
theorem sliceWeight_product (W : EnrichedFunctor V (C × E)ᵒᵖ V) (x z : C) (e f : E) :
    (α_ (W.obj (op (z, f))) (x ⟶[V] z) (e ⟶[V] f)).inv ≫
      (rightSliceWeight W f x z ⊗ₘ 𝟙 (e ⟶[V] f)) ≫ leftSliceWeight W x e f =
    MonoidalClosed.uncurry (W.map (op (z, f)) (op (x, e))) := by
  let a : C × E := (x, e)
  let b : C × E := (x, f)
  let c : C × E := (z, f)
  let R : V := x ⟶[V] z
  let M : V := e ⟶[V] f
  let U := W.obj (op c)
  let Y := W.obj (op b)
  let X := W.obj (op a)
  let j : R ⟶ R ⊗ (f ⟶[V] f) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) f).map x z
  let k : M ⟶ (x ⟶[V] x) ⊗ M :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) x).map e f
  let v : U ⊗ (R ⊗ (f ⟶[V] f)) ⟶ Y :=
    MonoidalClosed.uncurry (W.map (op c) (op b))
  let w : Y ⊗ ((x ⟶[V] x) ⊗ M) ⟶ X :=
    MonoidalClosed.uncurry (W.map (op b) (op a))
  let zMap : U ⊗ (R ⊗ M) ⟶ X := MonoidalClosed.uncurry (W.map (op c) (op a))
  let q : U ⊗ R ⟶ Y := U ◁ j ≫ v
  let cp : ((x ⟶[V] x) ⊗ M) ⊗ (R ⊗ (f ⟶[V] f)) ⟶ R ⊗ M := eComp V a b c
  have hc := leftThenRight_comp (V := V) x z e f
  change (k ⊗ₘ j) ≫ cp = (β_ M R).hom at hc
  have hp : (j ⊗ₘ k) ≫ (β_ (R ⊗ (f ⟶[V] f)) ((x ⟶[V] x) ⊗ M)).hom ≫ cp =
      𝟙 (R ⊗ M) := by
    rw [BraidedCategory.braiding_naturality_assoc, hc]
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding M R, Iso.inv_hom_id]
  have hm := weightAction_comp_maps W a b c j k
  change (α_ U R M).inv ≫ (q ⊗ₘ k) ≫ w =
    U ◁ ((j ⊗ₘ k) ≫ (β_ (R ⊗ (f ⟶[V] f)) ((x ⟶[V] x) ⊗ M)).hom ≫ cp) ≫ zMap at hm
  rw [hp, whiskerLeft_id, Category.id_comp] at hm
  have hf : (q ⊗ₘ 𝟙 M) ≫ Y ◁ k = q ⊗ₘ k := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id q) (Category.id_comp k)
  have hf' : (q ⊗ₘ 𝟙 M) ≫ Y ◁ k ≫ w = (q ⊗ₘ k) ≫ w := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ w) hf
  change (α_ U R M).inv ≫ (q ⊗ₘ 𝟙 M) ≫ Y ◁ k ≫ w = zMap
  rw [hf']
  exact hm

/-- The original full outer Hom composes with the original inner weight Hom. -/
abbrev outerHomComposition (x y z : C) (e f : E) :
    ((y ⟶[V] z) ⊗ (e ⟶[V] f)) ⊗ (x ⟶[V] y) ⟶ (x ⟶[V] z) ⊗ (e ⟶[V] f) :=
  (β_ ((y ⟶[V] z) ⊗ (e ⟶[V] f)) (x ⟶[V] y)).hom ≫
    (α_ (x ⟶[V] y) (y ⟶[V] z) (e ⟶[V] f)).inv ≫
      (eComp V x y z ⊗ₘ 𝟙 (e ⟶[V] f))

/-- The original outer weight face followed by contraction retains the entire outer Hom. -/
@[reassoc]
theorem outerWeight_comp (W : EnrichedFunctor V (C × E)ᵒᵖ V) (x y z : C) (e f : E) :
    (α_ (W.obj (op (z, f))) (((y, e) : C × E) ⟶[V] (z, f)) (x ⟶[V] y)).inv ≫
      (MonoidalClosed.uncurry (W.map (op (z, f)) (op (y, e))) ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
      rightSliceWeight W e x y =
    W.obj (op (z, f)) ◁ outerHomComposition (V := V) x y z e f ≫
      MonoidalClosed.uncurry (W.map (op (z, f)) (op (x, e))) := by
  let a : C × E := (x, e)
  let b : C × E := (y, e)
  let c : C × E := (z, f)
  let R : V := x ⟶[V] y
  let L : V := y ⟶[V] z
  let M : V := e ⟶[V] f
  let S := L ⊗ M
  let U := W.obj (op c)
  let Y := W.obj (op b)
  let X := W.obj (op a)
  let j : R ⟶ R ⊗ (e ⟶[V] e) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e).map x y
  let v : U ⊗ S ⟶ Y := MonoidalClosed.uncurry (W.map (op c) (op b))
  let w : Y ⊗ (R ⊗ (e ⟶[V] e)) ⟶ X := MonoidalClosed.uncurry (W.map (op b) (op a))
  let q : U ⊗ ((x ⟶[V] z) ⊗ M) ⟶ X := MonoidalClosed.uncurry (W.map (op c) (op a))
  let cp : (R ⊗ (e ⟶[V] e)) ⊗ S ⟶ (x ⟶[V] z) ⊗ M := eComp V a b c
  have hc := rightInclusion_full_comp (V := V) x y z e f
  change (j ⊗ₘ 𝟙 S) ≫ cp = (α_ R L M).inv ≫ (eComp V x y z ⊗ₘ 𝟙 M) at hc
  have hp : (𝟙 S ⊗ₘ j) ≫ (β_ S (R ⊗ (e ⟶[V] e))).hom ≫ cp =
      outerHomComposition (V := V) x y z e f := by
    rw [BraidedCategory.braiding_naturality_assoc]
    rw [hc]
  have hm := weightAction_comp_maps W a b c (𝟙 S) j
  change (α_ U S R).inv ≫ ((U ◁ 𝟙 S ≫ v) ⊗ₘ j) ≫ w =
    U ◁ ((𝟙 S ⊗ₘ j) ≫ (β_ S (R ⊗ (e ⟶[V] e))).hom ≫ cp) ≫ q at hm
  rw [whiskerLeft_id, Category.id_comp, hp] at hm
  have hf : (v ⊗ₘ 𝟙 R) ≫ Y ◁ j = v ⊗ₘ j := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id v) (Category.id_comp j)
  have hf' : (v ⊗ₘ 𝟙 R) ≫ Y ◁ j ≫ w = (v ⊗ₘ j) ≫ w := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ w) hf
  change (α_ U S R).inv ≫ (v ⊗ₘ 𝟙 R) ≫ Y ◁ j ≫ w =
    U ◁ outerHomComposition (V := V) x y z e f ≫ q
  rw [hf']
  exact hm

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorInclusion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- Map the actual fixed-first identity through the original product enriched functor. -/
theorem leftInclusion_fixed_product (T : EnrichedFunctor V C K) (a : C) (e f : E) :
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) a).map e f ≫
      (prodEnrichedFunctor T (EnrichedFunctor.id V E)).map (a, e) (a, f) =
    (EnrichedFunctor.prodRightInclusion (V := V) (B := E) (T.obj a)).map e f := by
  let M : V := e ⟶[V] f
  let R : V := a ⟶[V] a
  let S : V := T.obj a ⟶[V] T.obj a
  let i : 𝟙_ V ⟶ R := eId V a
  let j : 𝟙_ V ⟶ S := eId V (T.obj a)
  let t : R ⟶ S := T.map a a
  have hi : i ≫ t = j := T.map_id a
  have ht : (i ⊗ₘ 𝟙 M) ≫ (t ⊗ₘ 𝟙 M) = j ⊗ₘ 𝟙 M :=
    (tensorHom_comp_tensorHom i (𝟙 M) t (𝟙 M)).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) hi (Category.comp_id (𝟙 M)))
  change ((λ_ M).inv ≫ (i ⊗ₘ 𝟙 M)) ≫ (t ⊗ₘ 𝟙 M) = (λ_ M).inv ≫ (j ⊗ₘ 𝟙 M)
  exact (Category.assoc _ _ _).trans (congrArg (fun z => (λ_ M).inv ≫ z) ht)

end CategoryTheory.EnrichedDayKernel.AssociatorInclusion

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Compose a full Hom action while retaining its second Hom parameter. -/
abbrev outerAction {L R S : V} (f : L ⊗ R ⟶ S) (M : V) :
    (L ⊗ M) ⊗ R ⟶ S ⊗ M :=
  (α_ L M R).hom ≫ L ◁ (β_ M R).hom ≫ (α_ L R M).inv ≫ (f ⊗ₘ 𝟙 M)

/-- The actual coefficient permutation used after the first action is contracted. -/
abbrev outerReassociate (S M A B : V) : (S ⊗ A) ⊗ (M ⊗ B) ⟶ (S ⊗ M) ⊗ (A ⊗ B) :=
  (α_ S A (M ⊗ B)).hom ≫ S ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
    (α_ S M (A ⊗ B)).inv

/-- The coefficient permutation is natural in the full result of the first action. -/
@[reassoc]
theorem outerReassociate_naturality {S S' : V} (f : S ⟶ S') (M A B : V) :
    (f ▷ A ⊗ₘ 𝟙 (M ⊗ B)) ≫ outerReassociate S' M A B =
      outerReassociate S M A B ≫ f ▷ M ▷ (A ⊗ B) := by
  simp only [outerReassociate, Category.assoc, tensorHom_id]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

private theorem outerAction_word_pure (L R M A B : V) :
    tensorμ L M (R ⊗ A) B ≫ ((α_ L R A).inv ⊗ₘ 𝟙 (M ⊗ B)) ≫
      outerReassociate (L ⊗ R) M A B =
    (L ⊗ M) ◁ (α_ R A B).hom ≫ (α_ (L ⊗ M) R (A ⊗ B)).inv ≫
      (outerAction (𝟙 (L ⊗ R)) M ⊗ₘ 𝟙 (A ⊗ B)) := by
  simp only [tensorμ, outerAction, outerReassociate, AssociatorRightContraction.frontHomIso,
    Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    BraidedCategory.braiding_tensor_right_hom, tensorHom_def, id_whiskerRight,
    whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding M A]
  monoidal
  simp only [whiskerRightIso_refl, Iso.trans_refl, whiskerLeftIso_refl, Iso.refl_trans,
    whiskerLeftIso_trans,
    Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Iso.trans_assoc, Iso.symm_hom,
      whiskerRight_tensor,
    Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
  have hGap : L ◁ (α_ R (A ⊗ M) B).inv ≫ L ◁ ((α_ R A M).inv ▷ B) ≫
      (α_ L ((R ⊗ A) ⊗ M) B).inv ≫ (α_ L (R ⊗ A) M).inv ▷ B ≫
      (α_ L R A).inv ▷ M ▷ B ≫ (α_ ((L ⊗ R) ⊗ A) M B).hom ≫
      (α_ (L ⊗ R) A (M ⊗ B)).hom ≫ (α_ L R (A ⊗ (M ⊗ B))).hom ≫
      L ◁ R ◁ (α_ A M B).inv = 𝟙 (L ⊗ (R ⊗ ((A ⊗ M) ⊗ B))) := by monoidal
  slice_lhs 4 12 => rw [hGap]
  simp only [Category.id_comp, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp,
    ← comp_whiskerRight_assoc]
  monoidal
  simp only [whiskerRightIso_refl, Iso.trans_refl, whiskerLeftIso_refl, whiskerLeftIso_trans,
    Iso.trans_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Iso.refl_hom, Iso.refl_trans, Iso.trans_assoc,
      Iso.symm_hom,
    Category.id_comp, cancelIso, Category.assoc, whiskerRightIso_trans]
  monoidal

/-- The original tensor interchange and coefficient braid preserve the complete action word. -/
@[reassoc]
theorem outerAction_word {L R S : V} (f : L ⊗ R ⟶ S) (M A B : V) :
    tensorμ L M (R ⊗ A) B ≫
      (((α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (M ⊗ B)) ≫
      (α_ S A (M ⊗ B)).hom ≫ S ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
      (α_ S M (A ⊗ B)).inv =
    (L ⊗ M) ◁ (α_ R A B).hom ≫ (α_ (L ⊗ M) R (A ⊗ B)).inv ≫
      (outerAction f M ⊗ₘ 𝟙 (A ⊗ B)) := by
  have hf : (((α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (M ⊗ B)) =
      ((α_ L R A).inv ⊗ₘ 𝟙 (M ⊗ B)) ≫ (f ▷ A ⊗ₘ 𝟙 (M ⊗ B)) := by
    simp only [tensorHom_id, comp_whiskerRight]
  have hg : outerAction f M = outerAction (𝟙 (L ⊗ R)) M ≫ f ▷ M := by
    simp only [outerAction, tensorHom_id, id_whiskerRight, Category.comp_id, Category.assoc]
  change tensorμ L M (R ⊗ A) B ≫
      (((α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (M ⊗ B)) ≫ outerReassociate S M A B = _
  rw [hf, Category.assoc, outerReassociate_naturality, hg]
  have hp := congrArg (fun z => z ≫ f ▷ M ▷ (A ⊗ B)) (outerAction_word_pure L R M A B)
  simpa only [tensorHom_id, comp_whiskerRight, Category.assoc] using hp

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {E : Type uE} [EnrichedCategory V E]

/-- The tensor action word is the original full product precomposition. -/
theorem outerAction_comp (x y z : C) (e f : E) :
    outerAction ((β_ (y ⟶[V] z) (x ⟶[V] y)).hom ≫ eComp V x y z) (e ⟶[V] f) =
      outerHomComposition (V := V) x y z e f := by
  simp only [outerAction, outerHomComposition, BraidedCategory.braiding_tensor_left_hom,
    tensorHom_id, comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The full flat weight action along the actual fixed-first triple inclusion. -/
abbrev flatOuterSlice (a : I × I) (e f : I) :
    (AssociatorIndex.leftWeight d m).obj (op (a, f)) ⊗ (e ⟶[V] f) ⟶
      (AssociatorIndex.leftWeight d m).obj (op (a, e)) :=
  (AssociatorIndex.leftWeight d m).obj (op (a, f)) ◁
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) a).map e f ≫
      MonoidalClosed.uncurry ((AssociatorIndex.leftWeight d m).map (op (a, f)) (op (a, e)))

/-- The full flat outer action is the actual outer slice after preservation of the inner identity.
-/
theorem flatOuterSlice_original (a : I × I) (e f : I) :
    flatOuterSlice d m a e f =
      AssociatorContraction.leftSliceWeight (weight d.tensorEnrichedFunctor m)
        (d.tensorEnrichedFunctor.obj a) e f := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let Q := AssociatorIndex.leftWeight d m
  let P := AssociatorTensor.leftProduct d
  let U := Q.obj (op (a, f))
  let M : V := e ⟶[V] f
  let R : V := a ⟶[V] a
  let S : V := T.obj a ⟶[V] T.obj a
  let j : M ⟶ R ⊗ M := (EnrichedFunctor.prodRightInclusion (V := V) (B := I) a).map e f
  let k : M ⟶ S ⊗ M :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) (T.obj a)).map e f
  let t : R ⊗ M ⟶ S ⊗ M := P.map (a, e) (a, f)
  let v : U ⊗ (R ⊗ M) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (Q.map (op (a, f)) (op (a, e)))
  let w : U ⊗ (S ⊗ M) ⟶ Q.obj (op (a, e)) :=
    MonoidalClosed.uncurry (W.map (op (T.obj a, f)) (op (T.obj a, e)))
  have hv : v = U ◁ t ≫ w := by
    have h := AssociatorTensor.leftWeightMap_naturality d m (a, e) (a, f)
    change v ≫ 𝟙 (Q.obj (op (a, e))) = (𝟙 U ⊗ₘ t) ≫ w at h
    simpa only [Category.comp_id, id_tensorHom] using h
  have hj : j ≫ t = k := AssociatorInclusion.leftInclusion_fixed_product T a e f
  change U ◁ j ≫ v = U ◁ k ≫ w
  rw [hv]
  exact (whiskerLeft_comp_assoc U j t w).symm.trans (congrArg (fun z => U ◁ z ≫ w) hj)

/-- Both full original outer weight legs contract to the actual flat outer Hom action. -/
@[reassoc]
theorem sliceBase_outer (a p q : I × I) :
    (weight d.tensorEnrichedFunctor m).obj (op q) ◁
      AssociatorContraction.outerHomComposition (V := V) (d.tensorEnrichedFunctor.obj a)
        p.1 q.1 p.2 q.2 ≫
      (α_ ((weight d.tensorEnrichedFunctor m).obj (op q))
        (d.tensorEnrichedFunctor.obj a ⟶[V] q.1) (p.2 ⟶[V] q.2)).inv ≫
      (sliceBase d m q a ⊗ₘ 𝟙 (p.2 ⟶[V] q.2)) ≫ flatOuterSlice d m a p.2 q.2 =
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op q)) (p ⟶[V] q)
        (d.tensorEnrichedFunctor.obj a ⟶[V] p.1)).inv ≫
      (MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map (op q) (op p)) ⊗ₘ
        𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] p.1)) ≫ sliceBase d m p a := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let x := T.obj a
  let U := W.obj (op q)
  let δ := AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2
  have h0 := AssociatorContraction.outerWeight_comp W x p.1 q.1 p.2 q.2
  have h1 := AssociatorContraction.sliceWeight_product W x q.1 p.2 q.2
  have h2 := congrArg (fun z => U ◁ δ ≫ z) h1
  rw [flatOuterSlice_original]
  change U ◁ δ ≫
      (α_ (W.obj (op (q.1, q.2))) (x ⟶[V] q.1) (p.2 ⟶[V] q.2)).inv ≫
      (AssociatorContraction.rightSliceWeight W q.2 x q.1 ⊗ₘ 𝟙 (p.2 ⟶[V] q.2)) ≫
      AssociatorContraction.leftSliceWeight W x p.2 q.2 =
    (α_ (W.obj (op (q.1, q.2))) (((p.1, p.2) : I × I) ⟶[V] (q.1, q.2))
      (x ⟶[V] p.1)).inv ≫
      (MonoidalClosed.uncurry (W.map (op (q.1, q.2)) (op (p.1, p.2))) ⊗ₘ 𝟙 (x ⟶[V] p.1)) ≫
      AssociatorContraction.rightSliceWeight W p.2 x p.1
  simpa only [Category.assoc] using h2.trans h0.symm

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Lift the proved full outer weight relation through the unchanged nested coefficient word. -/
@[reassoc]
theorem contract_outer_weight {U K X Y L R S : V} (f : L ⊗ R ⟶ S)
    (M A B : V) (v : U ⊗ (L ⊗ M) ⟶ K) (k : K ⊗ R ⟶ X)
    (l : U ⊗ S ⟶ Y) (q : Y ⊗ M ⟶ X)
    (h : U ◁ outerAction f M ≫ (α_ U S M).inv ≫ (l ⊗ₘ 𝟙 M) ≫ q =
      (α_ U (L ⊗ M) R).inv ≫ (v ⊗ₘ 𝟙 R) ≫ k) :
    (α_ U (L ⊗ M) ((R ⊗ A) ⊗ B)).inv ≫
      (v ⊗ₘ 𝟙 ((R ⊗ A) ⊗ B)) ≫ contract k A B =
    U ◁ (tensorμ L M (R ⊗ A) B ≫
      (((α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (M ⊗ B))) ≫
      contract l A (M ⊗ B) ≫ Y ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
      (α_ Y M (A ⊗ B)).inv ≫ (q ⊗ₘ 𝟙 (A ⊗ B)) := by
  let P := L ⊗ M
  let C := A ⊗ B
  let D := (R ⊗ A) ⊗ B
  let Z := A ⊗ (M ⊗ B)
  let n : Z ⟶ M ⊗ C := (AssociatorRightContraction.frontHomIso M A B).hom
  let g : D ⟶ R ⊗ C := (α_ R A B).hom
  let δ : P ⊗ R ⟶ S ⊗ M := outerAction f M
  let z : P ⊗ D ⟶ (S ⊗ A) ⊗ (M ⊗ B) :=
    tensorμ L M (R ⊗ A) B ≫ ((α_ L R A).inv ≫ f ▷ A) ▷ (M ⊗ B)
  have hw : z ≫ (α_ S A (M ⊗ B)).hom ≫ S ◁ n ≫ (α_ S M C).inv =
      P ◁ g ≫ (α_ P R C).inv ≫ δ ▷ C := by
    simpa only [z, n, g, δ, tensorHom_id, Category.assoc] using outerAction_word f M A B
  have h0 : U ◁ δ ≫ (α_ U S M).inv ≫ l ▷ M ≫ q =
      (α_ U P R).inv ≫ v ▷ R ≫ k := by
    simpa only [tensorHom_id] using h
  symm
  simp only [contract, tensorHom_id, Category.assoc]
  change U ◁ z ≫ U ◁ (α_ S A (M ⊗ B)).hom ≫ (α_ U S Z).inv ≫
      l ▷ Z ≫ Y ◁ n ≫ (α_ Y M C).inv ≫ q ▷ C =
    (α_ U P D).inv ≫ v ▷ D ≫ K ◁ g ≫ (α_ K R C).inv ≫ k ▷ C
  rw [← whisker_exchange_assoc l n, ← associator_inv_naturality_right_assoc U S n,
    associator_inv_naturality_left_assoc l M C, ← pentagon_inv_assoc]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [hw]
  rw [whiskerLeft_comp_assoc, whiskerLeft_comp_assoc,
    associator_inv_naturality_middle_assoc U δ C]
  rw [← whisker_exchange_assoc v g, ← associator_inv_naturality_right_assoc U P g,
    associator_inv_naturality_left_assoc v R C, ← pentagon_inv_assoc]
  have hh := congrArg (fun z => U ◁ P ◁ g ≫ U ◁ (α_ P R C).inv ≫
    (α_ U (P ⊗ R) C).inv ≫ z ▷ C) h0
  simpa only [comp_whiskerRight, Category.assoc] using hh

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]

/-- Contraction identifies both complete original outer relation faces after the flat projection. -/
@[reassoc]
theorem contractWord_outer (p q a : I × I) :
    AssociatorFaces.Left.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q a ≫
      contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (a, p.2) =
    AssociatorFaces.Left.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q a ≫
      contractWord d F G H m q a ≫ AssociatorFlat.leftGenerator d F G H m (a, q.2) := by
  let T := d.tensorEnrichedFunctor
  let W := weight T m
  let Q := AssociatorIndex.leftWeight d m
  let x := T.obj a
  let U := W.obj (op q)
  let K := W.obj (op p)
  let X := W.obj (op (x, p.2))
  let Y := W.obj (op (x, q.2))
  let L : V := p.1 ⟶[V] q.1
  let M : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.1
  let S : V := x ⟶[V] q.1
  let A := F.obj a.1 ⊗ G.obj a.2
  let B := H.obj p.2
  let B' := H.obj q.2
  let f : L ⊗ R ⟶ S := (β_ L R).hom ≫ eComp V x p.1 q.1
  let out : L ⊗ (R ⊗ A) ⟶ S ⊗ A := Output.outputAction x p.1 q.1 A
  let b : M ⊗ B ⟶ B' := (β_ M B).hom ≫ MonoidalClosed.uncurry (H.map p.2 q.2)
  let v : U ⊗ (L ⊗ M) ⟶ K := MonoidalClosed.uncurry (W.map (op q) (op p))
  let k : K ⊗ R ⟶ X := sliceBase d m p a
  let l : U ⊗ S ⟶ Y := sliceBase d m q a
  let t : Y ⊗ M ⟶ X := flatOuterSlice d m a p.2 q.2
  let Z := AssociatorFlat.leftPoint d F G H m
  let ga : X ⊗ (A ⊗ B) ⟶ Z := AssociatorFlat.leftGenerator d F G H m (a, p.2)
  let gb : Y ⊗ (A ⊗ B') ⟶ Z := AssociatorFlat.leftGenerator d F G H m (a, q.2)
  let pre : U ⊗ ((L ⊗ M) ⊗ ((R ⊗ A) ⊗ B)) ⟶ Y ⊗ (A ⊗ (M ⊗ B)) :=
    U ◁ (tensorμ L M (R ⊗ A) B ≫ (out ⊗ₘ 𝟙 (M ⊗ B))) ≫
      AssociatorContraction.contract l A (M ⊗ B)
  have hout : out = (α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A) := by
    change (α_ L R A).inv ≫ ((β_ L R).hom ⊗ₘ 𝟙 A) ≫
        (eComp V x p.1 q.1 ⊗ₘ 𝟙 A) = (α_ L R A).inv ≫ (f ⊗ₘ 𝟙 A)
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hd : AssociatorContraction.outerAction f M =
      AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2 :=
    AssociatorContraction.outerAction_comp (V := V) x p.1 q.1 p.2 q.2
  have hw := sliceBase_outer d m a p q
  change U ◁ AssociatorContraction.outerHomComposition (V := V) x p.1 q.1 p.2 q.2 ≫
      (α_ U S M).inv ≫ (l ⊗ₘ 𝟙 M) ≫ t =
    (α_ U (L ⊗ M) R).inv ≫ (v ⊗ₘ 𝟙 R) ≫ k at hw
  rw [← hd] at hw
  have h0 := AssociatorContraction.contract_outer_weight f M A B v k l t hw
  have h0' : (α_ U (L ⊗ M) ((R ⊗ A) ⊗ B)).inv ≫
      (v ⊗ₘ 𝟙 ((R ⊗ A) ⊗ B)) ≫ AssociatorContraction.contract k A B ≫ ga =
    pre ≫ Y ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
      (α_ Y M (A ⊗ B)).inv ≫ (t ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga := by
    simpa only [pre, hout, AssociatorContraction.contract, Category.assoc] using
      congrArg (fun z => z ≫ ga) h0
  have hb := AssociatorRightContraction.leftSlice_condition Q (F.externalTensor G) H a p.2 q.2 (𝟙 B)
  change Y ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
      (α_ Y M (A ⊗ B)).inv ≫ (t ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) ≫ ga =
    Y ◁ (A ◁ (M ◁ 𝟙 B ≫ b)) ≫ gb at hb
  rw [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hb
  have hb' : pre ≫ Y ◁ (AssociatorRightContraction.frontHomIso M A B).hom ≫
      (α_ Y M (A ⊗ B)).inv ≫ (t ⊗ₘ 𝟙 (A ⊗ B)) ≫ ga =
    pre ≫ Y ◁ A ◁ b ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => pre ≫ z) hb
  have hf : (out ⊗ₘ 𝟙 (M ⊗ B)) ≫ (𝟙 (S ⊗ A) ⊗ₘ b) = out ⊗ₘ b := by
    rw [tensorHom_comp_tensorHom]
    exact congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id out) (Category.id_comp b)
  have hn : U ◁ (𝟙 (S ⊗ A) ⊗ₘ b) ≫ AssociatorContraction.contract l A B' =
      AssociatorContraction.contract l A (M ⊗ B) ≫ Y ◁ A ◁ b := by
    simpa only [whiskerLeft_id, id_tensorHom] using
      AssociatorContraction.contract_naturality l (𝟙 A) b
  have hng : U ◁ (𝟙 (S ⊗ A) ⊗ₘ b) ≫ AssociatorContraction.contract l A B' ≫ gb =
      AssociatorContraction.contract l A (M ⊗ B) ≫ Y ◁ A ◁ b ≫ gb := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ gb) hn
  have h1' : U ◁ (tensorμ L M (R ⊗ A) B ≫ (out ⊗ₘ b)) ≫
      AssociatorContraction.contract l A B' ≫ gb = pre ≫ Y ◁ A ◁ b ≫ gb := by
    rw [whiskerLeft_comp, Category.assoc, ← hf, whiskerLeft_comp, Category.assoc, hng]
    simp only [pre, whiskerLeft_comp, Category.assoc]
  change ((α_ U (L ⊗ M) ((R ⊗ A) ⊗ B)).inv ≫ (v ⊗ₘ 𝟙 ((R ⊗ A) ⊗ B))) ≫
      AssociatorContraction.contract k A B ≫ ga =
    U ◁ (tensorμ L M (R ⊗ A) B ≫ (out ⊗ₘ b)) ≫
      AssociatorContraction.contract l A B' ≫ gb
  simpa only [Category.assoc] using h0'.trans (hb'.trans h1'.symm)

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

/-- The original full enriched identity acts as the actual coefficient identity. -/
@[reassoc]
theorem action_identity (Q : EnrichedFunctor V C V) (a : C) :
    (ρ_ (Q.obj a)).inv ≫ (𝟙 (Q.obj a) ⊗ₘ eId V a) ≫
      MonoidalClosed.uncurry (Q.map a a) = 𝟙 (Q.obj a) := by
  have h := congrArg MonoidalClosed.uncurry (Q.map_id a)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  simp only [id_tensorHom]
  rw [h, Iso.inv_hom_id]

end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- Reassociate contraction naturally on the entire original weight Hom. -/
@[reassoc]
theorem contract_naturality_hom {U R R' Y : V} (t : R ⟶ R') (k : U ⊗ R' ⟶ Y) (A B : V) :
    U ◁ (t ▷ A ▷ B) ≫ contract k A B = contract (U ◁ t ≫ k) A B := by
  have hn : (t ▷ A ▷ B) ≫ (α_ R' A B).hom = (α_ R A B).hom ≫ t ▷ (A ⊗ B) :=
    associator_naturality_left t A B
  simp only [contract, tensorHom_id, comp_whiskerRight]
  rw [← whiskerLeft_comp_assoc, hn, whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]

private theorem contract_unit_pure (U A B : V) :
    U ◁ ((λ_ A).inv ▷ B) ≫ contract (ρ_ U).hom A B = 𝟙 (U ⊗ (A ⊗ B)) := by
  simp only [contract, tensorHom_id]
  monoidal

/-- Original identity insertion contracts the complete left tensor word. -/
@[reassoc]
theorem contract_identity {U R : V} (i : 𝟙_ V ⟶ R) (k : U ⊗ R ⟶ U)
    (hk : (ρ_ U).inv ≫ (𝟙 U ⊗ₘ i) ≫ k = 𝟙 U) (A B : V) :
    U ◁ (((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A)) ▷ B) ≫ contract k A B = 𝟙 (U ⊗ (A ⊗ B)) := by
  have hi : U ◁ i ≫ k = (ρ_ U).hom := by
    apply (cancel_epi (ρ_ U).inv).1
    simpa only [id_tensorHom, Category.assoc, Iso.inv_hom_id] using hk
  simp only [tensorHom_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [contract_naturality_hom, hi]
  exact contract_unit_pure U A B

end CategoryTheory.EnrichedDayKernel.AssociatorContraction

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The original full inner identity becomes the actual outer product identity. -/
@[reassoc]
theorem sliceBase_identity (a : I × I) (e : I) :
    (ρ_ ((weight d.tensorEnrichedFunctor m).obj (op (d.tensorEnrichedFunctor.obj a, e)))).inv ≫
      (𝟙 ((weight d.tensorEnrichedFunctor m).obj (op (d.tensorEnrichedFunctor.obj a, e))) ⊗ₘ
        eId V (d.tensorEnrichedFunctor.obj a)) ≫
      sliceBase d m (d.tensorEnrichedFunctor.obj a, e) a =
    𝟙 ((weight d.tensorEnrichedFunctor m).obj (op (d.tensorEnrichedFunctor.obj a, e))) := by
  let x := d.tensorEnrichedFunctor.obj a
  let p : I × I := (x, e)
  let W := weight d.tensorEnrichedFunctor m
  let U := W.obj (op p)
  let j : (x ⟶[V] x) ⟶ (p ⟶[V] p) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) e).map x x
  let w : U ⊗ (p ⟶[V] p) ⟶ U := MonoidalClosed.uncurry (W.map (op p) (op p))
  have hj : eId V x ≫ j = eId V p :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) e).map_id x
  have hi := AssociatorRightContraction.action_identity W (op p)
  change (ρ_ U).inv ≫ (𝟙 U ⊗ₘ eId V p) ≫ w = 𝟙 U at hi
  change (ρ_ U).inv ≫ (𝟙 U ⊗ₘ eId V x) ≫ (U ◁ j ≫ w) = 𝟙 U
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [hj]
  exact hi

/-- Insert the actual inner identity into the unchanged original left nested generator word. -/
abbrev identityWord (X : (I × I) × I) :
    AssociatorFlat.leftObjects d F G H m X ⟶
      AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        (d.tensorEnrichedFunctor.obj X.1, X.2) X.1 :=
  (weight d.tensorEnrichedFunctor m).obj (op (d.tensorEnrichedFunctor.obj X.1, X.2)) ◁
    (AssociatorUnit.identityInsert (d.tensorEnrichedFunctor.obj X.1) (F.obj X.1.1 ⊗ G.obj X.1.2) ▷
      H.obj X.2)

/-- Identity insertion followed by original contraction is the full original flat summand identity.
-/
@[reassoc]
theorem identityWord_contractWord (X : (I × I) × I) :
    identityWord d F G H m X ≫
      contractWord d F G H m (d.tensorEnrichedFunctor.obj X.1, X.2) X.1 =
    𝟙 (AssociatorFlat.leftObjects d F G H m X) := by
  let x := d.tensorEnrichedFunctor.obj X.1
  let p : I × I := (x, X.2)
  let U := (weight d.tensorEnrichedFunctor m).obj (op p)
  let A := F.obj X.1.1 ⊗ G.obj X.1.2
  let B := H.obj X.2
  let k : U ⊗ (x ⟶[V] x) ⟶ U := sliceBase d m p X.1
  change U ◁ (AssociatorUnit.identityInsert x A ▷ B) ≫
    AssociatorContraction.contract k A B = 𝟙 (U ⊗ (A ⊗ B))
  exact AssociatorContraction.contract_identity (eId V x) k (sliceBase_identity d m X.1 X.2) A B

variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)]

/-- The actual flat-to-nested generator is the original nested generator after identity insertion.
-/
@[reassoc]
theorem leftGenerator_flatToNested_identity (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ flatToNested d F G H m =
      identityWord d F G H m X ≫
        AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
          (d.tensorEnrichedFunctor.obj X.1, X.2) X.1 := by
  rw [leftGenerator_flatToNested]
  let x := d.tensorEnrichedFunctor.obj X.1
  let p : I × I := (x, X.2)
  let U := (weight d.tensorEnrichedFunctor m).obj (op p)
  let A := F.obj X.1.1 ⊗ G.obj X.1.2
  let B := H.obj X.2
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G x
  let i : A ⟶ (x ⟶[V] x) ⊗ A := AssociatorUnit.identityInsert x A
  let g : (x ⟶[V] x) ⊗ A ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor F G x X.1
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let j : U ⊗ (Y ⊗ B) ⟶ N :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m p
  change (𝟙 U ⊗ₘ ((i ≫ g) ⊗ₘ 𝟙 B)) ≫ j = U ◁ (i ▷ B) ≫ U ◁ (g ▷ B) ≫ j
  simp only [id_tensorHom, tensorHom_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc]

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening

namespace CategoryTheory.EnrichedDayKernel.AssociatorFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The original contracted flat index keeps both inner inputs and the outer final input. -/
abbrev flatIndex (p a : I × I) : (I × I) × I := (a, p.2)
variable [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      F G H m)
    (AssociatorPresentation.Left.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m)]

/-- Descend the original left contraction through both full original relation families. -/
def simultaneousDesc :
    AssociatorPresentation.Left.simultaneousPoint d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m ⟶
      AssociatorFlat.leftPoint d F G H m := by
  let objs : (I × I) × (I × I) → V :=
    AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      F G H m
  let family : ∀ pi, objs pi ⟶ AssociatorFlat.leftPoint d F G H m := fun pi =>
    contractWord d F G H m pi.1 pi.2 ≫ AssociatorFlat.leftGenerator d F G H m (flatIndex pi.1 pi.2)
  refine coequalizer.desc (Sigma.desc (f := objs) family) ?_
  apply Sigma.hom_ext
  intro r
  cases r with
  | inl pqi =>
    simp only [AssociatorPresentation.Left.simultaneousLeftMap,
      AssociatorPresentation.Left.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Left.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Left.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Left.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
      pqi.1.1 pqi.1.2 pqi.2
    let r := AssociatorFaces.Left.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
      pqi.1.1 pqi.1.2 pqi.2
    have hl : (l ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pqi.1.1, pqi.2) :=
      (Category.assoc l (Sigma.ι objs (pqi.1.1, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.1, pqi.2)))
    have hr : (r ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pqi.1.2, pqi.2) :=
      (Category.assoc r (Sigma.ι objs (pqi.1.2, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.2, pqi.2)))
    have hb : l ≫ family (pqi.1.1, pqi.2) = r ≫ family (pqi.1.2, pqi.2) :=
      contractWord_outer d F G H m pqi.1.1 pqi.1.2 pqi.2
    exact hl.trans (hb.trans hr.symm)
  | inr pij =>
    simp only [AssociatorPresentation.Left.simultaneousLeftMap,
      AssociatorPresentation.Left.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Left.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Left.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Left.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
      pij.1 pij.2.1 pij.2.2
    let r := AssociatorFaces.Left.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
      pij.1 pij.2.1 pij.2.2
    have hl : (l ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pij.1, pij.2.1) :=
      (Category.assoc l (Sigma.ι objs (pij.1, pij.2.1)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.1)))
    have hr : (r ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pij.1, pij.2.2) :=
      (Category.assoc r (Sigma.ι objs (pij.1, pij.2.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.2)))
    have hb : l ≫ family (pij.1, pij.2.1) = r ≫ family (pij.1, pij.2.2) :=
      contractWord_inner d F G H m pij.1 pij.2.1 pij.2.2
    exact hl.trans (hb.trans hr.symm)

/-- The simultaneous descent retains the actual original contraction on every raw right word. -/
@[reassoc]
theorem simultaneousProjection_simultaneousDesc (p a : I × I) :
    AssociatorPresentation.Left.simultaneousProjection d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m p a ≫
        simultaneousDesc d F G H m =
      contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (flatIndex p a) := by
  simp only [AssociatorPresentation.Left.simultaneousProjection, simultaneousDesc,
    Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.objects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
    (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)
    (AssociatorPresentation.Left.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [HasCoproduct (AssociatorPresentation.Left.innerObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)
    (AssociatorPresentation.Left.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
    d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
    d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)]

/-- The actual original left nested Day value descends to its unchanged selected flat triple coend.
-/
def nestedToFlat :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m ⟶
      AssociatorFlat.leftPoint d F G H m :=
  (AssociatorNested.Left.simultaneousIso d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
    m).hom ≫
    simultaneousDesc d F G H m

/-- Both original left generator legs contract to the exact original left flat summand. -/
@[reassoc]
theorem nestedGenerator_nestedToFlat (p a : I × I) :
    AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a
      ≫
        nestedToFlat d F G H m =
      contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (flatIndex p a) := by
  simp only [nestedToFlat, ← Category.assoc]
  rw [AssociatorNested.Left.nestedGenerator_simultaneousIso_hom,
    simultaneousProjection_simultaneousDesc]
  simp only [contractWord, Category.assoc]

/-- The original nested generators prove the left comparison's nested inverse equation. -/
@[reassoc]
theorem nestedToFlat_flatToNested :
    nestedToFlat d F G H m ≫ flatToNested d F G H m =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
        H m) := by
  apply AssociatorNested.Left.hom_ext d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
  intro p a
  rw [← Category.assoc, nestedGenerator_nestedToFlat]
  simpa only [Category.assoc, Category.comp_id] using contractWord_generator_factorization d F G H m
    p a

/-- Actual identity insertion proves the left comparison's flat inverse equation. -/
@[reassoc]
theorem flatToNested_nestedToFlat :
    flatToNested d F G H m ≫ nestedToFlat d F G H m = 𝟙 (AssociatorFlat.leftPoint d F G H m) := by
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d m) (Associator.leftCoefficients
    F G H)
  intro X
  rcases X with ⟨⟨e, g⟩, h⟩
  have hx := leftGenerator_flatToNested_identity d F G H m ((e, g), h)
  have hn := nestedGenerator_nestedToFlat d F G H m (d.tensorEnrichedFunctor.obj (e, g), h) (e, g)
  have hi := identityWord_contractWord d F G H m ((e, g), h)
  rw [← Category.assoc, hx, Category.assoc, hn]
  rw [← Category.assoc, hi]
  simp only [Category.id_comp, Category.comp_id]

/-- The genuine left flattening comparison on the original nested Day value and chosen coends. -/
def iso : AssociatorFlat.leftPoint d F G H m ≅
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m
      where
  hom := flatToNested d F G H m
  inv := nestedToFlat d F G H m
  hom_inv_id := flatToNested_nestedToFlat d F G H m
  inv_hom_id := nestedToFlat_flatToNested d F G H m


/-- The actual left comparison preserves every original flat generator and its identity leg. -/
@[reassoc]
theorem leftGenerator_iso_hom (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ (iso d F G H m).hom =
      (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] m) ⊗ₘ
        (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2))) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H
          m
          ((AssociatorTensor.leftProduct d).obj X) := leftGenerator_flatToNested d F G H m X

/-- The inverse keeps both original nested generator legs and their full original weight
  contraction. -/
@[reassoc]
theorem nestedGenerator_iso_inv (p a : I × I) :
    AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a
      ≫
        (iso d F G H m).inv =
      contractWord d F G H m p a ≫ AssociatorFlat.leftGenerator d F G H m (flatIndex p a) :=
  nestedGenerator_nestedToFlat d F G H m p a

end CategoryTheory.EnrichedDayKernel.AssociatorFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightTensor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {K : Type uK} [EnrichedCategory V K]
attribute [local instance] Enriched.prodCategory

/-- The full right product map, with the actual original three-Hom reassociation. -/
abbrev product (T : EnrichedFunctor V (D × E) K) :
    EnrichedFunctor V ((C × D) × E) (C × K) :=
  (Associator.productAssociator (V := V) (A := C) (B := D) (C := E)).comp V
    (prodEnrichedFunctor (EnrichedFunctor.id V C) T)

section Coefficients
variable (T : EnrichedFunctor V (D × E) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k)
    (EnrichedDayKernel.rightMap T G H k)]

/-- Insert the inner Day unit generator in the final two coefficients, keeping the first
  coefficient fixed on `C × (D × E)`. -/
abbrev coefficientMapBase (X : C × (D × E)) :
    (F.externalTensor (G.externalTensor H)).obj X ⟶
      (F.externalTensor (Output.functor T G H)).obj
        ((prodEnrichedFunctor (EnrichedFunctor.id V C) T).obj X) :=
  𝟙 (F.obj X.1) ⊗ₘ AssociatorUnit.unitGenerator T G H X.2

theorem coefficientMapBase_naturality (X Y : C × (D × E)) :
    MonoidalClosed.uncurry ((F.externalTensor (G.externalTensor H)).map X Y) ≫
        coefficientMapBase T F G H Y =
      (coefficientMapBase T F G H X ⊗ₘ
        (prodEnrichedFunctor (EnrichedFunctor.id V C) T).map X Y) ≫
        MonoidalClosed.uncurry ((F.externalTensor (Output.functor T G H)).map
          ((prodEnrichedFunctor (EnrichedFunctor.id V C) T).obj X)
          ((prodEnrichedFunctor (EnrichedFunctor.id V C) T).obj Y)) := by
  let A := F.obj X.1
  let A' := F.obj Y.1
  let B := G.obj X.2.1 ⊗ H.obj X.2.2
  let B' := G.obj Y.2.1 ⊗ H.obj Y.2.2
  let P : V := X.1 ⟶[V] Y.1
  let S : V := X.2 ⟶[V] Y.2
  let R : V := T.obj X.2 ⟶[V] T.obj Y.2
  let U := EnrichedDayKernel.obj T G H (T.obj X.2)
  let U' := EnrichedDayKernel.obj T G H (T.obj Y.2)
  let ua : B ⟶ U := AssociatorUnit.unitGenerator T G H X.2
  let ub : B' ⟶ U' := AssociatorUnit.unitGenerator T G H Y.2
  let t : S ⟶ R := T.map X.2 Y.2
  let f : A ⊗ P ⟶ A' := MonoidalClosed.uncurry (F.map X.1 Y.1)
  let g : B ⊗ S ⟶ B' := MonoidalClosed.uncurry ((G.externalTensor H).map X.2 Y.2)
  let o : U ⊗ R ⟶ U' := MonoidalClosed.uncurry (Output.map T G H (T.obj X.2) (T.obj Y.2))
  have hu : g ≫ ub = (ua ⊗ₘ t) ≫ o := by
    have h := AssociatorUnit.unitGenerator_naturality T G H X.2 Y.2
    change g ≫ ub = (ua ⊗ₘ 𝟙 S) ≫ U ◁ t ≫ o at h
    simpa only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id] using h
  rw [EnrichedFunctor.externalTensor_uncurry F (G.externalTensor H) X Y,
    EnrichedFunctor.externalTensor_uncurry F (Output.functor T G H)
      ((prodEnrichedFunctor (EnrichedFunctor.id V C) T).obj X)
      ((prodEnrichedFunctor (EnrichedFunctor.id V C) T).obj Y)]
  change (tensorμ A B P S ≫ (f ⊗ₘ g)) ≫ (𝟙 A' ⊗ₘ ub) =
    ((𝟙 A ⊗ₘ ua) ⊗ₘ (𝟙 P ⊗ₘ t)) ≫ tensorμ A U P R ≫ (f ⊗ₘ o)
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.comp_id, hu]
  have hm := tensorμ_natural_assoc (𝟙 A) ua (𝟙 P) t (f ⊗ₘ o)
  simpa only [id_tensorHom_id, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using hm.symm

/-- Insert the final-two Day unit generator in the right-associated coefficient word
  indexed by `(C × D) × E`. -/
abbrev coefficientMap (X : (C × D) × E) :
    (Associator.rightCoefficients F G H).obj X ⟶
      (F.externalTensor (Output.functor T G H)).obj ((product (C := C) T).obj X) :=
  𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator T G H (X.1.2, X.2)

theorem coefficientMap_naturality (X Y : (C × D) × E) :
    MonoidalClosed.uncurry ((Associator.rightCoefficients F G H).map X Y) ≫
        coefficientMap T F G H Y =
      (coefficientMap T F G H X ⊗ₘ (product (C := C) T).map X Y) ≫
        MonoidalClosed.uncurry ((F.externalTensor (Output.functor T G H)).map
          ((product (C := C) T).obj X) ((product (C := C) T).obj Y)) := by
  let P := Associator.productAssociator (V := V) (A := C) (B := D) (C := E)
  let Q := prodEnrichedFunctor (EnrichedFunctor.id V C) T
  let L := F.externalTensor (G.externalTensor H)
  let R := F.externalTensor (Output.functor T G H)
  let qX : L.obj (P.obj X) ⟶ R.obj (Q.obj (P.obj X)) := coefficientMapBase T F G H (P.obj X)
  let qY : L.obj (P.obj Y) ⟶ R.obj (Q.obj (P.obj Y)) := coefficientMapBase T F G H (P.obj Y)
  let p : (X ⟶[V] Y) ⟶ (P.obj X ⟶[V] P.obj Y) := P.map X Y
  let q : (P.obj X ⟶[V] P.obj Y) ⟶ (Q.obj (P.obj X) ⟶[V] Q.obj (P.obj Y)) :=
    Q.map (P.obj X) (P.obj Y)
  change MonoidalClosed.uncurry (p ≫ L.map (P.obj X) (P.obj Y)) ≫ qY =
    (qX ⊗ₘ (p ≫ q)) ≫ MonoidalClosed.uncurry (R.map (Q.obj (P.obj X)) (Q.obj (P.obj Y)))
  rw [MonoidalClosed.uncurry_natural_left]
  have h := coefficientMapBase_naturality T F G H (P.obj X) (P.obj Y)
  change MonoidalClosed.uncurry (L.map (P.obj X) (P.obj Y)) ≫ qY =
    (qX ⊗ₘ q) ≫ MonoidalClosed.uncurry (R.map (Q.obj (P.obj X)) (Q.obj (P.obj Y))) at h
  rw [Category.assoc, h]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
end Coefficients

section Weight
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I) (m : I)

/-- The identity identification of the flat right weight with the outer Day weight after
  partially tensoring the final two indices. -/
abbrev weightMap (X : (I × I) × I) :
    (AssociatorIndex.rightWeight d m).obj (op X) ⟶
      (weight d.tensorEnrichedFunctor m).obj (op ((product d.tensorEnrichedFunctor).obj X)) := 𝟙 _

omit [MonoidalClosed V] in
theorem index_map (X Y : (I × I) × I) :
    (AssociatorIndex.rightIndex d).map X Y =
      (product d.tensorEnrichedFunctor).map X Y ≫
        d.tensorEnrichedFunctor.map ((product d.tensorEnrichedFunctor).obj X)
          ((product d.tensorEnrichedFunctor).obj Y) := by
  change (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (X.1.1 ⟶[V] Y.1.1) ◁ d.tensorMap X.1.2 Y.1.2 X.2 Y.2 ≫
        d.tensorMap X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2) =
      ((α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (𝟙 (X.1.1 ⟶[V] Y.1.1) ⊗ₘ d.tensorMap X.1.2 Y.1.2 X.2 Y.2)) ≫
        d.tensorMap X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)
  simp only [id_tensorHom, Category.assoc]

theorem weightMap_naturality (X Y : (I × I) × I) :
    MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map (op Y) (op X)) ≫
        weightMap d m X =
      (weightMap d m Y ⊗ₘ (product d.tensorEnrichedFunctor).map X Y) ≫
        MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
          (op ((product d.tensorEnrichedFunctor).obj Y))
          (op ((product d.tensorEnrichedFunctor).obj X))) := by
  rw [weight_uncurry_map (AssociatorIndex.rightIndex d) m X Y,
    weight_uncurry_map d.tensorEnrichedFunctor m
      ((product d.tensorEnrichedFunctor).obj X) ((product d.tensorEnrichedFunctor).obj Y)]
  let RX := X.1.1 ⊗ (X.1.2 ⊗ X.2)
  let RY := Y.1.1 ⊗ (Y.1.2 ⊗ Y.2)
  let WX : V := RX ⟶[V] m
  let WY : V := RY ⟶[V] m
  let P : V := X ⟶[V] Y
  let Q : V := (X.1.1 ⟶[V] Y.1.1) ⊗ ((X.1.2 ⊗ X.2) ⟶[V] (Y.1.2 ⊗ Y.2))
  let l : P ⟶ (RX ⟶[V] RY) := (AssociatorIndex.rightIndex d).map X Y
  let s : P ⟶ Q := (product d.tensorEnrichedFunctor).map X Y
  let u : Q ⟶ (RX ⟶[V] RY) := d.tensorEnrichedFunctor.map
    ((product d.tensorEnrichedFunctor).obj X) ((product d.tensorEnrichedFunctor).obj Y)
  have hl : l = s ≫ u := index_map d X Y
  change (WY ◁ l ≫ (β_ WY (RX ⟶[V] RY)).hom ≫ eComp V RX RY m) ≫ 𝟙 WX =
    (𝟙 WY ⊗ₘ s) ≫ WY ◁ u ≫ (β_ WY (RX ⟶[V] RY)).hom ≫ eComp V RX RY m
  simp only [id_tensorHom, ← whiskerLeft_comp_assoc]
  rw [hl]
  exact Category.comp_id _
end Weight
end CategoryTheory.EnrichedDayKernel.AssociatorRightTensor


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) m)]

/-- Descend the original right triple into the chosen original right nested Day value. -/
def flatToNested : AssociatorFlat.rightPoint d F G H m ⟶
    EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m
      :=
  Enriched.weightedCoend.Transport.map (AssociatorRightTensor.product d.tensorEnrichedFunctor)
    (AssociatorIndex.rightWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.rightCoefficients F G H)
    (F.externalTensor (Output.functor d.tensorEnrichedFunctor G H))
    (AssociatorRightTensor.weightMap d m)
    (fun X => AssociatorRightTensor.coefficientMap d.tensorEnrichedFunctor F G H X)
    (AssociatorRightTensor.weightMap_naturality d m)
    (AssociatorRightTensor.coefficientMap_naturality d.tensorEnrichedFunctor F G H)

@[reassoc]
theorem rightGenerator_flatToNested (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ flatToNested d F G H m =
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] m) ⊗ₘ
        (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)))
          ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          F (Output.functor d.tensorEnrichedFunctor G H) m
          ((AssociatorRightTensor.product d.tensorEnrichedFunctor).obj X) :=
  Enriched.weightedCoend.Transport.ι_map (AssociatorRightTensor.product d.tensorEnrichedFunctor)
    (AssociatorIndex.rightWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.rightCoefficients F G H)
    (F.externalTensor (Output.functor d.tensorEnrichedFunctor G H))
    (AssociatorRightTensor.weightMap d m)
    (fun X => AssociatorRightTensor.coefficientMap d.tensorEnrichedFunctor F G H X)
    (AssociatorRightTensor.weightMap_naturality d m)
    (AssociatorRightTensor.coefficientMap_naturality d.tensorEnrichedFunctor F G H) X
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The original ordered right triple index of a right nested generator. -/
abbrev flatIndex (p a : I × I) : (I × I) × I := ((p.1, a.1), a.2)

/-- Full enriched precomposition along the slice with its original first index fixed. -/
abbrev sliceBase (p a : I × I) :
    (weight d.tensorEnrichedFunctor m).obj (op p) ⊗
        (d.tensorEnrichedFunctor.obj a ⟶[V] p.2) ⟶
      (weight d.tensorEnrichedFunctor m).obj (op (p.1, d.tensorEnrichedFunctor.obj a)) :=
  (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      (EnrichedFunctor.prodRightInclusion (V := V) (B := I) p.1).map
        (d.tensorEnrichedFunctor.obj a) p.2 ≫
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
      (op p) (op (p.1, d.tensorEnrichedFunctor.obj a)))

/-- Contract the full original right nested generator word into its original flat summand. -/
abbrev contractWord (p a : I × I) :
    AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p a ⟶
      AssociatorFlat.rightObjects d F G H m (flatIndex p a) :=
  (weight d.tensorEnrichedFunctor m).obj (op p) ◁
      (AssociatorRightContraction.frontHomIso (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)
        (F.obj p.1) (G.obj a.1 ⊗ H.obj a.2)).hom ≫
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op p))
      (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)
      (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2))).inv ≫
    (sliceBase d m p a ⊗ₘ 𝟙 (F.obj p.1 ⊗ (G.obj a.1 ⊗ H.obj a.2)))

variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) m)]

/-- The complete right contraction factors the actual original right nested generator. -/
@[reassoc]
theorem contractWord_generator_factorization (p a : I × I) :
    contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) ≫
        flatToNested d F G H m =
      AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor G H F m p a := by
  let x := d.tensorEnrichedFunctor.obj a
  let B := F.obj p.1
  let A := G.obj a.1 ⊗ H.obj a.2
  let R : V := x ⟶[V] p.2
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor G H p.2
  let X := EnrichedDayKernel.obj d.tensorEnrichedFunctor G H x
  let u : A ⟶ X := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H a
  let g : R ⊗ A ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor G H p.2 a
  let o : X ⊗ R ⟶ Y := MonoidalClosed.uncurry
    (Output.map d.tensorEnrichedFunctor G H x p.2)
  have hd : R ◁ u ≫ (β_ R X).hom ≫ o = g := by
    have hm := Output.map_uncurry d.tensorEnrichedFunctor G H x p.2
    change o = (β_ R X).inv ≫
      MonoidalClosed.uncurry (Output.actionDesc d.tensorEnrichedFunctor G H x p.2) at hm
    rw [hm]
    simp only [Iso.hom_inv_id_assoc]
    exact AssociatorUnit.unitGenerator_action d.tensorEnrichedFunctor G H a p.2
  have hc := AssociatorRightContraction.leftSlice_condition
    (weight d.tensorEnrichedFunctor m) F (Output.functor d.tensorEnrichedFunctor G H)
    p.1 x p.2 u
  rw [rightGenerator_flatToNested]
  let Wb := (weight d.tensorEnrichedFunctor m).obj (op p)
  let Wa := (weight d.tensorEnrichedFunctor m).obj (op (p.1, x))
  let k : Wb ⊗ R ⟶ Wa := sliceBase d m p a
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m
  let ga : Wa ⊗ (B ⊗ X) ⟶ N := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m (p.1, x)
  let gb : Wb ⊗ (B ⊗ Y) ⟶ N := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m p
  change (Wb ◁ (AssociatorRightContraction.frontHomIso R B A).hom ≫
      (α_ Wb R (B ⊗ A)).inv ≫ (k ⊗ₘ 𝟙 (B ⊗ A))) ≫
      (𝟙 Wa ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ ga = Wb ◁ (B ◁ g) ≫ gb
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  change Wb ◁ (AssociatorRightContraction.frontHomIso R B A).hom ≫
      (α_ Wb R (B ⊗ A)).inv ≫ (k ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ ga =
    Wb ◁ (B ◁ (R ◁ u ≫ (β_ R X).hom ≫ o)) ≫ gb at hc
  rw [hd] at hc
  exact hc
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightTensor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- Reverse the actual enriched product associator on objects and complete Hom objects. -/
def productAssociatorInv : EnrichedFunctor V (C × (D × E)) ((C × D) × E) where
  obj X := ((X.1, X.2.1), X.2.2)
  map X Y := (α_ (X.1 ⟶[V] Y.1) (X.2.1 ⟶[V] Y.2.1) (X.2.2 ⟶[V] Y.2.2)).inv
  map_id X := by
    let L := ((X.1, X.2.1), X.2.2)
    let a := α_ (X.1 ⟶[V] X.1) (X.2.1 ⟶[V] X.2.1) (X.2.2 ⟶[V] X.2.2)
    have h := (Associator.productAssociator (V := V) (A := C) (B := D) (C := E)).map_id L
    change eId V L ≫ a.hom = eId V X at h
    change eId V X ≫ a.inv = eId V L
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  map_comp X Y Z := by
    let LX := ((X.1, X.2.1), X.2.2)
    let LY := ((Y.1, Y.2.1), Y.2.2)
    let LZ := ((Z.1, Z.2.1), Z.2.2)
    let a := α_ (X.1 ⟶[V] Y.1) (X.2.1 ⟶[V] Y.2.1) (X.2.2 ⟶[V] Y.2.2)
    let b := α_ (Y.1 ⟶[V] Z.1) (Y.2.1 ⟶[V] Z.2.1) (Y.2.2 ⟶[V] Z.2.2)
    let c := α_ (X.1 ⟶[V] Z.1) (X.2.1 ⟶[V] Z.2.1) (X.2.2 ⟶[V] Z.2.2)
    have h := (Associator.productAssociator (V := V) (A := C) (B := D) (C := E)).map_comp LX LY LZ
    change eComp V LX LY LZ ≫ c.hom = (a.hom ⊗ₘ b.hom) ≫ eComp V X Y Z at h
    change eComp V X Y Z ≫ c.inv = (a.inv ⊗ₘ b.inv) ≫ eComp V LX LY LZ
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Iso.inv_hom_id, id_tensorHom_id]
    exact (Category.id_comp _).symm

/-- Insert the actual fixed first input into the unchanged original flat triple index. -/
abbrev innerInclusion (e : C) : EnrichedFunctor V (D × E) ((C × D) × E) :=
  (EnrichedFunctor.prodRightInclusion (V := V) (B := D × E) e).comp V
    (productAssociatorInv (V := V) (C := C) (D := D) (E := E))

@[simp]
theorem innerInclusion_obj (e : C) (a : D × E) :
    (innerInclusion (V := V) e).obj a = ((e, a.1), a.2) := rfl

theorem innerInclusion_map (e : C) (a b : D × E) :
    (innerInclusion (V := V) e).map a b =
      (λ_ (a ⟶[V] b)).inv ≫ (eId V e ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        (α_ (e ⟶[V] e) (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2)).inv := by
  change ((λ_ (a ⟶[V] b)).inv ≫ (eId V e ⊗ₘ 𝟙 (a ⟶[V] b))) ≫ _ = _
  exact Category.assoc _ _ _

theorem innerInclusion_product_map (e : C) (a b : D × E) :
    (innerInclusion (V := V) e).map a b ≫
        (Associator.productAssociator (V := V) (A := C) (B := D) (C := E)).map
          ((innerInclusion (V := V) e).obj a) ((innerInclusion (V := V) e).obj b) =
      (EnrichedFunctor.prodRightInclusion (V := V) (B := D × E) e).map a b := by
  change (((λ_ (a ⟶[V] b)).inv ≫ (eId V e ⊗ₘ 𝟙 (a ⟶[V] b))) ≫
      (α_ (e ⟶[V] e) (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2)).inv) ≫
      (α_ (e ⟶[V] e) (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2)).hom =
    (λ_ (a ⟶[V] b)).inv ≫ (eId V e ⊗ₘ 𝟙 (a ⟶[V] b))
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end CategoryTheory.EnrichedDayKernel.AssociatorRightTensor


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (J : EnrichedFunctor V A B) (W : EnrichedFunctor V Bᵒᵖ V) (Q : EnrichedFunctor V B V)
  [HasCoproduct (Enriched.weightedCoend.objects W Q)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q)]

/-- Pull the entire original coend balance back along a genuine enriched index functor. -/
@[reassoc]
theorem index_condition (a b : A) :
    (α_ (W.obj (op (J.obj b))) (a ⟶[V] b) (Q.obj (J.obj a))).inv ≫
        ((W.obj (op (J.obj b)) ◁ J.map a b ≫
          MonoidalClosed.uncurry (W.map (op (J.obj b)) (op (J.obj a)))) ⊗ₘ
          𝟙 (Q.obj (J.obj a))) ≫ Enriched.weightedCoend.ι W Q (J.obj a) =
      W.obj (op (J.obj b)) ◁
          ((J.map a b ⊗ₘ 𝟙 (Q.obj (J.obj a))) ≫
            (β_ (J.obj a ⟶[V] J.obj b) (Q.obj (J.obj a))).hom ≫
              MonoidalClosed.uncurry (Q.map (J.obj a) (J.obj b))) ≫
        Enriched.weightedCoend.ι W Q (J.obj b) := by
  let U := W.obj (op (J.obj b))
  let R : V := a ⟶[V] b
  let S : V := J.obj a ⟶[V] J.obj b
  let X := Q.obj (J.obj a)
  let Y := Q.obj (J.obj b)
  let j : R ⟶ S := J.map a b
  let w : U ⊗ S ⟶ W.obj (op (J.obj a)) :=
    MonoidalClosed.uncurry (W.map (op (J.obj b)) (op (J.obj a)))
  let act : S ⊗ X ⟶ Y := (β_ S X).hom ≫ MonoidalClosed.uncurry (Q.map (J.obj a) (J.obj b))
  let l : U ⊗ (S ⊗ X) ⟶ W.obj (op (J.obj a)) ⊗ X := (α_ U S X).inv ≫ (w ⊗ₘ 𝟙 X)
  let r : U ⊗ (S ⊗ X) ⟶ U ⊗ Y := U ◁ act
  let ga := Enriched.weightedCoend.ι W Q (J.obj a)
  let gb := Enriched.weightedCoend.ι W Q (J.obj b)
  have hb : l ≫ ga = r ≫ gb := Enriched.weightedCoend.condition W Q (J.obj a) (J.obj b)
  have h0 : U ◁ (j ⊗ₘ 𝟙 X) ≫ l = (α_ U R X).inv ≫ ((U ◁ j ≫ w) ⊗ₘ 𝟙 X) := by
    have hn := associator_inv_naturality (𝟙 U) j (𝟙 X)
    simpa only [l, id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, Category.assoc] using
      congrArg (fun f => f ≫ (w ⊗ₘ 𝟙 X)) hn
  have h1 : U ◁ (j ⊗ₘ 𝟙 X) ≫ r = U ◁ ((j ⊗ₘ 𝟙 X) ≫ act) :=
    (whiskerLeft_comp U (j ⊗ₘ 𝟙 X) act).symm
  have hc := congrArg (fun f => U ◁ (j ⊗ₘ 𝟙 X) ≫ f) hb
  change (α_ U R X).inv ≫ ((U ◁ j ≫ w) ⊗ₘ 𝟙 X) ≫ ga =
    U ◁ ((j ⊗ₘ 𝟙 X) ≫ act) ≫ gb
  simpa only [← Category.assoc, h0, h1] using hc
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorInclusion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- The actual fixed-first inclusion commutes with the entire map of a product functor. -/
theorem leftInclusion_product_map (T : EnrichedFunctor V C K) (e : E) (a b : C) :
    (EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a b ≫
      (prodEnrichedFunctor (EnrichedFunctor.id V E) T).map (e, a) (e, b) =
    T.map a b ≫
      (EnrichedFunctor.prodRightInclusion (V := V) (B := K) e).map (T.obj a) (T.obj b) := by
  let R : V := a ⟶[V] b
  let S : V := T.obj a ⟶[V] T.obj b
  let P : V := e ⟶[V] e
  let t : R ⟶ S := T.map a b
  let q : 𝟙_ V ⟶ P := eId V e
  change ((λ_ R).inv ≫ (q ⊗ₘ 𝟙 R)) ≫ (𝟙 P ⊗ₘ t) =
    t ≫ ((λ_ S).inv ≫ (q ⊗ₘ 𝟙 S))
  simp only [Category.assoc]
  have ht : (q ⊗ₘ 𝟙 R) ≫ (𝟙 P ⊗ₘ t) = q ⊗ₘ t := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hu : (𝟙_ V) ◁ t ≫ (q ⊗ₘ 𝟙 S) = q ⊗ₘ t := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [ht, ← hu, leftUnitor_inv_naturality_assoc]

/-- Lift the full original precomposition through the genuine fixed-first inclusion. -/
@[reassoc]
theorem leftInclusion_precomposition (e : E) (a b c : C)
    {P : V} (t : P ⟶ (a ⟶[V] b)) :
    ((EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map b c ⊗ₘ
        (t ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a b)) ≫
      (β_ ((e, b) ⟶[V] (e, c)) ((e, a) ⟶[V] (e, b))).hom ≫
      eComp V (e, a) (e, b) (e, c) =
    (b ⟶[V] c) ◁ t ≫ (β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫
      eComp V a b c ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := C) e).map a c := by
  let J := EnrichedFunctor.prodRightInclusion (V := V) (B := C) e
  let R : V := b ⟶[V] c
  let S : V := a ⟶[V] b
  let j1 : R ⟶ ((e, b) ⟶[V] (e, c)) := J.map b c
  let j2 : S ⟶ ((e, a) ⟶[V] (e, b)) := J.map a b
  let k := eComp V (e, a) (e, b) (e, c)
  let j3 : (a ⟶[V] c) ⟶ ((e, a) ⟶[V] (e, c)) := J.map a c
  have hn := BraidedCategory.braiding_naturality_assoc j1 (t ≫ j2) k
  have hc : (j2 ⊗ₘ j1) ≫ k = eComp V a b c ≫ j3 :=
    (J.map_comp a b c).symm
  change (j1 ⊗ₘ (t ≫ j2)) ≫ (β_ _ _).hom ≫ k =
    R ◁ t ≫ (β_ R S).hom ≫ eComp V a b c ≫ j3
  rw [hn]
  have ht : ((t ≫ j2) ⊗ₘ j1) = (t ⊗ₘ 𝟙 R) ≫ (j2 ⊗ₘ j1) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht, Category.assoc, hc]
  simpa only [tensorHom_id] using
    (BraidedCategory.braiding_naturality_right_assoc R t (eComp V a b c ≫ j3)).symm
end CategoryTheory.EnrichedDayKernel.AssociatorInclusion


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
/-- Contract an arbitrary full inner Hom into its actual weight map. -/
abbrev frontMap {K R W : V} (k : K ⊗ R ⟶ W) (B A : V) :
    K ⊗ (B ⊗ (R ⊗ A)) ⟶ W ⊗ (B ⊗ A) :=
  K ◁ (frontHomIso R B A).hom ≫ (α_ K R (B ⊗ A)).inv ≫ (k ⊗ₘ 𝟙 (B ⊗ A))

omit [MonoidalClosed V] in
/-- Preserve the entire additional inner-relation Hom before contracting the weight. -/
abbrev frontRelationMap {K R W : V} (k : K ⊗ R ⟶ W) (B P A : V) :
    K ⊗ (B ⊗ (R ⊗ (P ⊗ A))) ⟶ W ⊗ (P ⊗ (B ⊗ A)) :=
  frontMap k B (P ⊗ A) ≫ W ◁ (frontHomIso P B A).hom

omit [MonoidalClosed V] in
@[reassoc]
theorem frontHomIso_naturality_hom {R R' : V} (f : R ⟶ R') (B A : V) :
    B ◁ (f ⊗ₘ 𝟙 A) ≫ (frontHomIso R' B A).hom =
      (frontHomIso R B A).hom ≫ (f ⊗ₘ 𝟙 (B ⊗ A)) := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [← id_tensorHom B (f ⊗ₘ 𝟙 A), associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  have hb := BraidedCategory.braiding_naturality (𝟙 B) f
  rw [hb]
  rw [← tensorHom_comp_tensorHom_assoc]
  rw [associator_naturality]
  simp only [id_tensorHom_id]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_naturality_hom {K R R' W : V} (f : R ⟶ R')
    (k : K ⊗ R' ⟶ W) (B A : V) :
    K ◁ (B ◁ (f ⊗ₘ 𝟙 A)) ≫ frontMap k B A =
      frontMap (K ◁ f ≫ k) B A := by
  simp only [frontMap]
  rw [← whiskerLeft_comp_assoc, frontHomIso_naturality_hom]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← id_tensorHom K (f ⊗ₘ 𝟙 (B ⊗ A)), associator_inv_naturality_assoc]
  simp only [id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontHomIso_naturality_coefficient (R B : V) {A A' : V} (a : A ⟶ A') :
    B ◁ (R ◁ a) ≫ (frontHomIso R B A').hom =
      (frontHomIso R B A).hom ≫ R ◁ (B ◁ a) := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [← id_tensorHom R a, ← id_tensorHom B (𝟙 R ⊗ₘ a),
    associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
  have ht : (β_ B R).hom ⊗ₘ a =
      ((β_ B R).hom ⊗ₘ 𝟙 A) ≫ (𝟙 (R ⊗ B) ⊗ₘ a) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have ha : (𝟙 (R ⊗ B) ⊗ₘ a) ≫ (α_ R B A').hom =
      (α_ R B A).hom ≫ R ◁ (B ◁ a) := by
    simpa only [id_tensorHom_id, id_tensorHom, whiskerLeft_id] using
      associator_naturality (𝟙 R) (𝟙 B) a
  rw [ht, Category.assoc, ha]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_naturality_coefficient {K R W A A' : V}
    (k : K ⊗ R ⟶ W) (B : V) (a : A ⟶ A') :
    K ◁ (B ◁ (R ◁ a)) ≫ frontMap k B A' =
      frontMap k B A ≫ W ◁ (B ◁ a) := by
  simp only [frontMap, tensorHom_id, Category.assoc]
  rw [← whiskerLeft_comp_assoc, frontHomIso_naturality_coefficient]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange]

omit [MonoidalClosed V] in
private theorem frontMap_composition_pure (K R P B A : V) :
    K ◁ (B ◁ (α_ R P A).inv) ≫ K ◁ (frontHomIso (R ⊗ P) B A).hom ≫
        (α_ K (R ⊗ P) (B ⊗ A)).inv ≫ (α_ K R P).inv ▷ (B ⊗ A) =
      K ◁ (frontHomIso R B (P ⊗ A)).hom ≫
        (α_ K R (B ⊗ (P ⊗ A))).inv ≫
        (K ⊗ R) ◁ (frontHomIso P B A).hom ≫ (α_ (K ⊗ R) P (B ⊗ A)).inv := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, BraidedCategory.braiding_tensor_right_hom,
    tensorHom_def, Category.assoc]
  monoidal

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_composition {K R W P Z : V} (k : K ⊗ R ⟶ W)
    (v : W ⊗ P ⟶ Z) (B A : V) :
    K ◁ (B ◁ (α_ R P A).inv) ≫
        frontMap ((α_ K R P).inv ≫ (k ⊗ₘ 𝟙 P) ≫ v) B A =
      frontRelationMap k B P A ≫ (α_ W P (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A)) := by
  let C := B ⊗ A
  let D := B ⊗ (P ⊗ A)
  let h : D ⟶ P ⊗ C := (frontHomIso P B A).hom
  have hn : (k ⊗ₘ 𝟙 D) ≫ W ◁ h = (K ⊗ R) ◁ h ≫ (k ⊗ₘ 𝟙 (P ⊗ C)) := by
    simp only [tensorHom_id]
    exact (whisker_exchange k h).symm
  have ha : (k ⊗ₘ 𝟙 (P ⊗ C)) ≫ (α_ W P C).inv =
      (α_ (K ⊗ R) P C).inv ≫ ((k ⊗ₘ 𝟙 P) ⊗ₘ 𝟙 C) :=
    by simpa only [id_tensorHom_id] using associator_inv_naturality k (𝟙 P) (𝟙 C)
  simp only [frontMap, frontRelationMap, Category.assoc]
  change K ◁ (B ◁ (α_ R P A).inv) ≫ K ◁ (frontHomIso (R ⊗ P) B A).hom ≫
      (α_ K (R ⊗ P) C).inv ≫ (((α_ K R P).inv ≫ (k ⊗ₘ 𝟙 P) ≫ v) ⊗ₘ 𝟙 C) =
    K ◁ (frontHomIso R B (P ⊗ A)).hom ≫ (α_ K R D).inv ≫
      (k ⊗ₘ 𝟙 D) ≫ W ◁ h ≫ (α_ W P C).inv ≫ (v ⊗ₘ 𝟙 C)
  rw [reassoc_of% hn, reassoc_of% ha]
  have ht : (((α_ K R P).inv ≫ (k ⊗ₘ 𝟙 P) ≫ v) ⊗ₘ 𝟙 C) =
      (α_ K R P).inv ▷ C ≫ (((k ⊗ₘ 𝟙 P) ≫ v) ⊗ₘ 𝟙 C) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht]
  simp only [tensorHom_comp_tensorHom, Category.comp_id]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (((k ⊗ₘ 𝟙 P) ≫ v) ⊗ₘ 𝟙 C))
    (frontMap_composition_pure K R P B A)
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
/-- The original right index action through the complete inner inclusion. -/
@[reassoc]
theorem innerInclusion_index_map (e : I) (a b : I × I) :
    (AssociatorRightTensor.innerInclusion (V := V) e).map a b ≫
      (AssociatorIndex.rightIndex d).map
        ((AssociatorRightTensor.innerInclusion (V := V) e).obj a)
        ((AssociatorRightTensor.innerInclusion (V := V) e).obj b) =
    d.tensorEnrichedFunctor.map a b ≫
      (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map
        (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b) ≫
      d.tensorEnrichedFunctor.map (e, d.tensorEnrichedFunctor.obj a)
        (e, d.tensorEnrichedFunctor.obj b) := by
  let P : V := a ⟶[V] b
  let R : V := d.tensorEnrichedFunctor.obj a ⟶[V] d.tensorEnrichedFunctor.obj b
  let E : V := e ⟶[V] e
  let t : P ⟶ R := d.tensorEnrichedFunctor.map a b
  let jP : P ⟶ E ⊗ P := (EnrichedFunctor.prodRightInclusion (V := V) (B := I × I) e).map a b
  let jR : R ⟶ E ⊗ R := (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map
    (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b)
  let x : I := d.tensorEnrichedFunctor.obj (e, d.tensorEnrichedFunctor.obj a)
  let y : I := d.tensorEnrichedFunctor.obj (e, d.tensorEnrichedFunctor.obj b)
  let u : E ⊗ R ⟶ (x ⟶[V] y) :=
    d.tensorEnrichedFunctor.map (e, d.tensorEnrichedFunctor.obj a) (e, d.tensorEnrichedFunctor.obj
      b)
  let r := α_ E (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2)
  change (jP ≫ r.inv) ≫ (r.hom ≫ E ◁ t ≫ u) = t ≫ jR ≫ u
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := AssociatorInclusion.leftInclusion_product_map d.tensorEnrichedFunctor e a b
  change jP ≫ (𝟙 E ⊗ₘ t) = t ≫ jR at h
  simpa only [id_tensorHom, Category.assoc] using congrArg (fun f => f ≫ u) h

/-- The original flat right weight retains exactly the full inner slice action. -/
@[reassoc]
theorem innerInclusion_weight_action (e : I) (a b : I × I) :
    (AssociatorIndex.rightWeight d m).obj
          (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj b)) ◁
        (AssociatorRightTensor.innerInclusion (V := V) e).map a b ≫
      MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
        (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj b))
        (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj a))) =
    (weight d.tensorEnrichedFunctor m).obj (op (e, d.tensorEnrichedFunctor.obj b)) ◁
        (d.tensorEnrichedFunctor.map a b ≫
          (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map
            (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b)) ≫
      MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
        (op (e, d.tensorEnrichedFunctor.obj b)) (op (e, d.tensorEnrichedFunctor.obj a))) := by
  let Xa := (AssociatorRightTensor.innerInclusion (V := V) e).obj a
  let Xb := (AssociatorRightTensor.innerInclusion (V := V) e).obj b
  let x : I := d.tensorEnrichedFunctor.obj (e, d.tensorEnrichedFunctor.obj a)
  let y : I := d.tensorEnrichedFunctor.obj (e, d.tensorEnrichedFunctor.obj b)
  let Wb : V := y ⟶[V] m
  let R : V := x ⟶[V] y
  let j : (a ⟶[V] b) ⟶ (Xa ⟶[V] Xb) := (AssociatorRightTensor.innerInclusion (V := V) e).map a b
  let l : (Xa ⟶[V] Xb) ⟶ R := (AssociatorIndex.rightIndex d).map Xa Xb
  let t : (a ⟶[V] b) ⟶ ((e, d.tensorEnrichedFunctor.obj a) ⟶[V] (e, d.tensorEnrichedFunctor.obj b))
    :=
    d.tensorEnrichedFunctor.map a b ≫ (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map
      (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b)
  let u : ((e, d.tensorEnrichedFunctor.obj a) ⟶[V] (e, d.tensorEnrichedFunctor.obj b)) ⟶ R :=
    d.tensorEnrichedFunctor.map (e, d.tensorEnrichedFunctor.obj a) (e, d.tensorEnrichedFunctor.obj
      b)
  have hm : j ≫ l = t ≫ u := by
    have h := innerInclusion_index_map d e a b
    change j ≫ l = d.tensorEnrichedFunctor.map a b ≫
      (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map
        (d.tensorEnrichedFunctor.obj a) (d.tensorEnrichedFunctor.obj b) ≫ u at h
    exact h.trans (Category.assoc _ _ _).symm
  let wl : Wb ⊗ (Xa ⟶[V] Xb) ⟶ (x ⟶[V] m) :=
    MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map (op Xb) (op Xa))
  let wr : Wb ⊗ ((e, d.tensorEnrichedFunctor.obj a) ⟶[V] (e, d.tensorEnrichedFunctor.obj b)) ⟶
      (x ⟶[V] m) := MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
        (op (e, d.tensorEnrichedFunctor.obj b)) (op (e, d.tensorEnrichedFunctor.obj a)))
  have hl : wl = Wb ◁ l ≫ (β_ Wb R).hom ≫ eComp V x y m :=
    weight_uncurry_map (AssociatorIndex.rightIndex d) m Xa Xb
  have hr : wr = Wb ◁ u ≫ (β_ Wb R).hom ≫ eComp V x y m :=
    weight_uncurry_map d.tensorEnrichedFunctor m
      (e, d.tensorEnrichedFunctor.obj a) (e, d.tensorEnrichedFunctor.obj b)
  change Wb ◁ j ≫ wl = Wb ◁ t ≫ wr
  rw [hl, hr]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hm]

omit [MonoidalCategory I] in
/-- The original flat right coefficient action contracts only the inserted first identity. -/
@[reassoc]
theorem innerInclusion_coefficient_action (e : I) (a b : I × I) :
    ((AssociatorRightTensor.innerInclusion (V := V) e).map a b ⊗ₘ
        𝟙 (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))) ≫
      (β_ (((e, a.1), a.2) ⟶[V] ((e, b.1), b.2))
        (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))).hom ≫
      MonoidalClosed.uncurry ((Associator.rightCoefficients F G H).map
        ((e, a.1), a.2) ((e, b.1), b.2)) =
    (AssociatorRightContraction.frontHomIso (a ⟶[V] b) (F.obj e)
        (G.obj a.1 ⊗ H.obj a.2)).inv ≫ F.obj e ◁
      ((β_ (a ⟶[V] b) (G.obj a.1 ⊗ H.obj a.2)).hom ≫
        MonoidalClosed.uncurry ((G.externalTensor H).map a b)) := by
  let J := AssociatorRightTensor.innerInclusion (V := V) (C := I) (D := I) (E := I) e
  let P := Associator.productAssociator (V := V) (A := I) (B := I) (C := I)
  let Q := F.externalTensor (G.externalTensor H)
  let R : V := a ⟶[V] b
  let S : V := J.obj a ⟶[V] J.obj b
  let S' : V := (e, a) ⟶[V] (e, b)
  let X := F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let Y := F.obj e ⊗ (G.obj b.1 ⊗ H.obj b.2)
  let j : R ⟶ S := J.map a b
  let p : S ⟶ S' := P.map (J.obj a) (J.obj b)
  let i : R ⟶ S' := (EnrichedFunctor.prodRightInclusion (V := V) (B := I × I) e).map a b
  let r : S' ⟶ (ihom X).obj Y := Q.map (e, a) (e, b)
  let l : S ⟶ (ihom X).obj Y := (Associator.rightCoefficients F G H).map
    ((e, a.1), a.2) ((e, b.1), b.2)
  let q : X ⊗ S' ⟶ Y := MonoidalClosed.uncurry r
  have hm : j ≫ p = i := AssociatorRightTensor.innerInclusion_product_map e a b
  have hl : l = p ≫ r := rfl
  have hu : MonoidalClosed.uncurry l = X ◁ p ≫ q := by
    rw [hl]
    exact MonoidalClosed.uncurry_natural_left p r
  change (j ⊗ₘ 𝟙 X) ≫ (β_ S X).hom ≫ MonoidalClosed.uncurry l = _
  rw [hu]
  have hb := BraidedCategory.braiding_naturality_assoc j (𝟙 X) (X ◁ p ≫ q)
  rw [hb]
  simp only [id_tensorHom]
  rw [← whiskerLeft_comp_assoc, hm]
  have hc := AssociatorRightContraction.leftSlice_action F (G.externalTensor H) e a b
    (𝟙 (G.obj a.1 ⊗ H.obj a.2))
  change (i ⊗ₘ (𝟙 (F.obj e) ⊗ₘ 𝟙 (G.obj a.1 ⊗ H.obj a.2))) ≫
      (β_ S' X).hom ≫ q =
    (AssociatorRightContraction.frontHomIso R (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      F.obj e ◁ (R ◁ 𝟙 (G.obj a.1 ⊗ H.obj a.2) ≫
        (β_ R (G.obj a.1 ⊗ H.obj a.2)).hom ≫
          MonoidalClosed.uncurry ((G.externalTensor H).map a b)) at hc
  simp only [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hc
  have hn := BraidedCategory.braiding_naturality_assoc i (𝟙 X) q
  have hn' : (i ⊗ₘ 𝟙 X) ≫ (β_ S' X).hom ≫ q = (β_ R X).hom ≫ X ◁ i ≫ q := by
    simpa only [id_tensorHom] using hn
  exact hn'.symm.trans hc
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_face0 {K R S P Wa Wb : V}
    (f : S ⊗ P ⟶ R) (ka : K ⊗ R ⟶ Wa) (kb : K ⊗ S ⟶ Wb)
    (v : Wb ⊗ P ⟶ Wa)
    (h : (α_ K S P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v = K ◁ f ≫ ka)
    (B A : V) :
    K ◁ (B ◁ ((α_ S P A).inv ≫ (f ⊗ₘ 𝟙 A))) ≫ frontMap ka B A =
      frontRelationMap kb B P A ≫ (α_ Wb P (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A)) := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [frontMap_naturality_hom]
  rw [← h]
  simpa only [frontRelationMap, frontMap, Category.assoc] using
    frontMap_composition kb v B A

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_face1 {K R W P A A' : V} (k : K ⊗ R ⟶ W)
    (a : P ⊗ A ⟶ A') (B : V) :
    K ◁ (B ◁ (R ◁ a)) ≫ frontMap k B A' =
      frontRelationMap k B P A ≫
        W ◁ ((frontHomIso P B A).inv ≫ B ◁ a) := by
  rw [frontMap_naturality_coefficient]
  simp only [frontRelationMap, whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv_assoc]
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The full inner weight face contracts by genuine enriched composition on the first slice. -/
@[reassoc]
theorem sliceBase_inner (p a b : I × I) :
    (weight d.tensorEnrichedFunctor m).obj (op p) ◁
        MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor p.2).map (op b) (op a)) ≫
      sliceBase d m p a =
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op p))
        (d.tensorEnrichedFunctor.obj b ⟶[V] p.2) (a ⟶[V] b)).inv ≫
      (sliceBase d m p b ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      ((AssociatorIndex.rightWeight d m).obj
          (op ((AssociatorRightTensor.innerInclusion (V := V) p.1).obj b)) ◁
        (AssociatorRightTensor.innerInclusion (V := V) p.1).map a b ≫
        MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
          (op ((AssociatorRightTensor.innerInclusion (V := V) p.1).obj b))
          (op ((AssociatorRightTensor.innerInclusion (V := V) p.1).obj a)))) := by
  let W := weight d.tensorEnrichedFunctor m
  let e := p.1
  let x := d.tensorEnrichedFunctor.obj a
  let y := d.tensorEnrichedFunctor.obj b
  let k := p.2
  let J := EnrichedFunctor.prodRightInclusion (V := V) (B := I) e
  let U := W.obj (op p)
  let Wa := W.obj (op (e, x))
  let Wb := W.obj (op (e, y))
  let P : V := a ⟶[V] b
  let R : V := y ⟶[V] k
  let S : V := x ⟶[V] k
  let t : P ⟶ (x ⟶[V] y) := d.tensorEnrichedFunctor.map a b
  let f : R ⟶ ((e, y) ⟶[V] p) := J.map y k
  let g : P ⟶ ((e, x) ⟶[V] (e, y)) := t ≫ J.map x y
  let j : S ⟶ ((e, x) ⟶[V] p) := J.map x k
  let wa : U ⊗ ((e, x) ⟶[V] p) ⟶ Wa := MonoidalClosed.uncurry (W.map (op p) (op (e, x)))
  let wb : U ⊗ ((e, y) ⟶[V] p) ⟶ Wb := MonoidalClosed.uncurry (W.map (op p) (op (e, y)))
  let w : Wb ⊗ ((e, x) ⟶[V] (e, y)) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op (e, y)) (op (e, x)))
  let ka : U ⊗ S ⟶ Wa := sliceBase d m p a
  let kb : U ⊗ R ⟶ Wb := sliceBase d m p b
  let v : Wb ⊗ P ⟶ Wa := (AssociatorIndex.rightWeight d m).obj
      (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj b)) ◁
      (AssociatorRightTensor.innerInclusion (V := V) e).map a b ≫
      MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
        (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj b))
        (op ((AssociatorRightTensor.innerInclusion (V := V) e).obj a)))
  let tau : R ⊗ P ⟶ S :=
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor k).map (op b) (op a))
  have htau : tau = R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k :=
    weight_uncurry_map d.tensorEnrichedFunctor k a b
  let c : R ⊗ P ⟶ ((e, x) ⟶[V] p) :=
    (f ⊗ₘ g) ≫ (β_ ((e, y) ⟶[V] p) ((e, x) ⟶[V] (e, y))).hom ≫
      eComp V (e, x) (e, y) p
  have hc : c = tau ≫ j := by
    have h := AssociatorInclusion.leftInclusion_precomposition e x y k t
    change c = R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k ≫ j at h
    have h' : c = (R ◁ t ≫ (β_ R (x ⟶[V] y)).hom ≫ eComp V x y k) ≫ j := by
      simpa only [Category.assoc] using h
    exact h'.trans (congrArg (fun z => z ≫ j) htau.symm)
  have hv : v = Wb ◁ g ≫ w := innerInclusion_weight_action d m e a b
  have hl : (α_ U R P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v =
      (α_ U R P).inv ≫ (kb ⊗ₘ g) ≫ w := by
    rw [hv]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  have hcomp := AssociatorContraction.weightAction_comp_maps W (e, x) (e, y) p f g
  change (α_ U R P).inv ≫ (kb ⊗ₘ g) ≫ w = U ◁ c ≫ wa at hcomp
  rw [hc] at hcomp
  have hr : U ◁ (tau ≫ j) ≫ wa = U ◁ tau ≫ ka := by
    change U ◁ (tau ≫ j) ≫ wa = U ◁ tau ≫ (U ◁ j ≫ wa)
    simp only [whiskerLeft_comp, Category.assoc]
  change U ◁ tau ≫ ka = (α_ U R P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v
  exact (hl.trans (hcomp.trans hr)).symm

variable [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]

/-- Both original right inner relation faces balance after the genuine flat contraction. -/
@[reassoc]
theorem inner_balanced (p a b : I × I) :
    AssociatorFaces.Right.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p a b ≫
      contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) =
    AssociatorFaces.Right.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p a b ≫
      contractWord d F G H m p b ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p b) := by
  let J := AssociatorRightTensor.innerInclusion (V := V) (C := I) (D := I) (E := I) p.1
  let W := AssociatorIndex.rightWeight d m
  let Q := Associator.rightCoefficients F G H
  let U := (weight d.tensorEnrichedFunctor m).obj (op p)
  let B := F.obj p.1
  let Aa := G.obj a.1 ⊗ H.obj a.2
  let Ab := G.obj b.1 ⊗ H.obj b.2
  let P : V := a ⟶[V] b
  let Ra : V := d.tensorEnrichedFunctor.obj a ⟶[V] p.2
  let Rb : V := d.tensorEnrichedFunctor.obj b ⟶[V] p.2
  let Wa := W.obj (op (J.obj a))
  let Wb := W.obj (op (J.obj b))
  let ka : U ⊗ Ra ⟶ Wa := sliceBase d m p a
  let kb : U ⊗ Rb ⟶ Wb := sliceBase d m p b
  let f : Rb ⊗ P ⟶ Ra := MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor p.2).map (op b) (op
    a))
  let c : P ⊗ Aa ⟶ Ab := (β_ P Aa).hom ≫ MonoidalClosed.uncurry ((G.externalTensor H).map a b)
  let v : Wb ⊗ P ⟶ Wa := Wb ◁ J.map a b ≫ MonoidalClosed.uncurry (W.map (op (J.obj b)) (op (J.obj
    a)))
  let q : P ⊗ (B ⊗ Aa) ⟶ B ⊗ Ab :=
    (J.map a b ⊗ₘ 𝟙 (B ⊗ Aa)) ≫ (β_ (J.obj a ⟶[V] J.obj b) (B ⊗ Aa)).hom ≫
      MonoidalClosed.uncurry (Q.map (J.obj a) (J.obj b))
  let ga : Wa ⊗ (B ⊗ Aa) ⟶ AssociatorFlat.rightPoint d F G H m := AssociatorFlat.rightGenerator d F
    G H m (flatIndex p a)
  let gb : Wb ⊗ (B ⊗ Ab) ⟶ AssociatorFlat.rightPoint d F G H m := AssociatorFlat.rightGenerator d F
    G H m (flatIndex p b)
  let l : Wb ⊗ (P ⊗ (B ⊗ Aa)) ⟶ Wa ⊗ (B ⊗ Aa) := (α_ Wb P (B ⊗ Aa)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ Aa))
  let r : Wb ⊗ (P ⊗ (B ⊗ Aa)) ⟶ Wb ⊗ (B ⊗ Ab) := Wb ◁ q
  let pre := AssociatorRightContraction.frontRelationMap kb B P Aa
  have hweight : (α_ U Rb P).inv ≫ (kb ⊗ₘ 𝟙 P) ≫ v = U ◁ f ≫ ka :=
    (sliceBase_inner d m p a b).symm
  have hq : q = (AssociatorRightContraction.frontHomIso P B Aa).inv ≫ B ◁ c :=
    innerInclusion_coefficient_action F G H p.1 a b
  have h0 := AssociatorRightContraction.frontMap_face0 f ka kb v hweight B Aa
  have h1 := AssociatorRightContraction.frontMap_face1 kb c B
  have hc := AssociatorRightContraction.index_condition J W Q a b
  change (α_ Wb P (B ⊗ Aa)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ Aa)) ≫ ga = r ≫ gb at hc
  have hc' : l ≫ ga = r ≫ gb := by simpa only [l, Category.assoc] using hc
  change U ◁ (B ◁ ((α_ Rb P Aa).inv ≫ (f ⊗ₘ 𝟙 Aa))) ≫
      AssociatorRightContraction.frontMap ka B Aa = pre ≫ l at h0
  have h1' : U ◁ (B ◁ (Rb ◁ c)) ≫ AssociatorRightContraction.frontMap kb B Ab = pre ≫ r := by
    change _ = pre ≫ Wb ◁ q
    rw [hq]
    exact h1
  change (U ◁ (B ◁ ((α_ Rb P Aa).inv ≫ (f ⊗ₘ 𝟙 Aa)))) ≫
      AssociatorRightContraction.frontMap ka B Aa ≫ ga =
    U ◁ (B ◁ (Rb ◁ c)) ≫ AssociatorRightContraction.frontMap kb B Ab ≫ gb
  have h0' := congrArg (fun z => z ≫ ga) h0
  have h1'' := congrArg (fun z => z ≫ gb) h1'
  have hb := congrArg (fun z => pre ≫ z) hc'
  simp only [Category.assoc] at h0' h1'' hb
  simpa only [AssociatorRightContraction.frontMap, Category.assoc] using
    h0'.trans (hb.trans h1''.symm)
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

omit [MonoidalClosed V] in
private theorem frontMap_unit_pure (K B A : V) :
    K ◁ (B ◁ (λ_ A).inv) ≫ frontMap (ρ_ K).hom B A = 𝟙 (K ⊗ (B ⊗ A)) := by
  simp only [frontMap, frontHomIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, braiding_tensorUnit_right, tensorHom_def, Category.assoc]
  monoidal

omit [MonoidalClosed V] in
/-- Inserting the actual inner identity contracts the complete right tensor word. -/
@[reassoc]
theorem frontMap_identity {K R : V} (i : 𝟙_ V ⟶ R) (k : K ⊗ R ⟶ K)
    (hk : (ρ_ K).inv ≫ (𝟙 K ⊗ₘ i) ≫ k = 𝟙 K) (B A : V) :
    K ◁ (B ◁ ((λ_ A).inv ≫ (i ⊗ₘ 𝟙 A))) ≫ frontMap k B A = 𝟙 (K ⊗ (B ⊗ A)) := by
  have hi : K ◁ i ≫ k = (ρ_ K).hom := by
    apply (cancel_epi (ρ_ K).inv).1
    simpa only [id_tensorHom, Category.assoc, Iso.inv_hom_id] using hk
  simp only [whiskerLeft_comp, Category.assoc]
  rw [frontMap_naturality_hom, hi]
  exact frontMap_unit_pure K B A
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- The fixed first slice sends the original enriched inner identity to the original outer identity.
-/
@[reassoc]
theorem sliceBase_identity (e : I) (a : I × I) :
    (ρ_ ((weight d.tensorEnrichedFunctor m).obj (op (e, d.tensorEnrichedFunctor.obj a)))).inv ≫
      (𝟙 ((weight d.tensorEnrichedFunctor m).obj (op (e, d.tensorEnrichedFunctor.obj a))) ⊗ₘ
        eId V (d.tensorEnrichedFunctor.obj a)) ≫
      sliceBase d m (e, d.tensorEnrichedFunctor.obj a) a =
    𝟙 ((weight d.tensorEnrichedFunctor m).obj (op (e, d.tensorEnrichedFunctor.obj a))) := by
  let x := d.tensorEnrichedFunctor.obj a
  let p : I × I := (e, x)
  let W := weight d.tensorEnrichedFunctor m
  let U := W.obj (op p)
  let j : (x ⟶[V] x) ⟶ (p ⟶[V] p) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map x x
  let w : U ⊗ (p ⟶[V] p) ⟶ U := MonoidalClosed.uncurry (W.map (op p) (op p))
  have hj : eId V x ≫ j = eId V p :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) e).map_id x
  have hi := AssociatorRightContraction.action_identity W (op p)
  change (ρ_ U).inv ≫ (𝟙 U ⊗ₘ eId V p) ≫ w = 𝟙 U at hi
  change (ρ_ U).inv ≫ (𝟙 U ⊗ₘ eId V x) ≫ (U ◁ j ≫ w) = 𝟙 U
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [hj]
  exact hi

/-- Insert the actual inner identity into the original right nested word at its original index. -/
abbrev identityWord (X : (I × I) × I) :
    AssociatorFlat.rightObjects d F G H m X ⟶
      AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        (X.1.1, X.1.2 ⊗ X.2) (X.1.2, X.2) :=
  ((weight d.tensorEnrichedFunctor m).obj (op (X.1.1, X.1.2 ⊗ X.2))) ◁
    (F.obj X.1.1 ◁ AssociatorUnit.identityInsert (X.1.2 ⊗ X.2) (G.obj X.1.2 ⊗ H.obj X.2))

/-- Original identity insertion followed by original right contraction is the full identity. -/
@[reassoc]
theorem identityWord_contractWord (X : (I × I) × I) :
    identityWord d F G H m X ≫
      contractWord d F G H m (X.1.1, X.1.2 ⊗ X.2) (X.1.2, X.2) =
    𝟙 (AssociatorFlat.rightObjects d F G H m X) := by
  let a : I × I := (X.1.2, X.2)
  let x := d.tensorEnrichedFunctor.obj a
  let p : I × I := (X.1.1, x)
  let U := (weight d.tensorEnrichedFunctor m).obj (op p)
  let B := F.obj X.1.1
  let A := G.obj X.1.2 ⊗ H.obj X.2
  let k : U ⊗ (x ⟶[V] x) ⟶ U := sliceBase d m p a
  change U ◁ (B ◁ AssociatorUnit.identityInsert x A) ≫
    AssociatorRightContraction.frontMap k B A = 𝟙 (U ⊗ (B ⊗ A))
  exact AssociatorRightContraction.frontMap_identity (eId V x) k
    (sliceBase_identity d m X.1.1 a) B A

variable [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)]

/-- The actual right flattening generator is exactly the original nested generator with identity
  insertion. -/
@[reassoc]
theorem rightGenerator_flatToNested_identity (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ flatToNested d F G H m =
      identityWord d F G H m X ≫
        AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
          m
          (X.1.1, X.1.2 ⊗ X.2) (X.1.2, X.2) := by
  rw [rightGenerator_flatToNested]
  let p : I × I := (X.1.1, X.1.2 ⊗ X.2)
  let a : I × I := (X.1.2, X.2)
  let U := (weight d.tensorEnrichedFunctor m).obj (op p)
  let B := F.obj X.1.1
  let A := G.obj X.1.2 ⊗ H.obj X.2
  let i : A ⟶ (d.tensorEnrichedFunctor.obj a ⟶[V] d.tensorEnrichedFunctor.obj a) ⊗ A :=
    AssociatorUnit.identityInsert (d.tensorEnrichedFunctor.obj a) A
  let x := d.tensorEnrichedFunctor.obj a
  let Y := EnrichedDayKernel.obj d.tensorEnrichedFunctor G H x
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
    H) m
  let g : (x ⟶[V] x) ⊗ A ⟶ Y := EnrichedDayKernel.gen d.tensorEnrichedFunctor G H x a
  let h : U ⊗ (B ⊗ Y) ⟶ N :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m p
  change (𝟙 U ⊗ₘ (𝟙 B ⊗ₘ (i ≫ g))) ≫ h = U ◁ (B ◁ i) ≫ (U ◁ (B ◁ g) ≫ h)
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightTensor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
attribute [local instance] Enriched.prodCategory

/-- Insert the actual fixed last two inputs into the unchanged original right flat index. -/
abbrev outerInclusion (a : D × E) : EnrichedFunctor V C ((C × D) × E) :=
  (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) a).comp V
    (productAssociatorInv (V := V) (C := C) (D := D) (E := E))

@[simp]
theorem outerInclusion_obj (a : D × E) (e : C) :
    (outerInclusion (V := V) (C := C) a).obj e = ((e, a.1), a.2) := rfl

/-- The entire input Hom is inserted with the actual product identity of the last two inputs. -/
theorem outerInclusion_map (a : D × E) (e f : C) :
    (outerInclusion (V := V) (C := C) a).map e f =
      (ρ_ (e ⟶[V] f)).inv ≫ (𝟙 (e ⟶[V] f) ⊗ₘ eId V a) ≫
        (α_ (e ⟶[V] f) (a.1 ⟶[V] a.1) (a.2 ⟶[V] a.2)).inv := by
  change ((ρ_ (e ⟶[V] f)).inv ≫ (𝟙 (e ⟶[V] f) ⊗ₘ eId V a)) ≫ _ = _
  exact Category.assoc _ _ _

@[reassoc]
theorem outerInclusion_product_map (a : D × E) (e f : C) :
    (outerInclusion (V := V) (C := C) a).map e f ≫
        (Associator.productAssociator (V := V) (A := C) (B := D) (C := E)).map
          ((outerInclusion (V := V) (C := C) a).obj e)
          ((outerInclusion (V := V) (C := C) a).obj f) =
      (EnrichedFunctor.prodLeftInclusion (V := V) (A := C) a).map e f := by
  change (((ρ_ (e ⟶[V] f)).inv ≫ (𝟙 (e ⟶[V] f) ⊗ₘ eId V a)) ≫
      (α_ (e ⟶[V] f) (a.1 ⟶[V] a.1) (a.2 ⟶[V] a.2)).inv) ≫
      (α_ (e ⟶[V] f) (a.1 ⟶[V] a.1) (a.2 ⟶[V] a.2)).hom =
    (ρ_ (e ⟶[V] f)).inv ≫ (𝟙 (e ⟶[V] f) ⊗ₘ eId V a)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end CategoryTheory.EnrichedDayKernel.AssociatorRightTensor


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontHomIso_naturality_first (R : V) {B B' : V} (b : B ⟶ B') (A : V) :
    (b ⊗ₘ 𝟙 (R ⊗ A)) ≫ (frontHomIso R B' A).hom =
      (frontHomIso R B A).hom ≫ R ◁ (b ⊗ₘ 𝟙 A) := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [← id_tensorHom_id R A, associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  rw [BraidedCategory.braiding_naturality b (𝟙 R)]
  rw [← tensorHom_comp_tensorHom_assoc, associator_naturality]
  simp only [id_tensorHom]

omit [MonoidalClosed V] in
@[reassoc]
theorem frontMap_naturality_first {K R W B B' : V} (k : K ⊗ R ⟶ W)
    (b : B ⟶ B') (A : V) :
    K ◁ (b ⊗ₘ 𝟙 (R ⊗ A)) ≫ frontMap k B' A =
      frontMap k B A ≫ W ◁ (b ⊗ₘ 𝟙 A) := by
  simp only [frontMap]
  rw [← whiskerLeft_comp_assoc, frontHomIso_naturality_first]
  simp only [tensorHom_id, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange]

omit [MonoidalClosed V] in
/-- The full inner output action retains its original Hom composition and coefficient identity. -/
@[reassoc]
theorem outputAction_tensor {C : Type uC} [EnrichedCategory V C] (x k k' : C) (A : V) :
    Output.outputAction x k k' A =
      (α_ (k ⟶[V] k') (x ⟶[V] k) A).inv ≫
        (((β_ (k ⟶[V] k') (x ⟶[V] k)).hom ≫ eComp V x k k') ⊗ₘ 𝟙 A) := by
  simp only [Output.outputAction, tensorHom_comp_tensorHom, Category.comp_id]
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] in
/-- The original right index action contracts the actual identity of the last two inputs. -/
@[reassoc]
theorem outerInclusion_index_map (a : I × I) (e f : I) :
    (AssociatorRightTensor.outerInclusion (V := V) (C := I) a).map e f ≫
      (AssociatorIndex.rightIndex d).map
        ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj e)
        ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj f) =
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) (d.tensorEnrichedFunctor.obj a)).map e f ≫
      d.tensorEnrichedFunctor.map (e, d.tensorEnrichedFunctor.obj a) (f, d.tensorEnrichedFunctor.obj
        a) := by
  let R : V := e ⟶[V] f
  let P : V := a ⟶[V] a
  let x := d.tensorEnrichedFunctor.obj a
  let Q : V := x ⟶[V] x
  let r := α_ R (a.1 ⟶[V] a.1) (a.2 ⟶[V] a.2)
  let i : 𝟙_ V ⟶ P := eId V a
  let t : P ⟶ Q := d.tensorEnrichedFunctor.map a a
  let j : 𝟙_ V ⟶ Q := eId V x
  let u : R ⊗ Q ⟶ (d.tensorEnrichedFunctor.obj (e, x) ⟶[V] d.tensorEnrichedFunctor.obj (f, x)) :=
    d.tensorEnrichedFunctor.map (e, x) (f, x)
  change (((ρ_ R).inv ≫ (𝟙 R ⊗ₘ i)) ≫ r.inv) ≫ (r.hom ≫ R ◁ t ≫ u) =
    ((ρ_ R).inv ≫ (𝟙 R ⊗ₘ j)) ≫ u
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← id_tensorHom R t, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]
  have ht : i ≫ t = j := d.tensorEnrichedFunctor.map_id a
  rw [ht]

/-- The original right flat weight action agrees with the complete fixed-inner-index slice. -/
@[reassoc]
theorem outerInclusion_weight_action (a : I × I) (e f : I) :
    (AssociatorIndex.rightWeight d m).obj
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj f)) ◁
        (AssociatorRightTensor.outerInclusion (V := V) (C := I) a).map e f ≫
      MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj f))
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj e))) =
    (weight d.tensorEnrichedFunctor m).obj (op (f, d.tensorEnrichedFunctor.obj a)) ◁
        (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) (d.tensorEnrichedFunctor.obj a)).map e
          f ≫
      MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map
        (op (f, d.tensorEnrichedFunctor.obj a)) (op (e, d.tensorEnrichedFunctor.obj a))) := by
  let J := AssociatorRightTensor.outerInclusion (V := V) (C := I) a
  let Xe := J.obj e
  let Xf := J.obj f
  let x := d.tensorEnrichedFunctor.obj a
  let s : I := d.tensorEnrichedFunctor.obj (e, x)
  let t : I := d.tensorEnrichedFunctor.obj (f, x)
  let U : V := t ⟶[V] m
  let R : V := s ⟶[V] t
  let j : (e ⟶[V] f) ⟶ (Xe ⟶[V] Xf) := J.map e f
  let l : (Xe ⟶[V] Xf) ⟶ R := (AssociatorIndex.rightIndex d).map Xe Xf
  let k : (e ⟶[V] f) ⟶ ((e, x) ⟶[V] (f, x)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) x).map e f
  let u : ((e, x) ⟶[V] (f, x)) ⟶ R := d.tensorEnrichedFunctor.map (e, x) (f, x)
  have hm : j ≫ l = k ≫ u := outerInclusion_index_map d a e f
  let wl : U ⊗ (Xe ⟶[V] Xf) ⟶ (s ⟶[V] m) :=
    MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map (op Xf) (op Xe))
  let wr : U ⊗ ((e, x) ⟶[V] (f, x)) ⟶ (s ⟶[V] m) :=
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map (op (f, x)) (op (e, x)))
  have hl : wl = U ◁ l ≫ (β_ U R).hom ≫ eComp V s t m :=
    weight_uncurry_map (AssociatorIndex.rightIndex d) m Xe Xf
  have hr : wr = U ◁ u ≫ (β_ U R).hom ≫ eComp V s t m :=
    weight_uncurry_map d.tensorEnrichedFunctor m (e, x) (f, x)
  change U ◁ j ≫ wl = U ◁ k ≫ wr
  rw [hl, hr, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hm]

omit [MonoidalCategory I] in
/-- The original right flat coefficient retains the full first-input action and the last two
  identities. -/
@[reassoc]
theorem outerInclusion_coefficient_action (a : I × I) (e f : I) :
    ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).map e f ⊗ₘ
        𝟙 (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))) ≫
      (β_ (((e, a.1), a.2) ⟶[V] ((f, a.1), a.2))
        (F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2))).hom ≫
      MonoidalClosed.uncurry ((Associator.rightCoefficients F G H).map ((e, a.1), a.2) ((f, a.1),
        a.2)) =
    (α_ (e ⟶[V] f) (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      (((β_ (e ⟶[V] f) (F.obj e)).hom ≫ MonoidalClosed.uncurry (F.map e f)) ⊗ₘ
        𝟙 (G.obj a.1 ⊗ H.obj a.2)) := by
  let J := AssociatorRightTensor.outerInclusion (V := V) (C := I) a
  let P := Associator.productAssociator (V := V) (A := I) (B := I) (C := I)
  let Q := F.externalTensor (G.externalTensor H)
  let R : V := e ⟶[V] f
  let S : V := J.obj e ⟶[V] J.obj f
  let S' : V := (e, a) ⟶[V] (f, a)
  let X := F.obj e ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let Y := F.obj f ⊗ (G.obj a.1 ⊗ H.obj a.2)
  let j : R ⟶ S := J.map e f
  let p : S ⟶ S' := P.map (J.obj e) (J.obj f)
  let i : R ⟶ S' := (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) a).map e f
  let r : S' ⟶ (ihom X).obj Y := Q.map (e, a) (f, a)
  let l : S ⟶ (ihom X).obj Y := (Associator.rightCoefficients F G H).map
    ((e, a.1), a.2) ((f, a.1), a.2)
  let q : X ⊗ S' ⟶ Y := MonoidalClosed.uncurry r
  have hm : j ≫ p = i := AssociatorRightTensor.outerInclusion_product_map a e f
  have hl : l = p ≫ r := rfl
  have hu : MonoidalClosed.uncurry l = X ◁ p ≫ q := by
    rw [hl]
    exact MonoidalClosed.uncurry_natural_left p r
  change (j ⊗ₘ 𝟙 X) ≫ (β_ S X).hom ≫ MonoidalClosed.uncurry l = _
  rw [hu]
  have hb := BraidedCategory.braiding_naturality_assoc j (𝟙 X) (X ◁ p ≫ q)
  rw [hb]
  simp only [id_tensorHom]
  rw [← whiskerLeft_comp_assoc, hm]
  have hc := AssociatorContraction.rightSlice_action F (G.externalTensor H) a e f (𝟙 (F.obj e))
  change (i ⊗ₘ (𝟙 (F.obj e) ⊗ₘ 𝟙 (G.obj a.1 ⊗ H.obj a.2))) ≫ (β_ S' X).hom ≫ q =
    (α_ R (F.obj e) (G.obj a.1 ⊗ H.obj a.2)).inv ≫
      ((R ◁ 𝟙 (F.obj e) ≫ (β_ R (F.obj e)).hom ≫ MonoidalClosed.uncurry (F.map e f)) ⊗ₘ
        𝟙 (G.obj a.1 ⊗ H.obj a.2)) at hc
  simp only [id_tensorHom_id, whiskerLeft_id, Category.id_comp] at hc
  have hn := BraidedCategory.braiding_naturality_assoc i (𝟙 X) q
  have hn' : (i ⊗ₘ 𝟙 X) ≫ (β_ S' X).hom ≫ q = (β_ R X).hom ≫ X ◁ i ≫ q := by
    simpa only [id_tensorHom] using hn
  exact hn'.symm.trans hc
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
/-- The original opposite weight braid cancels the coefficient braid on the full product Hom. -/
@[reassoc]
theorem productWeightWord (E S R : V) :
    (β_ (E ⊗ S) R).hom ≫ (frontHomIso R E S).inv =
      (α_ E S R).hom ≫ E ◁ (β_ S R).hom := by
  simp only [BraidedCategory.braiding_tensor_left_hom, frontHomIso,
    Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv, tensorHom_id,
    Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  simp only [Iso.inv_hom_id, Category.comp_id]

omit [MonoidalClosed V] in
/-- The actual outer weight face contracts both complete weight factors in their original order. -/
@[reassoc]
theorem frontMap_outerWeight {U P K R W : V} (w : U ⊗ P ⟶ K) (k : K ⊗ R ⟶ W)
    (B A : V) :
    (α_ U P (B ⊗ (R ⊗ A))).inv ≫ (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A))) ≫ frontMap k B A =
      U ◁ (frontHomIso P B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ P R A).inv) ≫
        frontMap ((α_ U P R).inv ≫ (w ⊗ₘ 𝟙 R) ≫ k) B A := by
  have h := frontMap_composition w k B A
  have hp := congrArg (fun z => U ◁ (frontHomIso P B (R ⊗ A)).inv ≫ z) h
  simp only [frontRelationMap, frontMap, Category.assoc,
    whiskerLeft_inv_hom_assoc] at hp
  simpa only [frontMap, Category.assoc] using hp.symm

omit [MonoidalClosed V] in
/-- The full original outer relation word before its first coefficient action. -/
abbrev outerRelationMap {U S R R' W : V} (k : U ⊗ R' ⟶ W) (h : S ⊗ R ⟶ R')
    (E B A : V) : U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A))) ⟶ W ⊗ (E ⊗ (B ⊗ A)) :=
  U ◁ tensorμ E S B (R ⊗ A) ≫ U ◁ ((E ⊗ B) ◁ (α_ S R A).inv) ≫
    frontMap (U ◁ h ≫ k) (E ⊗ B) A ≫ W ◁ (α_ E B A).hom

omit [MonoidalClosed V] in
/-- Original coefficient and inner output actions retain the full unacted first-input Hom. -/
@[reassoc]
theorem frontMap_outerCoefficient {U E S R R' W B B' A : V}
    (k : U ⊗ R' ⟶ W) (h : S ⊗ R ⟶ R') (b : E ⊗ B ⟶ B') :
    U ◁ (tensorμ E S B (R ⊗ A) ≫
        (b ⊗ₘ ((α_ S R A).inv ≫ (h ⊗ₘ 𝟙 A)))) ≫ frontMap k B' A =
      outerRelationMap k h E B A ≫ W ◁ ((α_ E B A).inv ≫ (b ⊗ₘ 𝟙 A)) := by
  let X := E ⊗ B
  have ht : b ⊗ₘ ((α_ S R A).inv ≫ (h ⊗ₘ 𝟙 A)) =
      X ◁ (α_ S R A).inv ≫ X ◁ (h ⊗ₘ 𝟙 A) ≫ (b ⊗ₘ 𝟙 (R' ⊗ A)) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [ht]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [frontMap_naturality_first]
  have hn := frontMap_naturality_hom h k X A
  have hn' := congrArg (fun z => U ◁ tensorμ E S B (R ⊗ A) ≫
      U ◁ (X ◁ (α_ S R A).inv) ≫ z ≫ W ◁ (b ⊗ₘ 𝟙 A)) hn
  simpa only [outerRelationMap, frontMap, whiskerLeft_comp, Category.assoc,
    whiskerLeft_hom_inv_assoc] using hn'
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory

/-- Both original right outer Hom factors contract the inner weight before their unchanged first
  Hom. -/
abbrev outerInputBase (p q a : I × I) :
    (p ⟶[V] q) ⊗ (d.tensorEnrichedFunctor.obj a ⟶[V] p.2) ⟶
      (d.tensorEnrichedFunctor.obj a ⟶[V] q.2) ⊗ (p.1 ⟶[V] q.1) :=
  (α_ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)).hom ≫
    (p.1 ⟶[V] q.1) ◁ ((β_ (p.2 ⟶[V] q.2) (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)).hom ≫
      eComp V (d.tensorEnrichedFunctor.obj a) p.2 q.2) ≫
    (β_ (p.1 ⟶[V] q.1) (d.tensorEnrichedFunctor.obj a ⟶[V] q.2)).hom

/-- The full original right outer weight action agrees with the full original flat first-input
  relation. -/
@[reassoc]
theorem sliceBase_outer (p q a : I × I) :
    (α_ ((weight d.tensorEnrichedFunctor m).obj (op q)) (p ⟶[V] q)
        (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)).inv ≫
      (MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map (op q) (op p)) ⊗ₘ
        𝟙 (d.tensorEnrichedFunctor.obj a ⟶[V] p.2)) ≫ sliceBase d m p a =
    (weight d.tensorEnrichedFunctor m).obj (op q) ◁ outerInputBase d p q a ≫
      (α_ ((weight d.tensorEnrichedFunctor m).obj (op q))
        (d.tensorEnrichedFunctor.obj a ⟶[V] q.2) (p.1 ⟶[V] q.1)).inv ≫
      (sliceBase d m q a ⊗ₘ 𝟙 (p.1 ⟶[V] q.1)) ≫
      ((AssociatorIndex.rightWeight d m).obj
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj q.1)) ◁
        (AssociatorRightTensor.outerInclusion (V := V) (C := I) a).map p.1 q.1 ≫
        MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj q.1))
          (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj p.1)))) := by
  let W := weight d.tensorEnrichedFunctor m
  let x := d.tensorEnrichedFunctor.obj a
  let U := W.obj (op q)
  let Wp := W.obj (op p)
  let Wa := W.obj (op (p.1, x))
  let Wb := W.obj (op (q.1, x))
  let E : V := p.1 ⟶[V] q.1
  let S : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.2
  let R' : V := x ⟶[V] q.2
  let P : V := p ⟶[V] q
  let jp : R ⟶ ((p.1, x) ⟶[V] p) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) p.1).map x p.2
  let jq : R' ⟶ ((q.1, x) ⟶[V] q) :=
    (EnrichedFunctor.prodRightInclusion (V := V) (B := I) q.1).map x q.2
  let je : E ⟶ ((p.1, x) ⟶[V] (q.1, x)) :=
    (EnrichedFunctor.prodLeftInclusion (V := V) (A := I) x).map p.1 q.1
  let wp : U ⊗ P ⟶ Wp := MonoidalClosed.uncurry (W.map (op q) (op p))
  let wpa : Wp ⊗ ((p.1, x) ⟶[V] p) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op p) (op (p.1, x)))
  let wqa : U ⊗ ((p.1, x) ⟶[V] q) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op q) (op (p.1, x)))
  let wqb : U ⊗ ((q.1, x) ⟶[V] q) ⟶ Wb :=
    MonoidalClosed.uncurry (W.map (op q) (op (q.1, x)))
  let wba : Wb ⊗ ((p.1, x) ⟶[V] (q.1, x)) ⟶ Wa :=
    MonoidalClosed.uncurry (W.map (op (q.1, x)) (op (p.1, x)))
  let kp : Wp ⊗ R ⟶ Wa := sliceBase d m p a
  let kq : U ⊗ R' ⟶ Wb := sliceBase d m q a
  let v : Wb ⊗ E ⟶ Wa := (AssociatorIndex.rightWeight d m).obj
      (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj q.1)) ◁
      (AssociatorRightTensor.outerInclusion (V := V) (C := I) a).map p.1 q.1 ≫
      MonoidalClosed.uncurry ((AssociatorIndex.rightWeight d m).map
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj q.1))
        (op ((AssociatorRightTensor.outerInclusion (V := V) (C := I) a).obj p.1)))
  let h : S ⊗ R ⟶ R' := (β_ S R).hom ≫ eComp V x p.2 q.2
  let s : P ⊗ R ⟶ R' ⊗ E := outerInputBase d p q a
  change (α_ U P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp =
    U ◁ s ≫ (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v
  let c1 : P ⊗ R ⟶ E ⊗ R' := (α_ E S R).hom ≫ E ◁ h
  let c0 : P ⊗ R ⟶ ((p.1, x) ⟶[V] q) :=
    (𝟙 P ⊗ₘ jp) ≫ (β_ P ((p.1, x) ⟶[V] p)).hom ≫ eComp V (p.1, x) p q
  have hc0 : c0 = c1 := by
    have hf := AssociatorRightContraction.leftInclusion_full_comp (V := V) p.1 q.1 x p.2 q.2
    change (jp ⊗ₘ 𝟙 P) ≫ eComp V (p.1, x) p q =
      (AssociatorRightContraction.frontHomIso R E S).inv ≫ E ◁ eComp V x p.2 q.2 at hf
    have hn := BraidedCategory.braiding_naturality_assoc (𝟙 P) jp (eComp V (p.1, x) p q)
    change (𝟙 P ⊗ₘ jp) ≫ (β_ P ((p.1, x) ⟶[V] p)).hom ≫ eComp V (p.1, x) p q =
      (β_ P R).hom ≫ (jp ⊗ₘ 𝟙 P) ≫ eComp V (p.1, x) p q at hn
    change c0 = _ at hn
    rw [hf] at hn
    have hw := AssociatorRightContraction.productWeightWord E S R
    change (β_ P R).hom ≫ (AssociatorRightContraction.frontHomIso R E S).inv =
      (α_ E S R).hom ≫ E ◁ (β_ S R).hom at hw
    have hn' : c0 = ((β_ P R).hom ≫ (AssociatorRightContraction.frontHomIso R E S).inv) ≫
        E ◁ eComp V x p.2 q.2 := by simpa only [Category.assoc] using hn
    rw [hw] at hn'
    simpa only [c1, h, whiskerLeft_comp, Category.assoc] using hn'
  have h0 := AssociatorContraction.weightAction_comp_maps W (p.1, x) p q (𝟙 P) jp
  simp only [whiskerLeft_id, Category.id_comp] at h0
  change (α_ U P R).inv ≫ (wp ⊗ₘ jp) ≫ wpa = U ◁ c0 ≫ wqa at h0
  have h0' : (α_ U P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp = U ◁ c1 ≫ wqa := by
    rw [← hc0]
    change (α_ U P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ (Wp ◁ jp ≫ wpa) = U ◁ c0 ≫ wqa
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    simpa only [id_tensorHom] using h0
  have hv : v = Wb ◁ je ≫ wba := outerInclusion_weight_action d m a p.1 q.1
  let c2 : R' ⊗ E ⟶ ((p.1, x) ⟶[V] q) :=
    (jq ⊗ₘ je) ≫ (β_ ((q.1, x) ⟶[V] q) ((p.1, x) ⟶[V] (q.1, x))).hom ≫
      eComp V (p.1, x) (q.1, x) q
  have hc2 : c2 = (β_ R' E).hom := by
    have hn := BraidedCategory.braiding_naturality_assoc jq je (eComp V (p.1, x) (q.1, x) q)
    change c2 = (β_ R' E).hom ≫ (je ⊗ₘ jq) ≫ eComp V (p.1, x) (q.1, x) q at hn
    have hc := AssociatorContraction.rightThenLeft_comp (V := V) p.1 q.1 x q.2
    change (je ⊗ₘ jq) ≫ eComp V (p.1, x) (q.1, x) q = 𝟙 (E ⊗ R') at hc
    rw [hc, Category.comp_id] at hn
    exact hn
  have h1 := AssociatorContraction.weightAction_comp_maps W (p.1, x) (q.1, x) q jq je
  change (α_ U R' E).inv ≫ (kq ⊗ₘ je) ≫ wba = U ◁ c2 ≫ wqa at h1
  have h1' : (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v = U ◁ (β_ R' E).hom ≫ wqa := by
    rw [hv]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    rw [hc2] at h1
    simpa only [id_tensorHom] using h1
  have hs : s = c1 ≫ (β_ E R').hom := by
    change (α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom =
      ((α_ E S R).hom ≫ E ◁ h) ≫ (β_ E R').hom
    exact (Category.assoc _ _ _).symm
  have hh := congrArg (fun z => U ◁ s ≫ z) h1'
  have hc : U ◁ s ≫ U ◁ (β_ R' E).hom ≫ wqa = U ◁ c1 ≫ wqa := by
    rw [← whiskerLeft_comp_assoc, hs]
    simp only [Category.assoc, SymmetricCategory.symmetry, Category.comp_id]
  change (α_ U P R).inv ≫ (wp ⊗ₘ 𝟙 R) ≫ kp =
    U ◁ s ≫ (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v
  exact h0'.trans (hc.symm.trans hh.symm)
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
private theorem frontHomIso_tail (T B E : V) :
    (frontHomIso T B E).hom ≫ T ◁ (β_ B E).hom =
      (β_ B (T ⊗ E)).hom ≫ (α_ T E B).hom := by
  simp only [frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [BraidedCategory.braiding_tensor_right_hom B T E]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [MonoidalClosed V] in
@[reassoc]
private theorem frontHomIso_head (P B R : V) :
    (frontHomIso P B R).inv ≫ (β_ B (P ⊗ R)).hom =
      P ◁ (β_ B R).hom ≫ (α_ P R B).inv := by
  simp only [frontHomIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, tensorHom_id, Category.assoc]
  rw [BraidedCategory.braiding_tensor_right_hom B P R]
  simp only [Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]

omit [MonoidalClosed V] in
/-- Move an entire original coefficient block using the full ordinary braid naturality. -/
@[reassoc]
theorem frontBlock_word {P R E T : V} (a : P ⊗ R ⟶ E ⊗ T) (B : V) :
    (frontHomIso P B R).inv ≫ B ◁ a ≫ B ◁ (β_ E T).hom ≫
      (frontHomIso T B E).hom ≫ T ◁ (β_ B E).hom =
    P ◁ (β_ B R).hom ≫ (α_ P R B).inv ≫ a ▷ B ≫
      (β_ E T).hom ▷ B ≫ (α_ T E B).hom := by
  rw [frontHomIso_tail, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc, frontHomIso_head_assoc]

omit [MonoidalClosed V] in
@[reassoc]
private theorem tensorMu_common (E S B R : V) :
    tensorμ E S B R ≫ (β_ (E ⊗ B) (S ⊗ R)).hom =
      (E ⊗ S) ◁ (β_ B R).hom ≫ (α_ (E ⊗ S) R B).inv ≫
        (α_ E S R).hom ▷ B ≫ (β_ E (S ⊗ R)).hom ▷ B ≫ (α_ (S ⊗ R) E B).hom := by
  simp only [tensorμ]
  rw [BraidedCategory.braiding_tensor_left_hom E B (S ⊗ R),
    BraidedCategory.braiding_tensor_right_hom B S R]
  simp only [whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc]
  simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  monoidal

omit [MonoidalClosed V] in
/-- The actual four-factor permutation retaining both Hom blocks and both ordered coefficients. -/
@[reassoc]
theorem outerFourWord (E S B R : V) :
    tensorμ E S B R ≫ (β_ (E ⊗ B) (S ⊗ R)).hom =
      (frontHomIso (E ⊗ S) B R).inv ≫ B ◁ (α_ E S R).hom ≫
        B ◁ (β_ E (S ⊗ R)).hom ≫ (frontHomIso (S ⊗ R) B E).hom ≫
          (S ⊗ R) ◁ (β_ B E).hom := by
  exact (tensorMu_common E S B R).trans (frontBlock_word (α_ E S R).hom B).symm
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
private abbrev outerFrameSource (U E S B R A : V) :
    U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A))) ≅
      (U ⊗ ((E ⊗ S) ⊗ (B ⊗ R))) ⊗ A :=
  whiskerLeftIso U (whiskerLeftIso (E ⊗ S) (α_ B R A).symm ≪≫
    (α_ (E ⊗ S) (B ⊗ R) A).symm) ≪≫ (α_ U ((E ⊗ S) ⊗ (B ⊗ R)) A).symm

omit [MonoidalClosed V] in
private abbrev outerFrameTarget (U E S B R A : V) :
    (U ⊗ ((S ⊗ R) ⊗ (E ⊗ B))) ⊗ A ≅
      (U ⊗ (S ⊗ R)) ⊗ (E ⊗ (B ⊗ A)) :=
  whiskerRightIso (α_ U (S ⊗ R) (E ⊗ B)).symm A ≪≫
    α_ (U ⊗ (S ⊗ R)) (E ⊗ B) A ≪≫
      whiskerLeftIso (U ⊗ (S ⊗ R)) (α_ E B A)

omit [MonoidalClosed V] in
private abbrev outerWordTransport (U E S B R A : V)
    (f : (E ⊗ S) ⊗ (B ⊗ R) ⟶ (S ⊗ R) ⊗ (E ⊗ B)) :
    U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A))) ⟶
      (U ⊗ (S ⊗ R)) ⊗ (E ⊗ (B ⊗ A)) :=
  (outerFrameSource U E S B R A).hom ≫ (U ◁ f) ▷ A ≫
    (outerFrameTarget U E S B R A).hom

omit [MonoidalClosed V] in
private abbrev outerFrameLeft (U E S B R A : V) :
    U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A))) ⟶
      (U ⊗ (S ⊗ R)) ⊗ (E ⊗ (B ⊗ A)) :=
  U ◁ tensorμ E S B (R ⊗ A) ≫ U ◁ ((E ⊗ B) ◁ (α_ S R A).inv) ≫
    U ◁ (frontHomIso (S ⊗ R) (E ⊗ B) A).hom ≫
      (α_ U (S ⊗ R) ((E ⊗ B) ⊗ A)).inv ≫
        (U ⊗ (S ⊗ R)) ◁ (α_ E B A).hom

omit [MonoidalClosed V] in
private abbrev outerFrameRight (U E S B R A : V) :
    U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A))) ⟶
      (U ⊗ (S ⊗ R)) ⊗ (E ⊗ (B ⊗ A)) :=
  U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ (E ⊗ S) R A).inv) ≫
    U ◁ (B ◁ (((α_ E S R).hom ≫ (β_ E (S ⊗ R)).hom) ⊗ₘ 𝟙 A)) ≫
    U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫
    U ◁ (frontHomIso (S ⊗ R) B (E ⊗ A)).hom ≫
      (α_ U (S ⊗ R) (B ⊗ (E ⊗ A))).inv ≫
        (U ⊗ (S ⊗ R)) ◁ (frontHomIso E B A).hom

omit [MonoidalClosed V] in
private theorem outerFrameLeft_transport (U E S B R A : V) :
    outerFrameLeft U E S B R A =
      outerWordTransport U E S B R A (tensorμ E S B R ≫ (β_ (E ⊗ B) (S ⊗ R)).hom) := by
  simp only [outerFrameLeft, outerWordTransport, outerFrameSource, outerFrameTarget,
    frontHomIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, tensorμ, tensorHom_def,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

omit [MonoidalClosed V] in
private theorem outerFrameRight_transport (U E S B R A : V) :
    outerFrameRight U E S B R A =
      outerWordTransport U E S B R A
        ((frontHomIso (E ⊗ S) B R).inv ≫ B ◁ (α_ E S R).hom ≫
          B ◁ (β_ E (S ⊗ R)).hom ≫ (frontHomIso (S ⊗ R) B E).hom ≫
            (S ⊗ R) ◁ (β_ B E).hom) := by
  simp only [outerFrameRight, outerWordTransport, outerFrameSource, outerFrameTarget,
    frontHomIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
    whiskerLeftIso_hom, whiskerRightIso_hom, tensorHom_def,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

omit [MonoidalClosed V] in
private theorem outerFrame_eq (U E S B R A : V) :
    outerFrameLeft U E S B R A = outerFrameRight U E S B R A := by
  exact (outerFrameLeft_transport U E S B R A).trans
    ((congrArg (outerWordTransport U E S B R A) (outerFourWord E S B R)).trans
      (outerFrameRight_transport U E S B R A).symm)

omit [MonoidalClosed V] in
/-- The original full four-factor word comparison retains the entire outer parameter and
  coefficient. -/
@[reassoc]
theorem outerRelationMap_frame {U S R W : V} (k : U ⊗ (S ⊗ R) ⟶ W) (E B A : V) :
    U ◁ tensorμ E S B (R ⊗ A) ≫ U ◁ ((E ⊗ B) ◁ (α_ S R A).inv) ≫
      frontMap k (E ⊗ B) A ≫ W ◁ (α_ E B A).hom =
    U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ (E ⊗ S) R A).inv) ≫
      U ◁ (B ◁ (((α_ E S R).hom ≫ (β_ E (S ⊗ R)).hom) ⊗ₘ 𝟙 A)) ≫
      U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫ frontRelationMap k B E A := by
  have h := congrArg (fun z => z ≫ (k ⊗ₘ 𝟙 (E ⊗ (B ⊗ A)))) (outerFrame_eq U E S B R A)
  have hL : outerFrameLeft U E S B R A ≫ (k ⊗ₘ 𝟙 (E ⊗ (B ⊗ A))) =
      U ◁ tensorμ E S B (R ⊗ A) ≫ U ◁ ((E ⊗ B) ◁ (α_ S R A).inv) ≫
      frontMap k (E ⊗ B) A ≫ W ◁ (α_ E B A).hom := by
    simp only [outerFrameLeft, frontMap, tensorHom_id, Category.assoc]
    rw [whisker_exchange]
  have hR : outerFrameRight U E S B R A ≫ (k ⊗ₘ 𝟙 (E ⊗ (B ⊗ A))) =
      U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ (E ⊗ S) R A).inv) ≫
      U ◁ (B ◁ (((α_ E S R).hom ≫ (β_ E (S ⊗ R)).hom) ⊗ₘ 𝟙 A)) ≫
      U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫ frontRelationMap k B E A := by
    simp only [outerFrameRight, frontRelationMap, frontMap, tensorHom_id, Category.assoc]
    rw [whisker_exchange]
  exact hL.symm.trans (h.trans hR)
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightContraction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
/-- The complete outer relation contraction retains the full composed inner Hom map. -/
@[reassoc]
theorem outerRelationMap_contract {U S R R' W : V} (k : U ⊗ R' ⟶ W)
    (h : S ⊗ R ⟶ R') (E B A : V) :
    outerRelationMap k h E B A =
      U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ (E ⊗ S) R A).inv) ≫
      U ◁ (B ◁ (((α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom) ⊗ₘ 𝟙 A)) ≫
      U ◁ (B ◁ (α_ R' E A).hom) ≫ frontRelationMap k B E A := by
  let k0 : U ⊗ (S ⊗ R) ⟶ W := U ◁ h ≫ k
  let f0 : ((E ⊗ S) ⊗ R) ⟶ (S ⊗ R) ⊗ E :=
    (α_ E S R).hom ≫ (β_ E (S ⊗ R)).hom
  let f1 : ((E ⊗ S) ⊗ R) ⟶ R' ⊗ E :=
    (α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom
  let Z := U ⊗ ((E ⊗ S) ⊗ (B ⊗ (R ⊗ A)))
  let X := U ⊗ (B ⊗ (((E ⊗ S) ⊗ R) ⊗ A))
  let pre : Z ⟶ X := U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫
    U ◁ (B ◁ (α_ (E ⊗ S) R A).inv)
  have hs : f1 = f0 ≫ h ▷ E := by
    change (α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom =
      ((α_ E S R).hom ≫ (β_ E (S ⊗ R)).hom) ≫ h ▷ E
    rw [BraidedCategory.braiding_naturality_right]
    exact (Category.assoc _ _ _).symm
  have ht : f1 ⊗ₘ 𝟙 A = (f0 ⊗ₘ 𝟙 A) ≫ ((h ▷ E) ⊗ₘ 𝟙 A) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, hs]
  have ha : ((h ▷ E) ⊗ₘ 𝟙 A) ≫ (α_ R' E A).hom =
      (α_ (S ⊗ R) E A).hom ≫ (h ⊗ₘ 𝟙 (E ⊗ A)) := by
    simpa only [id_tensorHom_id, tensorHom_id, id_whiskerRight] using associator_naturality h (𝟙 E)
      (𝟙 A)
  have hw : (f1 ⊗ₘ 𝟙 A) ≫ (α_ R' E A).hom =
      (f0 ⊗ₘ 𝟙 A) ≫ (α_ (S ⊗ R) E A).hom ≫ (h ⊗ₘ 𝟙 (E ⊗ A)) := by
    rw [ht, Category.assoc, ha]
  have hw' := congrArg (fun z => U ◁ (B ◁ z)) hw
  simp only [whiskerLeft_comp] at hw'
  have hn := frontMap_naturality_hom h k B (E ⊗ A)
  let tail := W ◁ (frontHomIso E B A).hom
  have hswap := congrArg (fun z => pre ≫ z ≫ frontMap k B (E ⊗ A) ≫ tail) hw'
  have hn' := congrArg (fun z => pre ≫ U ◁ (B ◁ (f0 ⊗ₘ 𝟙 A)) ≫
    U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫ z ≫ tail) hn
  simp only [Category.assoc] at hswap hn'
  have hright : pre ≫ U ◁ (B ◁ (f1 ⊗ₘ 𝟙 A)) ≫ U ◁ (B ◁ (α_ R' E A).hom) ≫
      frontRelationMap k B E A =
    pre ≫ U ◁ (B ◁ (f0 ⊗ₘ 𝟙 A)) ≫ U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫
      frontRelationMap k0 B E A := by
    simpa only [frontRelationMap, frontMap, tail, Category.assoc] using
      hswap.trans hn'
  have hf := outerRelationMap_frame k0 E B A
  have hf' : outerRelationMap k h E B A =
      pre ≫ U ◁ (B ◁ (f0 ⊗ₘ 𝟙 A)) ≫
        U ◁ (B ◁ (α_ (S ⊗ R) E A).hom) ≫ frontRelationMap k0 B E A := by
    simpa only [outerRelationMap, pre, f0, Category.assoc] using hf
  simpa only [pre, f1, Category.assoc] using hf'.trans hright.symm

omit [MonoidalClosed V] in
/-- Actual weight composition and the proved full tensor word give the original outer weight face.
-/
@[reassoc]
theorem frontMap_outerWeight_balance {U E S K R R' Wa Wb : V}
    (w : U ⊗ (E ⊗ S) ⟶ K) (kp : K ⊗ R ⟶ Wa) (kq : U ⊗ R' ⟶ Wb)
    (h : S ⊗ R ⟶ R') (v : Wb ⊗ E ⟶ Wa)
    (hw : (α_ U (E ⊗ S) R).inv ≫ (w ⊗ₘ 𝟙 R) ≫ kp =
      U ◁ ((α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom) ≫
        (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v) (B A : V) :
    (α_ U (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫ (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A))) ≫ frontMap kp B A =
      outerRelationMap kq h E B A ≫ (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A)) := by
  let s : (E ⊗ S) ⊗ R ⟶ R' ⊗ E := (α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom
  let k0 : U ⊗ ((E ⊗ S) ⊗ R) ⟶ Wa := (α_ U (E ⊗ S) R).inv ≫ (w ⊗ₘ 𝟙 R) ≫ kp
  let k1 : U ⊗ (R' ⊗ E) ⟶ Wa := (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v
  let pre := U ◁ (frontHomIso (E ⊗ S) B (R ⊗ A)).inv ≫ U ◁ (B ◁ (α_ (E ⊗ S) R A).inv)
  let l : Wb ⊗ (E ⊗ (B ⊗ A)) ⟶ Wa ⊗ (B ⊗ A) :=
    (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A))
  have hk : k0 = U ◁ s ≫ k1 := hw
  have h0 := frontMap_outerWeight w kp B A
  have h0' : (α_ U (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫
      (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A))) ≫ frontMap kp B A = pre ≫ frontMap k0 B A := by
    simpa only [pre, Category.assoc] using h0
  have hn := frontMap_naturality_hom s k1 B A
  have hn' : pre ≫ frontMap k0 B A = pre ≫ U ◁ (B ◁ (s ⊗ₘ 𝟙 A)) ≫ frontMap k1 B A := by
    rw [hk]
    simpa only [Category.assoc] using congrArg (fun z => pre ≫ z) hn.symm
  have hc := frontMap_composition kq v B A
  have hc' := congrArg (fun z => U ◁ (B ◁ (α_ R' E A).hom) ≫ z) hc
  simp only [frontMap, frontRelationMap, ← whiskerLeft_comp_assoc,
    Category.assoc, Iso.hom_inv_id,
    whiskerLeft_id, Category.id_comp] at hc'
  have hcomp : frontMap k1 B A =
      U ◁ (B ◁ (α_ R' E A).hom) ≫ frontRelationMap kq B E A ≫ l := by
    simpa only [k1, frontMap, frontRelationMap, l, whiskerLeft_comp, Category.assoc] using hc'
  have hframe := outerRelationMap_contract kq h E B A
  have hframe' : outerRelationMap kq h E B A =
      pre ≫ U ◁ (B ◁ (s ⊗ₘ 𝟙 A)) ≫ U ◁ (B ◁ (α_ R' E A).hom) ≫ frontRelationMap kq B E A := by
    simpa only [pre, s, Category.assoc] using hframe
  have ht := congrArg (fun z => pre ≫ U ◁ (B ◁ (s ⊗ₘ 𝟙 A)) ≫ z) hcomp
  have hf := congrArg (fun z => z ≫ l) hframe'
  simp only [Category.assoc] at ht hf
  have result := h0'.trans (hn'.trans (ht.trans hf.symm))
  simpa only [l, Category.assoc] using result
end CategoryTheory.EnrichedDayKernel.AssociatorRightContraction


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]

/-- Both original full right outer relation faces balance after the genuine flat contraction. -/
@[reassoc]
theorem outer_balanced (p q a : I × I) :
    AssociatorFaces.Right.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q a ≫
      contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) =
    AssociatorFaces.Right.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q a ≫
      contractWord d F G H m q a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex q a) := by
  let J := AssociatorRightTensor.outerInclusion (V := V) (C := I) a
  let W := AssociatorIndex.rightWeight d m
  let Q := Associator.rightCoefficients F G H
  let U := (weight d.tensorEnrichedFunctor m).obj (op q)
  let K := (weight d.tensorEnrichedFunctor m).obj (op p)
  let x := d.tensorEnrichedFunctor.obj a
  let E : V := p.1 ⟶[V] q.1
  let S : V := p.2 ⟶[V] q.2
  let R : V := x ⟶[V] p.2
  let R' : V := x ⟶[V] q.2
  let B := F.obj p.1
  let B' := F.obj q.1
  let A := G.obj a.1 ⊗ H.obj a.2
  let Wa := W.obj (op (J.obj p.1))
  let Wb := W.obj (op (J.obj q.1))
  let w : U ⊗ (E ⊗ S) ⟶ K := MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor m).map (op q)
    (op p))
  let kp : K ⊗ R ⟶ Wa := sliceBase d m p a
  let kq : U ⊗ R' ⟶ Wb := sliceBase d m q a
  let h : S ⊗ R ⟶ R' := (β_ S R).hom ≫ eComp V x p.2 q.2
  let b : E ⊗ B ⟶ B' := AssociatorFaces.Right.coefficientAction F p q
  let v : Wb ⊗ E ⟶ Wa := Wb ◁ J.map p.1 q.1 ≫ MonoidalClosed.uncurry (W.map (op (J.obj q.1)) (op
    (J.obj p.1)))
  let c : E ⊗ (B ⊗ A) ⟶ B' ⊗ A := (J.map p.1 q.1 ⊗ₘ 𝟙 (B ⊗ A)) ≫
    (β_ (J.obj p.1 ⟶[V] J.obj q.1) (B ⊗ A)).hom ≫ MonoidalClosed.uncurry (Q.map (J.obj p.1) (J.obj
      q.1))
  let ga : Wa ⊗ (B ⊗ A) ⟶ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.rightGenerator d F G H m (flatIndex p a)
  let gb : Wb ⊗ (B' ⊗ A) ⟶ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.rightGenerator d F G H m (flatIndex q a)
  let l : Wb ⊗ (E ⊗ (B ⊗ A)) ⟶ Wa ⊗ (B ⊗ A) := (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A))
  let r : Wb ⊗ (E ⊗ (B ⊗ A)) ⟶ Wb ⊗ (B' ⊗ A) := Wb ◁ c
  let pre := AssociatorRightContraction.outerRelationMap kq h E B A
  have hw : (α_ U (E ⊗ S) R).inv ≫ (w ⊗ₘ 𝟙 R) ≫ kp =
      U ◁ ((α_ E S R).hom ≫ E ◁ h ≫ (β_ E R').hom) ≫
        (α_ U R' E).inv ≫ (kq ⊗ₘ 𝟙 E) ≫ v := sliceBase_outer d m p q a
  have hc : c = (α_ E B A).inv ≫ (b ⊗ₘ 𝟙 A) := outerInclusion_coefficient_action F G H a p.1 q.1
  have h0 := AssociatorRightContraction.frontMap_outerWeight_balance w kp kq h v hw B A
  have h1 := AssociatorRightContraction.frontMap_outerCoefficient (A := A) kq h b
  have hout := AssociatorRightContraction.outputAction_tensor x p.2 q.2 A
  have hb := AssociatorRightContraction.index_condition J W Q p.1 q.1
  change (α_ Wb E (B ⊗ A)).inv ≫ (v ⊗ₘ 𝟙 (B ⊗ A)) ≫ ga = r ≫ gb at hb
  have hb' : l ≫ ga = r ≫ gb := by simpa only [l, Category.assoc] using hb
  have h0' : (α_ U (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫
      (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A))) ≫ AssociatorRightContraction.frontMap kp B A = pre ≫ l := by
    simpa only [pre, AssociatorRightContraction.outerRelationMap,
      AssociatorRightContraction.frontMap, l, Category.assoc] using h0
  have h1' : U ◁ (tensorμ E S B (R ⊗ A) ≫ (b ⊗ₘ Output.outputAction x p.2 q.2 A)) ≫
      AssociatorRightContraction.frontMap kq B' A = pre ≫ r := by
    rw [hout]
    change _ = pre ≫ Wb ◁ c
    rw [hc]
    exact h1
  change ((α_ U (E ⊗ S) (B ⊗ (R ⊗ A))).inv ≫
      (w ⊗ₘ 𝟙 (B ⊗ (R ⊗ A)))) ≫ (AssociatorRightContraction.frontMap kp B A ≫ ga) =
    U ◁ (tensorμ E S B (R ⊗ A) ≫ (b ⊗ₘ Output.outputAction x p.2 q.2 A)) ≫
      (AssociatorRightContraction.frontMap kq B' A ≫ gb)
  simp only [Category.assoc]
  have hh0 := congrArg (fun z => z ≫ ga) h0'
  have hh1 := congrArg (fun z => z ≫ gb) h1'
  have hh := congrArg (fun z => pre ≫ z) hb'
  simp only [Category.assoc] at hh0 hh1 hh
  simpa only [AssociatorRightContraction.frontMap, Category.assoc] using
    hh0.trans (hh.trans hh1.symm)
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoequalizer
    (AssociatorPresentation.Right.simultaneousLeftMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)]

/-- Descend the original right contraction through both full original relation families. -/
def simultaneousDesc :
    AssociatorPresentation.Right.simultaneousPoint d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m ⟶
      AssociatorFlat.rightPoint d F G H m := by
  let objs : (I × I) × (I × I) → V :=
    AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m
  let family : ∀ pi, objs pi ⟶ AssociatorFlat.rightPoint d F G H m := fun pi =>
    contractWord d F G H m pi.1 pi.2 ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex pi.1 pi.2)
  refine coequalizer.desc (Sigma.desc (f := objs) family) ?_
  apply Sigma.hom_ext
  intro r
  cases r with
  | inl pqi =>
    simp only [AssociatorPresentation.Right.simultaneousLeftMap,
      AssociatorPresentation.Right.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Right.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Right.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        pqi.1.1 pqi.1.2 pqi.2 ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Right.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
      pqi.1.1 pqi.1.2 pqi.2
    let r := AssociatorFaces.Right.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
      pqi.1.1 pqi.1.2 pqi.2
    have hl : (l ≫ Sigma.ι objs (pqi.1.1, pqi.2)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pqi.1.1, pqi.2) :=
      (Category.assoc l (Sigma.ι objs (pqi.1.1, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.1, pqi.2)))
    have hr : (r ≫ Sigma.ι objs (pqi.1.2, pqi.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pqi.1.2, pqi.2) :=
      (Category.assoc r (Sigma.ι objs (pqi.1.2, pqi.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pqi.1.2, pqi.2)))
    have hb : l ≫ family (pqi.1.1, pqi.2) = r ≫ family (pqi.1.2, pqi.2) :=
      outer_balanced d F G H m pqi.1.1 pqi.1.2 pqi.2
    exact hl.trans (hb.trans hr.symm)
  | inr pij =>
    simp only [AssociatorPresentation.Right.simultaneousLeftMap,
      AssociatorPresentation.Right.simultaneousRightMap, Sigma.ι_comp_desc_assoc]
    change ((AssociatorFaces.Right.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family) =
      ((AssociatorFaces.Right.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        pij.1 pij.2.1 pij.2.2 ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family)
    let l := AssociatorFaces.Right.b0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
      pij.1 pij.2.1 pij.2.2
    let r := AssociatorFaces.Right.b1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
      pij.1 pij.2.1 pij.2.2
    have hl : (l ≫ Sigma.ι objs (pij.1, pij.2.1)) ≫ Sigma.desc (f := objs) family =
        l ≫ family (pij.1, pij.2.1) :=
      (Category.assoc l (Sigma.ι objs (pij.1, pij.2.1)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => l ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.1)))
    have hr : (r ≫ Sigma.ι objs (pij.1, pij.2.2)) ≫ Sigma.desc (f := objs) family =
        r ≫ family (pij.1, pij.2.2) :=
      (Category.assoc r (Sigma.ι objs (pij.1, pij.2.2)) (Sigma.desc (f := objs) family)).trans
        (congrArg (fun z => r ≫ z) (Sigma.ι_comp_desc (f := objs) family (pij.1, pij.2.2)))
    have hb : l ≫ family (pij.1, pij.2.1) = r ≫ family (pij.1, pij.2.2) :=
      inner_balanced d F G H m pij.1 pij.2.1 pij.2.2
    exact hl.trans (hb.trans hr.symm)

/-- The simultaneous descent retains the actual original contraction on every raw right word. -/
@[reassoc]
theorem simultaneousProjection_simultaneousDesc (p a : I × I) :
    AssociatorPresentation.Right.simultaneousProjection d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m p a ≫
        simultaneousDesc d F G H m =
      contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) := by
  simp only [AssociatorPresentation.Right.simultaneousProjection, simultaneousDesc,
    Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Right.objects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Right.innerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
    (AssociatorFaces.Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m pq)]
  [∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Right.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)
    (AssociatorPresentation.Right.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [HasCoproduct (AssociatorPresentation.Right.innerObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.outerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoequalizer
    (AssociatorPresentation.Right.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
      m)
    (AssociatorPresentation.Right.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
      F m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)]

/-- The actual original right nested Day value descends to its unchanged selected flat triple coend.
-/
def nestedToFlat :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m ⟶
      AssociatorFlat.rightPoint d F G H m :=
  (AssociatorNested.Right.simultaneousIso d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
    m).hom ≫
    simultaneousDesc d F G H m

/-- Both original right generator legs contract to the exact original right flat summand. -/
@[reassoc]
theorem nestedGenerator_nestedToFlat (p a : I × I) :
    AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p
      a ≫
        nestedToFlat d F G H m =
      contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) := by
  simp only [nestedToFlat, ← Category.assoc]
  rw [AssociatorNested.Right.nestedGenerator_simultaneousIso_hom,
    simultaneousProjection_simultaneousDesc]
  simp only [contractWord, Category.assoc]

/-- The original nested generators prove the right comparison's nested inverse equation. -/
@[reassoc]
theorem nestedToFlat_flatToNested :
    nestedToFlat d F G H m ≫ flatToNested d F G H m =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
        H) m) := by
  apply AssociatorNested.Right.hom_ext d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
  intro p a
  rw [← Category.assoc, nestedGenerator_nestedToFlat]
  simpa only [Category.assoc, Category.comp_id] using contractWord_generator_factorization d F G H m
    p a

/-- Actual identity insertion proves the right comparison's flat inverse equation. -/
@[reassoc]
theorem flatToNested_nestedToFlat :
    flatToNested d F G H m ≫ nestedToFlat d F G H m = 𝟙 (AssociatorFlat.rightPoint d F G H m) := by
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.rightWeight d m)
    (Associator.rightCoefficients F G H)
  intro X
  rcases X with ⟨⟨e, g⟩, h⟩
  have hx := rightGenerator_flatToNested_identity d F G H m ((e, g), h)
  have hn := nestedGenerator_nestedToFlat d F G H m (e, g ⊗ h) (g, h)
  have hi := identityWord_contractWord d F G H m ((e, g), h)
  rw [← Category.assoc, hx, Category.assoc, hn]
  rw [← Category.assoc, hi]
  simp only [Category.id_comp, Category.comp_id]

/-- The genuine right flattening comparison on the original nested Day value and chosen coends. -/
def iso : AssociatorFlat.rightPoint d F G H m ≅
    EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m
      where
  hom := flatToNested d F G H m
  inv := nestedToFlat d F G H m
  hom_inv_id := flatToNested_nestedToFlat d F G H m
  inv_hom_id := nestedToFlat_flatToNested d F G H m

/-- The actual right comparison's forward map preserves every original flat generator. -/
@[reassoc]
theorem rightGenerator_iso_hom (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ (iso d F G H m).hom =
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] m) ⊗ₘ
        (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)))
          ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
          m
          (X.1.1, X.1.2 ⊗ X.2) := rightGenerator_flatToNested d F G H m X

/-- The actual inverse preserves both original right nested generator legs and their full weight
  action. -/
@[reassoc]
theorem nestedGenerator_iso_inv (p a : I × I) :
    AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p
      a ≫
        (iso d F G H m).inv =
      contractWord d F G H m p a ≫ AssociatorFlat.rightGenerator d F G H m (flatIndex p a) :=
  nestedGenerator_nestedToFlat d F G H m p a
end CategoryTheory.EnrichedDayKernel.AssociatorRightFlattening


namespace CategoryTheory.EnrichedDayKernel.AssociatorNaturality

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

section OutputAlgebra

variable [BraidedCategory V] {K : Type uK} [EnrichedCategory V K]

/-- The original output action commutes with every coefficient arrow. -/
@[reassoc]
theorem outputAction_coefficient (x m n : K) {Q Q' : V} (q : Q ⟶ Q') :
    (m ⟶[V] n) ◁ ((x ⟶[V] m) ◁ q) ≫ Output.outputAction x m n Q' =
      Output.outputAction x m n Q ≫ ((x ⟶[V] n) ◁ q) := by
  dsimp only [Output.outputAction]
  simp only [Category.assoc, tensorHom_id]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    whisker_exchange (eComp V x m n) q]

end OutputAlgebra

section OutputPrecomposition

variable [BraidedCategory V] {K : Type uK} [Category.{vK} K]
  [EnrichedOrdinaryCategory V K]

/-- Full output composition commutes with original enriched precomposition. -/
@[reassoc]
theorem outputAction_precomposition {x y : K} (f : x ⟶ y) (m n : K)
    {Q Q' : V} (q : Q ⟶ Q') :
    (m ⟶[V] n) ◁ (eHomWhiskerRight V f m ⊗ₘ q) ≫
        Output.outputAction x m n Q' =
      Output.outputAction y m n Q ≫ (eHomWhiskerRight V f n ⊗ₘ q) := by
  simp only [Output.outputAction, Category.assoc, ← id_tensorHom]
  rw [associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  simp only [tensorHom_id]
  rw [← eComp_eHomWhiskerRight]

end OutputPrecomposition

section UnitInputs

variable [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

variable
  (T : EnrichedFunctor V (C × D) K)
  {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')

/-- Input transformations commute with the original inserted-identity generator. -/
@[reassoc]
theorem unitGenerator_input (X : C × D)
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj X))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj X))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj X))
      (EnrichedDayKernel.rightMap T F G (T.obj X))]
    [HasCoproduct (EnrichedDayKernel.objects T F' G' (T.obj X))]
    [HasCoproduct (EnrichedDayKernel.relations T F' G' (T.obj X))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F' G' (T.obj X))
      (EnrichedDayKernel.rightMap T F' G' (T.obj X))] :
    AssociatorUnit.unitGenerator T F G X ≫ Input.mapAt T a b (T.obj X) =
      ((eHomEquiv V).symm (a.app X.1) ⊗ₘ (eHomEquiv V).symm (b.app X.2)) ≫
        AssociatorUnit.unitGenerator T F' G' X := by
  let Q := F.obj X.1 ⊗ G.obj X.2
  let Q' := F'.obj X.1 ⊗ G'.obj X.2
  let E : V := T.obj X ⟶[V] T.obj X
  let s : Q ⟶ Q' :=
    (eHomEquiv V).symm (a.app X.1) ⊗ₘ (eHomEquiv V).symm (b.app X.2)
  let g : E ⊗ Q ⟶ EnrichedDayKernel.obj T F G (T.obj X) :=
    EnrichedDayKernel.gen T F G (T.obj X) X
  let g' : E ⊗ Q' ⟶ EnrichedDayKernel.obj T F' G' (T.obj X) :=
    EnrichedDayKernel.gen T F' G' (T.obj X) X
  have hg : g ≫ Input.mapAt T a b (T.obj X) = (𝟙 E ⊗ₘ s) ≫ g' :=
    Input.gen_mapAt T a b (T.obj X) X
  change (AssociatorUnit.identityInsert (T.obj X) Q ≫ g) ≫
    Input.mapAt T a b (T.obj X) = s ≫ AssociatorUnit.identityInsert (T.obj X) Q' ≫ g'
  rw [Category.assoc, hg]
  simpa only [id_tensorHom, Category.assoc] using
    AssociatorUnit.identityInsert_naturality_assoc (T.obj X) s g'

end UnitInputs

section MapInputs

variable [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (T : EnrichedFunctor V A B)
  (W : EnrichedFunctor V Aᵒᵖ V) (W' : EnrichedFunctor V Bᵒᵖ V)
  (Q₀ Q₁ : EnrichedFunctor V A V) (Q₀' Q₁' : EnrichedFunctor V B V)
  (w : ∀ X, W.obj (op X) ⟶ W'.obj (op (T.obj X)))
  (q₀ : ∀ X, Q₀.obj X ⟶ Q₀'.obj (T.obj X))
  (q₁ : ∀ X, Q₁.obj X ⟶ Q₁'.obj (T.obj X))
  (hW : ∀ X Y,
    MonoidalClosed.uncurry (W.map (op Y) (op X)) ≫ w X =
      (w Y ⊗ₘ T.map X Y) ≫
        MonoidalClosed.uncurry (W'.map (op (T.obj Y)) (op (T.obj X))))
  (hQ₀ : ∀ X Y,
    MonoidalClosed.uncurry (Q₀.map X Y) ≫ q₀ Y =
      (q₀ X ⊗ₘ T.map X Y) ≫ MonoidalClosed.uncurry (Q₀'.map (T.obj X) (T.obj Y)))
  (hQ₁ : ∀ X Y,
    MonoidalClosed.uncurry (Q₁.map X Y) ≫ q₁ Y =
      (q₁ X ⊗ₘ T.map X Y) ≫ MonoidalClosed.uncurry (Q₁'.map (T.obj X) (T.obj Y)))
  (s : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) Q₀ Q₁)
  (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) Q₀' Q₁')
  [HasCoproduct (Enriched.weightedCoend.objects W Q₀)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q₀)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q₀) (Enriched.weightedCoend.rightMap W Q₀)]
  [HasCoproduct (Enriched.weightedCoend.objects W Q₁)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q₁)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q₁) (Enriched.weightedCoend.rightMap W Q₁)]
  [HasCoproduct (Enriched.weightedCoend.objects W' Q₀')]
  [HasCoproduct (Enriched.weightedCoend.relations W' Q₀')]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q₀') (Enriched.weightedCoend.rightMap W' Q₀')]
  [HasCoproduct (Enriched.weightedCoend.objects W' Q₁')]
  [HasCoproduct (Enriched.weightedCoend.relations W' Q₁')]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q₁') (Enriched.weightedCoend.rightMap W' Q₁')]

/-- Proved coefficient squares induce a square of the actual chosen coend maps. -/
theorem map_diagram_natural
    (hq : ∀ X, (eHomEquiv V).symm (s.app X) ≫ q₁ X =
      q₀ X ≫ (eHomEquiv V).symm (t.app (T.obj X))) :
    Enriched.weightedCoend.mapDiagramGraded W s ≫
        Enriched.weightedCoend.Transport.map T W W' Q₁ Q₁' w q₁ hW hQ₁ =
      Enriched.weightedCoend.Transport.map T W W' Q₀ Q₀' w q₀ hW hQ₀ ≫
        Enriched.weightedCoend.mapDiagramGraded W' t := by
  apply Enriched.weightedCoend.hom_ext W Q₀
  intro X
  let u : Q₀.obj X ⟶ Q₁.obj X := (eHomEquiv V).symm (s.app X)
  let v : Q₀'.obj (T.obj X) ⟶ Q₁'.obj (T.obj X) :=
    (eHomEquiv V).symm (t.app (T.obj X))
  let D : Enriched.weightedCoend W Q₀ ⟶ Enriched.weightedCoend W Q₁ :=
    Enriched.weightedCoend.mapDiagramGraded W s
  let D' : Enriched.weightedCoend W' Q₀' ⟶ Enriched.weightedCoend W' Q₁' :=
    Enriched.weightedCoend.mapDiagramGraded W' t
  let M₀ := Enriched.weightedCoend.Transport.map T W W' Q₀ Q₀' w q₀ hW hQ₀
  let M₁ := Enriched.weightedCoend.Transport.map T W W' Q₁ Q₁' w q₁ hW hQ₁
  let i₀ : W.obj (op X) ⊗ Q₀.obj X ⟶ Enriched.weightedCoend W Q₀ :=
    Enriched.weightedCoend.ι W Q₀ X
  let i₁ : W.obj (op X) ⊗ Q₁.obj X ⟶ Enriched.weightedCoend W Q₁ :=
    Enriched.weightedCoend.ι W Q₁ X
  let j₀ : W'.obj (op (T.obj X)) ⊗ Q₀'.obj (T.obj X) ⟶
      Enriched.weightedCoend W' Q₀' := Enriched.weightedCoend.ι W' Q₀' (T.obj X)
  let j₁ : W'.obj (op (T.obj X)) ⊗ Q₁'.obj (T.obj X) ⟶
      Enriched.weightedCoend W' Q₁' := Enriched.weightedCoend.ι W' Q₁' (T.obj X)
  have hd : i₀ ≫ D = (𝟙 (W.obj (op X)) ⊗ₘ u) ≫ i₁ :=
    Enriched.weightedCoend.mapDiagramGraded_ι W s X
  have hd' : j₀ ≫ D' = (𝟙 (W'.obj (op (T.obj X))) ⊗ₘ v) ≫ j₁ :=
    Enriched.weightedCoend.mapDiagramGraded_ι W' t (T.obj X)
  have hm₀ : i₀ ≫ M₀ = (w X ⊗ₘ q₀ X) ≫ j₀ :=
    Enriched.weightedCoend.Transport.ι_map T W W' Q₀ Q₀' w q₀ hW hQ₀ X
  have hm₁ : i₁ ≫ M₁ = (w X ⊗ₘ q₁ X) ≫ j₁ :=
    Enriched.weightedCoend.Transport.ι_map T W W' Q₁ Q₁' w q₁ hW hQ₁ X
  have hs : u ≫ q₁ X = q₀ X ≫ v := hq X
  change i₀ ≫ (D ≫ M₁) = i₀ ≫ (M₀ ≫ D')
  calc
    _ = (𝟙 (W.obj (op X)) ⊗ₘ u) ≫ i₁ ≫ M₁ := by
      rw [← Category.assoc, hd, Category.assoc]
    _ = (𝟙 (W.obj (op X)) ⊗ₘ u) ≫ (w X ⊗ₘ q₁ X) ≫ j₁ := by rw [hm₁]
    _ = (w X ⊗ₘ q₀ X) ≫ (𝟙 (W'.obj (op (T.obj X))) ⊗ₘ v) ≫ j₁ := by
      simp only [← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id, hs]
    _ = (w X ⊗ₘ q₀ X) ≫ j₀ ≫ D' := by rw [hd']
    _ = _ := by rw [← Category.assoc, ← hm₀, Category.assoc]

end MapInputs

section SelfTransport

variable [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

/-- Actual isomorphism transport retains the complete uncurried Hom action. -/
theorem uncurry_ofIsoComponents (F : EnrichedFunctor V C V) (Gobj : C → V)
    (e : ∀ X, F.obj X ≅ Gobj X) (X Y : C) :
    MonoidalClosed.uncurry ((F.ofIsoComponents Gobj e).map X Y) =
      ((e X).inv ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (F.map X Y) ≫
        (e Y).hom := by
  have hx : (eHomEquiv V).symm ((F.ofIsoComponentsGraded Gobj e).app X) = (e X).hom :=
    (congrArg (eHomEquiv V).symm
      (EnrichedFunctor.ofIsoComponentsGraded_app F Gobj e X)).trans
        ((eHomEquiv V).symm_apply_apply (e X).hom)
  have hy : (eHomEquiv V).symm ((F.ofIsoComponentsGraded Gobj e).app Y) = (e Y).hom :=
    (congrArg (eHomEquiv V).symm
      (EnrichedFunctor.ofIsoComponentsGraded_app F Gobj e Y)).trans
        ((eHomEquiv V).symm_apply_apply (e Y).hom)
  have h := (F.ofIsoComponentsGraded Gobj e).uncurriedNaturality X Y
  rw [hx, hy] at h
  let t : F.obj X ⊗ (X ⟶[V] Y) ≅ Gobj X ⊗ (X ⟶[V] Y) :=
    e X ⊗ᵢ Iso.refl (X ⟶[V] Y)
  have hi := congrArg (fun f => t.inv ≫ f) h
  change t.inv ≫ (MonoidalClosed.uncurry (F.map X Y) ≫ (e Y).hom) =
    t.inv ≫ t.hom ≫ MonoidalClosed.uncurry ((F.ofIsoComponents Gobj e).map X Y) at hi
  rw [Iso.inv_hom_id_assoc] at hi
  exact hi.symm

end SelfTransport

section LeftOutput

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.leftObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.leftRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.leftMap0 d F G H k)
    (AssociatorFlat.leftMap1 d F G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H k)]

/-- The actual left flattening map commutes with the full curried output action. -/
theorem left_actionDesc_natural (m n : I) :
    Output.actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n ≫
        (ihom (m ⟶[V] n)).map (AssociatorFlattening.flatToNested d F G H n) =
      AssociatorFlattening.flatToNested d F G H m ≫
        Output.actionDesc d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
          H m n := by
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d m)
    (Associator.leftCoefficients F G H)
  intro X
  let x := (X.1.1 ⊗ X.1.2) ⊗ X.2
  let p : I × I := (X.1.1 ⊗ X.1.2, X.2)
  let Q := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let Q' := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G (X.1.1 ⊗ X.1.2) ⊗ H.obj X.2
  let R : V := m ⟶[V] n
  let s : Q ⟶ Q' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2)
  let fₘ := AssociatorFlattening.flatToNested d F G H m
  let fₙ := AssociatorFlattening.flatToNested d F G H n
  let iₘ : (x ⟶[V] m) ⊗ Q ⟶ AssociatorFlat.leftPoint d F G H m :=
    AssociatorFlat.leftGenerator d F G H m X
  let iₙ : (x ⟶[V] n) ⊗ Q ⟶ AssociatorFlat.leftPoint d F G H n :=
    AssociatorFlat.leftGenerator d F G H n X
  let jₘ : (x ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m p
  let jₙ : (x ⟶[V] n) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H n :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H n p
  let a₀ := Output.actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n
  let a₁ := Output.actionDesc d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m n
  have hm : iₘ ≫ fₘ = (𝟙 (x ⟶[V] m) ⊗ₘ s) ≫ jₘ :=
    AssociatorFlattening.leftGenerator_flatToNested d F G H m X
  have hn : iₙ ≫ fₙ = (𝟙 (x ⟶[V] n) ⊗ₘ s) ≫ jₙ :=
    AssociatorFlattening.leftGenerator_flatToNested d F G H n X
  have h₀ : R ◁ iₘ ≫ MonoidalClosed.uncurry a₀ = Output.outputAction x m n Q ≫ iₙ := by
    have h := congrArg MonoidalClosed.uncurry
      (Output.gen_actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n X)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] at h
    exact h
  have h₁ : R ◁ jₘ ≫ MonoidalClosed.uncurry a₁ = Output.outputAction x m n Q' ≫ jₙ := by
    have h := congrArg MonoidalClosed.uncurry
      (Output.gen_actionDesc d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H m n p)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] at h
    exact h
  change iₘ ≫ (a₀ ≫ (ihom R).map fₙ) = iₘ ≫ (fₘ ≫ a₁)
  apply MonoidalClosed.uncurry_injective (A := R)
  rw [MonoidalClosed.uncurry_natural_left iₘ (a₀ ≫ (ihom R).map fₙ),
    MonoidalClosed.uncurry_natural_right a₀ fₙ,
    MonoidalClosed.uncurry_natural_left iₘ (fₘ ≫ a₁),
    MonoidalClosed.uncurry_natural_left fₘ a₁]
  rw [← Category.assoc, h₀, Category.assoc, hn]
  rw [← whiskerLeft_comp_assoc, hm, whiskerLeft_comp, Category.assoc, h₁]
  simpa only [id_tensorHom, Category.assoc] using
    (outputAction_coefficient_assoc x m n s jₙ).symm

/-- Entire output-index Hom naturality of the actual left flat-to-nested map. -/
theorem left_output_natural (m n : I) :
    MonoidalClosed.uncurry
        ((Output.functor (AssociatorIndex.leftIndex d) (F.externalTensor G) H).map m n) ≫
      AssociatorFlattening.flatToNested d F G H n =
    (AssociatorFlattening.flatToNested d F G H m ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
      MonoidalClosed.uncurry
        ((Output.functor d.tensorEnrichedFunctor
          (Output.functor d.tensorEnrichedFunctor F G) H).map m n) := by
  have h := congrArg (MonoidalClosed.uncurry (A := m ⟶[V] n))
    (left_actionDesc_natural d F G H m n)
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left] at h
  rw [Output.functor_map, Output.functor_map, Output.map_uncurry, Output.map_uncurry]
  rw [Category.assoc, h]
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun t => t ≫ MonoidalClosed.uncurry
      (Output.actionDesc d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H m n))
      (BraidedCategory.braiding_inv_naturality_left
        (AssociatorFlattening.flatToNested d F G H m) (m ⟶[V] n)).symm

end LeftOutput

section RightFlatOutput

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable
  [∀ k : I, HasCoproduct (AssociatorFlat.leftObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.leftRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.leftMap0 d F G H k)
    (AssociatorFlat.leftMap1 d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.rightObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.rightRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.rightMap0 d F G H k)
    (AssociatorFlat.rightMap1 d F G H k)]

/-- The actual right flat objects, with full output maps transported by the proved flat Iso. -/
def rightOutputFunctor : EnrichedFunctor V I V :=
  EnrichedFunctor.ofIsoComponents
    (Output.functor (AssociatorIndex.leftIndex d) (F.externalTensor G) H)
    (fun m => AssociatorFlat.rightPoint d F G H m)
    (fun m => AssociatorFlat.iso d F G H m)

@[simp]
theorem rightOutputFunctor_obj (m : I) :
    (rightOutputFunctor d F G H).obj m = AssociatorFlat.rightPoint d F G H m := rfl

/-- The chosen right curried action uses both actual flat comparison legs. -/
def rightActionDesc (m n : I) :
    AssociatorFlat.rightPoint d F G H m ⟶
      (ihom (m ⟶[V] n)).obj (AssociatorFlat.rightPoint d F G H n) :=
  (AssociatorFlat.iso d F G H m).inv ≫
    Output.actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n ≫
      (ihom (m ⟶[V] n)).map (AssociatorFlat.iso d F G H n).hom

/-- Its literal output map retains the original inverse output-Hom braid. -/
theorem rightOutputFunctor_map_uncurry (m n : I) :
    MonoidalClosed.uncurry ((rightOutputFunctor d F G H).map m n) =
      (β_ (m ⟶[V] n) (AssociatorFlat.rightPoint d F G H m)).inv ≫
        MonoidalClosed.uncurry (rightActionDesc d F G H m n) := by
  let R : V := m ⟶[V] n
  let eₘ : AssociatorFlat.leftPoint d F G H m ≅ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.iso d F G H m
  let eₙ : AssociatorFlat.leftPoint d F G H n ≅ AssociatorFlat.rightPoint d F G H n :=
    AssociatorFlat.iso d F G H n
  let a : AssociatorFlat.leftPoint d F G H m ⟶
      (ihom R).obj (AssociatorFlat.leftPoint d F G H n) :=
    Output.actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n
  let M : R ⟶ (ihom (AssociatorFlat.rightPoint d F G H m)).obj
      (AssociatorFlat.rightPoint d F G H n) := (rightOutputFunctor d F G H).map m n
  have ht : MonoidalClosed.uncurry M =
      (eₘ.inv ⊗ₘ 𝟙 R) ≫
        MonoidalClosed.uncurry (Output.map (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n)
          ≫
          eₙ.hom :=
    uncurry_ofIsoComponents
      (Output.functor (AssociatorIndex.leftIndex d) (F.externalTensor G) H)
      (fun k => AssociatorFlat.rightPoint d F G H k)
      (fun k => AssociatorFlat.iso d F G H k) m n
  have ha :
      MonoidalClosed.uncurry (Output.map (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n) =
        (β_ R (AssociatorFlat.leftPoint d F G H m)).inv ≫ MonoidalClosed.uncurry a :=
    Output.map_uncurry (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n
  have hd : MonoidalClosed.uncurry (rightActionDesc d F G H m n) =
      R ◁ eₘ.inv ≫ MonoidalClosed.uncurry a ≫ eₙ.hom := by
    change MonoidalClosed.uncurry (eₘ.inv ≫ (a ≫ (ihom R).map eₙ.hom)) =
      R ◁ eₘ.inv ≫ MonoidalClosed.uncurry a ≫ eₙ.hom
    rw [MonoidalClosed.uncurry_natural_left eₘ.inv (a ≫ (ihom R).map eₙ.hom),
      MonoidalClosed.uncurry_natural_right a eₙ.hom]
  have hb : (eₘ.inv ⊗ₘ 𝟙 R) ≫ (β_ R (AssociatorFlat.leftPoint d F G H m)).inv =
      (β_ R (AssociatorFlat.rightPoint d F G H m)).inv ≫ R ◁ eₘ.inv := by
    simpa only [tensorHom_id] using BraidedCategory.braiding_inv_naturality_left eₘ.inv R
  change MonoidalClosed.uncurry M =
    (β_ R (AssociatorFlat.rightPoint d F G H m)).inv ≫
      MonoidalClosed.uncurry (rightActionDesc d F G H m n)
  calc
    _ = (eₘ.inv ⊗ₘ 𝟙 R) ≫
        MonoidalClosed.uncurry (Output.map (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n)
          ≫
          eₙ.hom := ht
    _ = (eₘ.inv ⊗ₘ 𝟙 R) ≫ (β_ R (AssociatorFlat.leftPoint d F G H m)).inv ≫
        MonoidalClosed.uncurry a ≫ eₙ.hom := by
      rw [ha]
      simp only [Category.assoc]
    _ = (β_ R (AssociatorFlat.rightPoint d F G H m)).inv ≫ R ◁ eₘ.inv ≫
        MonoidalClosed.uncurry a ≫ eₙ.hom := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ MonoidalClosed.uncurry a ≫ eₙ.hom) hb
    _ = _ := by rw [hd]

/-- Every original right generator has exactly its original full output composition action. -/
@[reassoc]
theorem right_actionDesc_generator (m n : I) (X : (I × I) × I) :
    (m ⟶[V] n) ◁ AssociatorFlat.rightGenerator d F G H m X ≫
        MonoidalClosed.uncurry (rightActionDesc d F G H m n) =
      Output.outputAction (X.1.1 ⊗ (X.1.2 ⊗ X.2)) m n
        (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) ≫
          AssociatorFlat.rightGenerator d F G H n X := by
  let l := (X.1.1 ⊗ X.1.2) ⊗ X.2
  let r := X.1.1 ⊗ (X.1.2 ⊗ X.2)
  let Q := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let Q' := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let R : V := m ⟶[V] n
  let eₘ : AssociatorFlat.leftPoint d F G H m ≅ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.iso d F G H m
  let eₙ : AssociatorFlat.leftPoint d F G H n ≅ AssociatorFlat.rightPoint d F G H n :=
    AssociatorFlat.iso d F G H n
  let c : Q ≅ Q' := α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)
  let iₘ : (l ⟶[V] m) ⊗ Q ⟶ AssociatorFlat.leftPoint d F G H m :=
    AssociatorFlat.leftGenerator d F G H m X
  let iₙ : (l ⟶[V] n) ⊗ Q ⟶ AssociatorFlat.leftPoint d F G H n :=
    AssociatorFlat.leftGenerator d F G H n X
  let jₘ : (r ⟶[V] m) ⊗ Q' ⟶ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.rightGenerator d F G H m X
  let jₙ : (r ⟶[V] n) ⊗ Q' ⟶ AssociatorFlat.rightPoint d F G H n :=
    AssociatorFlat.rightGenerator d F G H n X
  let pₘ : (r ⟶[V] m) ⟶ (l ⟶[V] m) := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m
  let pₙ : (r ⟶[V] n) ⟶ (l ⟶[V] n) := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom n
  let qₙ : (l ⟶[V] n) ⟶ (r ⟶[V] n) := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv n
  let a : AssociatorFlat.leftPoint d F G H m ⟶
      (ihom R).obj (AssociatorFlat.leftPoint d F G H n) :=
    Output.actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n
  have hi : jₘ ≫ eₘ.inv = (pₘ ⊗ₘ c.inv) ≫ iₘ :=
    AssociatorFlat.rightGenerator_iso_inv d F G H m X
  have hf : iₙ ≫ eₙ.hom = (qₙ ⊗ₘ c.hom) ≫ jₙ :=
    AssociatorFlat.leftGenerator_iso_hom d F G H n X
  have ha : R ◁ iₘ ≫ MonoidalClosed.uncurry a = Output.outputAction l m n Q ≫ iₙ := by
    have h := congrArg MonoidalClosed.uncurry
      (Output.gen_actionDesc (AssociatorIndex.leftIndex d) (F.externalTensor G) H m n X)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] at h
    exact h
  have hd : MonoidalClosed.uncurry (rightActionDesc d F G H m n) =
      R ◁ eₘ.inv ≫ MonoidalClosed.uncurry a ≫ eₙ.hom := by
    change MonoidalClosed.uncurry (eₘ.inv ≫ (a ≫ (ihom R).map eₙ.hom)) =
      R ◁ eₘ.inv ≫ MonoidalClosed.uncurry a ≫ eₙ.hom
    rw [MonoidalClosed.uncurry_natural_left eₘ.inv (a ≫ (ihom R).map eₙ.hom),
      MonoidalClosed.uncurry_natural_right a eₙ.hom]
  have hp : R ◁ (pₘ ⊗ₘ c.inv) ≫ Output.outputAction l m n Q =
      Output.outputAction r m n Q' ≫ (pₙ ⊗ₘ c.inv) :=
    outputAction_precomposition (α_ X.1.1 X.1.2 X.2).hom m n c.inv
  have hc : (pₙ ⊗ₘ c.inv) ≫ (qₙ ⊗ₘ c.hom) = 𝟙 ((r ⟶[V] n) ⊗ Q') := by
    change (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom n ⊗ₘ c.inv) ≫
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv n ⊗ₘ c.hom) = 𝟙 _
    rw [tensorHom_comp_tensorHom, ← eHomWhiskerRight_comp]
    simp only [Iso.inv_hom_id, eHomWhiskerRight_id, id_tensorHom_id]
  change R ◁ jₘ ≫ MonoidalClosed.uncurry (rightActionDesc d F G H m n) =
    Output.outputAction r m n Q' ≫ jₙ
  calc
    _ = R ◁ (jₘ ≫ eₘ.inv) ≫ MonoidalClosed.uncurry a ≫ eₙ.hom := by
      rw [hd, whiskerLeft_comp]
      simp only [Category.assoc]
    _ = R ◁ (pₘ ⊗ₘ c.inv) ≫ R ◁ iₘ ≫ MonoidalClosed.uncurry a ≫ eₙ.hom := by
      rw [hi, whiskerLeft_comp]
      simp only [Category.assoc]
    _ = R ◁ (pₘ ⊗ₘ c.inv) ≫ Output.outputAction l m n Q ≫ iₙ ≫ eₙ.hom := by
      simpa only [Category.assoc] using
        congrArg (fun f => R ◁ (pₘ ⊗ₘ c.inv) ≫ f ≫ eₙ.hom) ha
    _ = R ◁ (pₘ ⊗ₘ c.inv) ≫ Output.outputAction l m n Q ≫ (qₙ ⊗ₘ c.hom) ≫ jₙ := by rw [hf]
    _ = Output.outputAction r m n Q' ≫ (pₙ ⊗ₘ c.inv) ≫ (qₙ ⊗ₘ c.hom) ≫ jₙ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ (qₙ ⊗ₘ c.hom) ≫ jₙ) hp
    _ = _ := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f => Output.outputAction r m n Q' ≫ f ≫ jₙ) hc

/-- The actual right full output map is characterized on every original right generator. -/
@[reassoc]
theorem right_output_generator (m n : I) (X : (I × I) × I) :
    (AssociatorFlat.rightGenerator d F G H m X ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
        MonoidalClosed.uncurry ((rightOutputFunctor d F G H).map m n) =
      (β_ (m ⟶[V] n) (AssociatorFlat.rightObjects d F G H m X)).inv ≫
        Output.outputAction (X.1.1 ⊗ (X.1.2 ⊗ X.2)) m n
          (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) ≫
            AssociatorFlat.rightGenerator d F G H n X := by
  let R : V := m ⟶[V] n
  let M : R ⟶ (ihom (AssociatorFlat.rightPoint d F G H m)).obj
      (AssociatorFlat.rightPoint d F G H n) := (rightOutputFunctor d F G H).map m n
  let g : AssociatorFlat.rightObjects d F G H m X ⟶ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.rightGenerator d F G H m X
  have hm : MonoidalClosed.uncurry M =
      (β_ R (AssociatorFlat.rightPoint d F G H m)).inv ≫
        MonoidalClosed.uncurry (rightActionDesc d F G H m n) :=
    rightOutputFunctor_map_uncurry d F G H m n
  change (g ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry M =
    (β_ R (AssociatorFlat.rightObjects d F G H m X)).inv ≫
      Output.outputAction (X.1.1 ⊗ (X.1.2 ⊗ X.2)) m n
        (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) ≫
          AssociatorFlat.rightGenerator d F G H n X
  rw [hm]
  rw [tensorHom_id, ← Category.assoc, BraidedCategory.braiding_inv_naturality_left,
    Category.assoc, right_actionDesc_generator]
  rfl

end RightFlatOutput

section RightOutput

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable
  [∀ k : I, HasCoproduct (AssociatorFlat.leftObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.leftRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.leftMap0 d F G H k)
    (AssociatorFlat.leftMap1 d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.rightObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.rightRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.rightMap0 d F G H k)
    (AssociatorFlat.rightMap1 d F G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) k)]

/-- The actual right flattening map preserves the full curried output action. -/
theorem right_actionDesc_natural (m n : I) :
    rightActionDesc d F G H m n ≫
        (ihom (m ⟶[V] n)).map (AssociatorRightFlattening.flatToNested d F G H n) =
      AssociatorRightFlattening.flatToNested d F G H m ≫
        Output.actionDesc d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m n
          := by
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.rightWeight d m)
    (Associator.rightCoefficients F G H)
  intro X
  let x := X.1.1 ⊗ (X.1.2 ⊗ X.2)
  let p : I × I := (X.1.1, X.1.2 ⊗ X.2)
  let Q := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let Q' := F.obj X.1.1 ⊗ EnrichedDayKernel.obj d.tensorEnrichedFunctor G H (X.1.2 ⊗ X.2)
  let R : V := m ⟶[V] n
  let s : Q ⟶ Q' := 𝟙 (F.obj X.1.1) ⊗ₘ
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)
  let fₘ := AssociatorRightFlattening.flatToNested d F G H m
  let fₙ := AssociatorRightFlattening.flatToNested d F G H n
  let iₘ : (x ⟶[V] m) ⊗ Q ⟶ AssociatorFlat.rightPoint d F G H m :=
    AssociatorFlat.rightGenerator d F G H m X
  let iₙ : (x ⟶[V] n) ⊗ Q ⟶ AssociatorFlat.rightPoint d F G H n :=
    AssociatorFlat.rightGenerator d F G H n X
  let jₘ : (x ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m p
  let jₙ : (x ⟶[V] n) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) n :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) n p
  let a₀ : AssociatorFlat.rightPoint d F G H m ⟶
      (ihom R).obj (AssociatorFlat.rightPoint d F G H n) := rightActionDesc d F G H m n
  let a₁ := Output.actionDesc d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
    m n
  have hm : iₘ ≫ fₘ = (𝟙 (x ⟶[V] m) ⊗ₘ s) ≫ jₘ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G H m X
  have hn : iₙ ≫ fₙ = (𝟙 (x ⟶[V] n) ⊗ₘ s) ≫ jₙ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G H n X
  have h₀ : R ◁ iₘ ≫ MonoidalClosed.uncurry a₀ = Output.outputAction x m n Q ≫ iₙ :=
    right_actionDesc_generator d F G H m n X
  have h₁ : R ◁ jₘ ≫ MonoidalClosed.uncurry a₁ = Output.outputAction x m n Q' ≫ jₙ := by
    have h := congrArg MonoidalClosed.uncurry
      (Output.gen_actionDesc d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
        m n p)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] at h
    exact h
  change iₘ ≫ (a₀ ≫ (ihom R).map fₙ) = iₘ ≫ (fₘ ≫ a₁)
  apply MonoidalClosed.uncurry_injective (A := R)
  rw [MonoidalClosed.uncurry_natural_left iₘ (a₀ ≫ (ihom R).map fₙ),
    MonoidalClosed.uncurry_natural_right a₀ fₙ,
    MonoidalClosed.uncurry_natural_left iₘ (fₘ ≫ a₁),
    MonoidalClosed.uncurry_natural_left fₘ a₁]
  rw [← Category.assoc, h₀, Category.assoc, hn]
  rw [← whiskerLeft_comp_assoc, hm, whiskerLeft_comp, Category.assoc, h₁]
  simpa only [id_tensorHom, Category.assoc] using
    (outputAction_coefficient_assoc x m n s jₙ).symm

/-- Entire output-index Hom naturality of the actual right flat-to-nested map. -/
theorem right_output_natural (m n : I) :
    MonoidalClosed.uncurry ((rightOutputFunctor d F G H).map m n) ≫
        AssociatorRightFlattening.flatToNested d F G H n =
      (AssociatorRightFlattening.flatToNested d F G H m ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
        MonoidalClosed.uncurry
          ((Output.functor d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
            H)).map m n) := by
  let R : V := m ⟶[V] n
  let fₘ := AssociatorRightFlattening.flatToNested d F G H m
  let fₙ := AssociatorRightFlattening.flatToNested d F G H n
  let M : R ⟶ (ihom (AssociatorFlat.rightPoint d F G H m)).obj
      (AssociatorFlat.rightPoint d F G H n) := (rightOutputFunctor d F G H).map m n
  let N : R ⟶ (ihom (EnrichedDayKernel.obj d.tensorEnrichedFunctor
      F (Output.functor d.tensorEnrichedFunctor G H) m)).obj
      (EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
        n) :=
    (Output.functor d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)).map m n
  let a := Output.actionDesc d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
    m n
  have hm : MonoidalClosed.uncurry M =
      (β_ R (AssociatorFlat.rightPoint d F G H m)).inv ≫
        MonoidalClosed.uncurry (rightActionDesc d F G H m n) :=
    rightOutputFunctor_map_uncurry d F G H m n
  have hn : MonoidalClosed.uncurry N =
      (β_ R (EnrichedDayKernel.obj d.tensorEnrichedFunctor
        F (Output.functor d.tensorEnrichedFunctor G H) m)).inv ≫ MonoidalClosed.uncurry a :=
    Output.map_uncurry d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m n
  have h := congrArg (MonoidalClosed.uncurry (A := R))
    (right_actionDesc_natural d F G H m n)
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left] at h
  change MonoidalClosed.uncurry M ≫ fₙ = (fₘ ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry N
  rw [hm, hn, Category.assoc, h]
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun t => t ≫ MonoidalClosed.uncurry a)
      (BraidedCategory.braiding_inv_naturality_left fₘ R).symm

end RightOutput

section LeftCoefficientInputs

variable [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C × D) K)
  {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}
  {H H' : EnrichedFunctor V E V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')
  (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H')
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F' G' k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F' G' k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F' G' k) (EnrichedDayKernel.rightMap T F' G'
    k)]

/-- All three genuine transformations commute with the actual left coefficient map. -/
theorem leftCoefficientMap_input (X : (C × D) × E) :
    (eHomEquiv V).symm ((EnrichedFunctor.externalMap (EnrichedFunctor.externalMap a b) c).app X) ≫
        AssociatorTensor.leftCoefficientMap T F' G' H' X =
      AssociatorTensor.leftCoefficientMap T F G H X ≫
        (eHomEquiv V).symm ((EnrichedFunctor.externalMap (Input.natTrans T a b) c).app
          ((prodEnrichedFunctor T (EnrichedFunctor.id V E)).obj X)) := by
  rw [EnrichedFunctor.externalMap_component, EnrichedFunctor.externalMap_component,
    EnrichedFunctor.externalMap_component, Input.natTrans_component]
  let s : F.obj X.1.1 ⊗ G.obj X.1.2 ⟶ F'.obj X.1.1 ⊗ G'.obj X.1.2 :=
    (eHomEquiv V).symm (a.app X.1.1) ⊗ₘ (eHomEquiv V).symm (b.app X.1.2)
  let t : H.obj X.2 ⟶ H'.obj X.2 := (eHomEquiv V).symm (c.app X.2)
  let u := AssociatorUnit.unitGenerator T F G X.1
  let u' := AssociatorUnit.unitGenerator T F' G' X.1
  change (s ⊗ₘ t) ≫ (u' ⊗ₘ 𝟙 (H'.obj X.2)) =
    (u ⊗ₘ 𝟙 (H.obj X.2)) ≫ (Input.mapAt T a b (T.obj X.1) ⊗ₘ t)
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using
    congrArg (fun f => f ⊗ₘ t) (unitGenerator_input T a b X.1).symm

end LeftCoefficientInputs

section RightCoefficientInputs

variable [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (D × E) K)
  {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}
  {H H' : EnrichedFunctor V E V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')
  (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H')
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k) (EnrichedDayKernel.rightMap T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G' H' k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G' H' k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G' H' k) (EnrichedDayKernel.rightMap T G' H'
    k)]

/-- The right input transformation keeps the full original product-associator reindexing. -/
abbrev rightCoefficientInput :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (Associator.rightCoefficients F G H) (Associator.rightCoefficients F' G' H') :=
  GradedNatTrans.restrict
    (Associator.productAssociator (V := V) (A := C) (B := D) (C := E))
    (EnrichedFunctor.externalMap a (EnrichedFunctor.externalMap b c))

/-- Its ordinary components are exactly the three original input components. -/
theorem rightCoefficientInput_component (X : (C × D) × E) :
    (eHomEquiv V).symm ((rightCoefficientInput a b c).app X) =
      (eHomEquiv V).symm (a.app X.1.1) ⊗ₘ
        ((eHomEquiv V).symm (b.app X.1.2) ⊗ₘ (eHomEquiv V).symm (c.app X.2)) := by
  let P := Associator.productAssociator (V := V) (A := C) (B := D) (C := E)
  let t := EnrichedFunctor.externalMap a (EnrichedFunctor.externalMap b c)
  have h₀ : (rightCoefficientInput a b c).app X = t.app (P.obj X) :=
    GradedNatTrans.restrict_app P t X
  have h₁ : (eHomEquiv V).symm (t.app (P.obj X)) =
      (eHomEquiv V).symm (a.app X.1.1) ⊗ₘ
        ((eHomEquiv V).symm (b.app X.1.2) ⊗ₘ (eHomEquiv V).symm (c.app X.2)) := by
    have h := EnrichedFunctor.externalMap_component a (EnrichedFunctor.externalMap b c)
      (X.1.1, (X.1.2, X.2))
    rw [EnrichedFunctor.externalMap_component b c] at h
    exact h
  exact (congrArg (eHomEquiv V).symm h₀).trans h₁

/-- All three genuine transformations commute with the actual right coefficient map. -/
theorem rightCoefficientMap_input (X : (C × D) × E) :
    (eHomEquiv V).symm ((rightCoefficientInput a b c).app X) ≫
        AssociatorRightTensor.coefficientMap T F' G' H' X =
      AssociatorRightTensor.coefficientMap T F G H X ≫
        (eHomEquiv V).symm ((EnrichedFunctor.externalMap a (Input.natTrans T b c)).app
          ((AssociatorRightTensor.product T).obj X)) := by
  rw [rightCoefficientInput_component, EnrichedFunctor.externalMap_component,
    Input.natTrans_component]
  let s : F.obj X.1.1 ⟶ F'.obj X.1.1 := (eHomEquiv V).symm (a.app X.1.1)
  let t : G.obj X.1.2 ⊗ H.obj X.2 ⟶ G'.obj X.1.2 ⊗ H'.obj X.2 :=
    (eHomEquiv V).symm (b.app X.1.2) ⊗ₘ (eHomEquiv V).symm (c.app X.2)
  let u := AssociatorUnit.unitGenerator T G H (X.1.2, X.2)
  let u' := AssociatorUnit.unitGenerator T G' H' (X.1.2, X.2)
  change (s ⊗ₘ t) ≫ (𝟙 (F'.obj X.1.1) ⊗ₘ u') =
    (𝟙 (F.obj X.1.1) ⊗ₘ u) ≫ (s ⊗ₘ Input.mapAt T b c (T.obj (X.1.2, X.2)))
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using
    congrArg (fun f => s ⊗ₘ f) (unitGenerator_input T b c (X.1.2, X.2)).symm

end RightCoefficientInputs

section LeftInputs

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)
  {F F' G G' H H' : EnrichedFunctor V I V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')
  (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H') (m : I)

attribute [local instance] Enriched.prodCategory

variable
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (AssociatorFlat.leftObjects d F' G' H' m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F' G' H' m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F' G' H' m) (AssociatorFlat.leftMap1 d F' G' H' m)]

/-- The original left flat input map is the genuine graded coend diagram map. -/
abbrev leftInputMap : AssociatorFlat.leftPoint d F G H m ⟶ AssociatorFlat.leftPoint d F' G' H' m :=
  Input.mapAt (AssociatorIndex.leftIndex d) (EnrichedFunctor.externalMap a b) c m

/-- Every left flat input generator keeps the identity weight and all three components. -/
@[reassoc]
theorem leftInputMap_generator (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ leftInputMap d a b c m =
      (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] m) ⊗ₘ
        (((eHomEquiv V).symm (a.app X.1.1) ⊗ₘ (eHomEquiv V).symm (b.app X.1.2)) ⊗ₘ
          (eHomEquiv V).symm (c.app X.2))) ≫ AssociatorFlat.leftGenerator d F' G' H' m X := by
  have h := Input.gen_mapAt (AssociatorIndex.leftIndex d) (EnrichedFunctor.externalMap a b) c m X
  rw [EnrichedFunctor.externalMap_component] at h
  exact h

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F' G' k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F' G' k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F' G' k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F' G' k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F' G') H' m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F' G') H' m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F' G') H' m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F'
      G') H' m)]


/-- Joint naturality in all three genuine input transformations for the actual left map. -/
theorem left_input_natural :
    leftInputMap d a b c m ≫ AssociatorFlattening.flatToNested d F' G' H' m =
      AssociatorFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a b) c m := by
  exact map_diagram_natural (AssociatorTensor.leftProduct d)
    (AssociatorIndex.leftWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.leftCoefficients F G H) (Associator.leftCoefficients F' G' H')
    ((Output.functor d.tensorEnrichedFunctor F G).externalTensor H)
    ((Output.functor d.tensorEnrichedFunctor F' G').externalTensor H')
    (AssociatorTensor.leftWeightMap d m)
    (fun X => AssociatorTensor.leftCoefficientMap d.tensorEnrichedFunctor F G H X)
    (fun X => AssociatorTensor.leftCoefficientMap d.tensorEnrichedFunctor F' G' H' X)
    (AssociatorTensor.leftWeightMap_naturality d m)
    (AssociatorTensor.leftCoefficientMap_naturality d.tensorEnrichedFunctor F G H)
    (AssociatorTensor.leftCoefficientMap_naturality d.tensorEnrichedFunctor F' G' H')
    (EnrichedFunctor.externalMap (EnrichedFunctor.externalMap a b) c)
    (EnrichedFunctor.externalMap (Input.natTrans d.tensorEnrichedFunctor a b) c)
    (leftCoefficientMap_input d.tensorEnrichedFunctor a b c)

end LeftInputs

section RightInputs

variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)
  {F F' G G' H H' : EnrichedFunctor V I V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')
  (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H') (m : I)

attribute [local instance] Enriched.prodCategory

variable
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (AssociatorFlat.rightObjects d F' G' H' m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F' G' H' m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F' G' H' m) (AssociatorFlat.rightMap1 d F' G' H' m)]

/-- The original right flat input map descends its full product-reindexed transformation. -/
abbrev rightInputMap : AssociatorFlat.rightPoint d F G H m ⟶ AssociatorFlat.rightPoint d F' G' H' m
  :=
  Enriched.weightedCoend.mapDiagramGraded (AssociatorIndex.rightWeight d m) (rightCoefficientInput a
    b c)

/-- Every right flat input generator retains its original right word and all three components. -/
@[reassoc]
theorem rightInputMap_generator (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ rightInputMap d a b c m =
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] m) ⊗ₘ
        ((eHomEquiv V).symm (a.app X.1.1) ⊗ₘ
          ((eHomEquiv V).symm (b.app X.1.2) ⊗ₘ (eHomEquiv V).symm (c.app X.2)))) ≫
        AssociatorFlat.rightGenerator d F' G' H' m X := by
  have h := Enriched.weightedCoend.mapDiagramGraded_ι (AssociatorIndex.rightWeight d m)
    (rightCoefficientInput a b c) X
  rw [rightCoefficientInput_component] at h
  exact h

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G' H' k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G' H' k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G' H' k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G' H' k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F (Output.functor d.tensorEnrichedFunctor G H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    F' (Output.functor d.tensorEnrichedFunctor G' H') m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    F' (Output.functor d.tensorEnrichedFunctor G' H') m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    F' (Output.functor d.tensorEnrichedFunctor G' H') m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F' (Output.functor d.tensorEnrichedFunctor
      G' H') m)]


/-- Joint naturality in all three genuine input transformations for the actual right map. -/
theorem right_input_natural :
    rightInputMap d a b c m ≫ AssociatorRightFlattening.flatToNested d F' G' H' m =
      AssociatorRightFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor b c) m := by
  exact map_diagram_natural (AssociatorRightTensor.product d.tensorEnrichedFunctor)
    (AssociatorIndex.rightWeight d m) (weight d.tensorEnrichedFunctor m)
    (Associator.rightCoefficients F G H) (Associator.rightCoefficients F' G' H')
    (F.externalTensor (Output.functor d.tensorEnrichedFunctor G H))
    (F'.externalTensor (Output.functor d.tensorEnrichedFunctor G' H'))
    (AssociatorRightTensor.weightMap d m)
    (fun X => AssociatorRightTensor.coefficientMap d.tensorEnrichedFunctor F G H X)
    (fun X => AssociatorRightTensor.coefficientMap d.tensorEnrichedFunctor F' G' H' X)
    (AssociatorRightTensor.weightMap_naturality d m)
    (AssociatorRightTensor.coefficientMap_naturality d.tensorEnrichedFunctor F G H)
    (AssociatorRightTensor.coefficientMap_naturality d.tensorEnrichedFunctor F' G' H')
    (rightCoefficientInput a b c)
    (EnrichedFunctor.externalMap a (Input.natTrans d.tensorEnrichedFunctor b c))
    (rightCoefficientMap_input d.tensorEnrichedFunctor a b c)

end RightInputs

section IndividualInputs
variable [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

/-- Naturality of the actual left comparison in the first genuine input. -/
theorem left_input_natural_first (F F' G H : EnrichedFunctor V I V)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F' G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F' G k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F' G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F' G k)]
    [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
      (AssociatorFlat.leftMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.leftObjects d F' G H m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F' G H m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F' G H m)
      (AssociatorFlat.leftMap1 d F' G H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
        G) H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F' G) H m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F' G) H m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F' G) H m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F'
        G) H m)]
    :
    leftInputMap d a (GradedNatTrans.unitId G) (GradedNatTrans.unitId H) m ≫
      AssociatorFlattening.flatToNested d F' G H m =
      AssociatorFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a
          (GradedNatTrans.unitId G)) (GradedNatTrans.unitId H) m :=
  left_input_natural d a (GradedNatTrans.unitId G) (GradedNatTrans.unitId H) m

/-- Naturality of the actual left comparison in the second genuine input. -/
theorem left_input_natural_second (F G G' H : EnrichedFunctor V I V)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G' k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G' k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G' k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G' k)]
    [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
      (AssociatorFlat.leftMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.leftObjects d F G' H m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F G' H m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F G' H m)
      (AssociatorFlat.leftMap1 d F G' H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
        G) H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G') H m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G') H m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G') H m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
        G') H m)]
    :
    leftInputMap d (GradedNatTrans.unitId F) b (GradedNatTrans.unitId H) m ≫
      AssociatorFlattening.flatToNested d F G' H m =
      AssociatorFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor
          (GradedNatTrans.unitId F) b) (GradedNatTrans.unitId H) m :=
  left_input_natural d (GradedNatTrans.unitId F) b (GradedNatTrans.unitId H) m

/-- Naturality of the actual left comparison in the third genuine input. -/
theorem left_input_natural_third (F G H H' : EnrichedFunctor V I V)
    (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
    [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
      (AssociatorFlat.leftMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.leftObjects d F G H' m)]
    [HasCoproduct (AssociatorFlat.leftRelations d F G H' m)]
    [HasCoequalizer (AssociatorFlat.leftMap0 d F G H' m)
      (AssociatorFlat.leftMap1 d F G H' m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
        G) H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H' m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H' m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor
      d.tensorEnrichedFunctor F G) H' m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
        G) H' m)]
    :
    leftInputMap d (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) c m ≫
      AssociatorFlattening.flatToNested d F G H' m =
      AssociatorFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor
          (GradedNatTrans.unitId F) (GradedNatTrans.unitId G)) c m :=
  left_input_natural d (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) c m

/-- Naturality of the actual right comparison in the first genuine input. -/
theorem right_input_natural_first (F F' G H : EnrichedFunctor V I V)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
    [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
      (AssociatorFlat.rightMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.rightObjects d F' G H m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F' G H m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F' G H m)
      (AssociatorFlat.rightMap1 d F' G H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
        G H) m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F' (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F' (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F' (Output.functor
      d.tensorEnrichedFunctor G H) m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F' (Output.functor d.tensorEnrichedFunctor
        G H) m)]
    :
    rightInputMap d a (GradedNatTrans.unitId G) (GradedNatTrans.unitId H) m ≫
      AssociatorRightFlattening.flatToNested d F' G H m =
      AssociatorRightFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor
          (GradedNatTrans.unitId G) (GradedNatTrans.unitId H)) m :=
  right_input_natural d a (GradedNatTrans.unitId G) (GradedNatTrans.unitId H) m

/-- Naturality of the actual right comparison in the second genuine input. -/
theorem right_input_natural_second (F G G' H : EnrichedFunctor V I V)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G' H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G' H k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G' H k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G' H k)]
    [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
      (AssociatorFlat.rightMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.rightObjects d F G' H m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F G' H m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F G' H m)
      (AssociatorFlat.rightMap1 d F G' H m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
        G H) m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G' H) m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G' H) m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G' H) m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
        G' H) m)]
    :
    rightInputMap d (GradedNatTrans.unitId F) b (GradedNatTrans.unitId H) m ≫
      AssociatorRightFlattening.flatToNested d F G' H m =
      AssociatorRightFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Input.natTrans
          d.tensorEnrichedFunctor b (GradedNatTrans.unitId H)) m :=
  right_input_natural d (GradedNatTrans.unitId F) b (GradedNatTrans.unitId H) m

/-- Naturality of the actual right comparison in the third genuine input. -/
theorem right_input_natural_third (F G H H' : EnrichedFunctor V I V)
    (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H') (m : I)
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H' k)]
    [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H' k)]
    [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H' k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H' k)]
    [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
      (AssociatorFlat.rightMap1 d F G H m)]
    [HasCoproduct (AssociatorFlat.rightObjects d F G H' m)]
    [HasCoproduct (AssociatorFlat.rightRelations d F G H' m)]
    [HasCoequalizer (AssociatorFlat.rightMap0 d F G H' m)
      (AssociatorFlat.rightMap1 d F G H' m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H) m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
        G H) m)]
    [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H') m)]
    [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H') m)]
    [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor
      d.tensorEnrichedFunctor G H') m)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
        G H') m)]
    :
    rightInputMap d (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) c m ≫
      AssociatorRightFlattening.flatToNested d F G H' m =
      AssociatorRightFlattening.flatToNested d F G H m ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F) (Input.natTrans
          d.tensorEnrichedFunctor (GradedNatTrans.unitId G) c) m :=
  right_input_natural d (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) c m

end IndividualInputs
end CategoryTheory.EnrichedDayKernel.AssociatorNaturality
