/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorCoefficients

/-!
# The original index associator and the triple Day weights

The full enriched index associator carries the left triple weight to the
right triple weight by precomposition with its actual inverse.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uI vI uA uD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorIndex

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

/-- The original left index functor, including its stored full tensor Hom map. -/
abbrev leftIndex : EnrichedFunctor V ((I × I) × I) I :=
  (fun {F G : EnrichedFunctor V ((I × I) × I) I}
    (_ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) => F) d.associatorGraded

/-- The original right index functor, including the full Hom-object reassociation. -/
abbrev rightIndex : EnrichedFunctor V ((I × I) × I) I :=
  (fun {F G : EnrichedFunctor V ((I × I) × I) I}
    (_ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) => G) d.associatorGraded

/-- The left index uses the actual left-associated index tensor. -/
@[simp]
theorem leftIndex_obj (X : (I × I) × I) :
    (leftIndex d).obj X = (X.1.1 ⊗ X.1.2) ⊗ X.2 := rfl

/-- The right index uses the actual right-associated index tensor. -/
@[simp]
theorem rightIndex_obj (X : (I × I) × I) :
    (rightIndex d).obj X = X.1.1 ⊗ (X.1.2 ⊗ X.2) := rfl

/-- Both successive full index tensor maps are retained on the left. -/
theorem leftIndex_map (X Y : (I × I) × I) :
    (leftIndex d).map X Y =
      (d.tensorMap X.1.1 Y.1.1 X.1.2 Y.1.2 ⊗ₘ 𝟙 (X.2 ⟶[V] Y.2)) ≫
        d.tensorMap (X.1.1 ⊗ X.1.2) (Y.1.1 ⊗ Y.1.2) X.2 Y.2 := rfl

/-- The original full right index Hom map includes the actual Hom associator. -/
theorem rightIndex_map (X Y : (I × I) × I) :
    (rightIndex d).map X Y =
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (X.1.1 ⟶[V] Y.1.1) ◁ d.tensorMap X.1.2 Y.1.2 X.2 Y.2 ≫
        d.tensorMap X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2) := rfl

/-- The original full unit-graded index associator. -/
abbrev indexAssociator :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (leftIndex d) (rightIndex d) :=
  d.associatorGraded

/-- Every component is the actual index associator. -/
theorem indexAssociator_app (X : (I × I) × I) :
    (indexAssociator d).app X = eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom :=
  d.associatorGraded_app X

/-- The original index square determines the entire right triple Hom map. -/
theorem indexMap_congr (X Y : (I × I) × I) :
    (rightIndex d).map X Y = (leftIndex d).map X Y ≫
      (Iso.eHomCongr V (α_ X.1.1 X.1.2 X.2) (α_ Y.1.1 Y.1.2 Y.2)).hom := by
  have hn : ∀ X Y : (I × I) × I,
      (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          ((leftIndex d).map X Y ⊗ₘ eHomEquiv V (α_ Y.1.1 Y.1.2 Y.2).hom) ≫
          eComp V ((leftIndex d).obj X) ((leftIndex d).obj Y) ((rightIndex d).obj Y) =
        (eHomEquiv V (α_ X.1.1 X.1.2 X.2).hom ⊗ₘ (rightIndex d).map X Y) ≫
          eComp V ((leftIndex d).obj X) ((rightIndex d).obj X)
            ((rightIndex d).obj Y) := by
    intro X Y
    have h := (indexAssociator d).naturality X Y
    dsimp only [leftIndex, rightIndex, indexAssociator, EnrichedFunctor.comp,
      EnrichedMonoidalCategoryData.tensorEnrichedFunctor] at h ⊢
    simpa only [EnrichedMonoidalCategoryData.associatorGraded_app,
      Center.ofBraided, Center.ofBraidedObj] using h
  exact EnrichedFunctor.ofRawIsoComponents_map_eq (leftIndex d) (rightIndex d).obj
    (rightIndex d).map (fun X => α_ X.1.1 X.1.2 X.2) hn X Y

/-- The inverse Hom congruence recovers the entire original left triple action. -/
@[reassoc]
theorem indexMap_congr_inv (X Y : (I × I) × I) :
    (rightIndex d).map X Y ≫
        (Iso.eHomCongr V (α_ X.1.1 X.1.2 X.2) (α_ Y.1.1 Y.1.2 Y.2)).inv =
      (leftIndex d).map X Y := by
  rw [indexMap_congr]
  dsimp only [leftIndex, EnrichedFunctor.comp,
    EnrichedMonoidalCategoryData.tensorEnrichedFunctor]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [MonoidalClosed V] (m : I)

/-- The original representable left triple weight. -/
abbrev leftWeight : EnrichedFunctor V ((I × I) × I)ᵒᵖ V :=
  weight (leftIndex d) m

/-- The original representable right triple weight on the same three inputs. -/
abbrev rightWeight : EnrichedFunctor V ((I × I) × I)ᵒᵖ V :=
  weight (rightIndex d) m

/-- Precomposition with the inverse index associator is the actual weight comparison. -/
def weightIso (X : (I × I) × I) :
    (leftWeight d m).obj (op X) ≅ (rightWeight d m).obj (op X) :=
  Iso.eHomCongr V (α_ X.1.1 X.1.2 X.2) (Iso.refl m)

/-- The forward weight map is the whole enriched precomposition map of the inverse associator. -/
@[simp]
theorem weightIso_hom (X : (I × I) × I) :
    (weightIso d m X).hom = eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m := by
  simp only [weightIso, Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id, Category.comp_id]
  rfl

/-- The inverse weight map is the whole enriched precomposition map of the associator. -/
@[simp]
theorem weightIso_inv (X : (I × I) × I) :
    (weightIso d m X).inv = eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m := by
  simp only [weightIso, Iso.eHomCongr, Iso.refl_inv, eHomWhiskerLeft_id, Category.comp_id]
  rfl

omit [BraidedCategory V] [MonoidalClosed V] [MonoidalCategory I] in
private theorem composition_congr {X Y Z X' Y' Z' : I}
    (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z') :
    eComp V X Y Z ≫ (Iso.eHomCongr V a c).hom =
      ((Iso.eHomCongr V a b).hom ⊗ₘ (Iso.eHomCongr V b c).hom) ≫
        eComp V X' Y' Z' := by
  simp only [Iso.eHomCongr, tensorHom_def, Category.assoc]
  rw [eComp_eHomWhiskerRight_assoc, eComp_eHomWhiskerLeft]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [← eComp_eHomWhiskerLeft]
  rw [eHom_whisker_cancel_assoc, eComp_eHomWhiskerLeft]

/-- The weight comparison preserves the complete original contravariant Hom action. -/
@[reassoc]
theorem weight_naturality (X Y : (I × I) × I) :
    MonoidalClosed.uncurry ((leftWeight d m).map (op Y) (op X)) ≫
        (weightIso d m X).hom =
      ((weightIso d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((rightWeight d m).map (op Y) (op X)) := by
  dsimp only [leftWeight, rightWeight]
  rw [weight_uncurry_map, weight_uncurry_map]
  let LX := (X.1.1 ⊗ X.1.2) ⊗ X.2
  let LY := (Y.1.1 ⊗ Y.1.2) ⊗ Y.2
  let RX := X.1.1 ⊗ (X.1.2 ⊗ X.2)
  let RY := Y.1.1 ⊗ (Y.1.2 ⊗ Y.2)
  let P : V := X ⟶[V] Y
  let W : V := LY ⟶[V] m
  let W' : V := RY ⟶[V] m
  let l : P ⟶ (LX ⟶[V] LY) := (leftIndex d).map X Y
  let r : P ⟶ (RX ⟶[V] RY) := (rightIndex d).map X Y
  let qX : (LX ⟶[V] m) ≅ (RX ⟶[V] m) := Iso.eHomCongr V (α_ X.1.1 X.1.2 X.2) (Iso.refl m)
  let qY : W ≅ W' := Iso.eHomCongr V (α_ Y.1.1 Y.1.2 Y.2) (Iso.refl m)
  let qXY : (LX ⟶[V] LY) ≅ (RX ⟶[V] RY) := Iso.eHomCongr V (α_ X.1.1 X.1.2 X.2) (α_ Y.1.1 Y.1.2 Y.2)
  change (W ◁ l ≫ (β_ W (LX ⟶[V] LY)).hom ≫ eComp V LX LY m) ≫ qX.hom =
    (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫ (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY m
  simp only [Category.assoc]
  have hc : eComp V LX LY m ≫ qX.hom =
      (qXY.hom ⊗ₘ qY.hom) ≫ eComp V RX RY m :=
    composition_congr (α_ X.1.1 X.1.2 X.2) (α_ Y.1.1 Y.1.2 Y.2) (Iso.refl m)
  have hm : r = l ≫ qXY.hom := indexMap_congr d X Y
  have hr : (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫
      (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY m =
      (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY m := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp]
    exact BraidedCategory.braiding_naturality_assoc qY.hom r (eComp V RX RY m)
  calc
    _ = (β_ W P).hom ≫ (l ⊗ₘ 𝟙 W) ≫ eComp V LX LY m ≫ qX.hom := by
      simpa only [id_tensorHom, Category.assoc] using
        BraidedCategory.braiding_naturality_assoc (𝟙 W) l (eComp V LX LY m ≫ qX.hom)
    _ = (β_ W P).hom ≫ ((l ≫ qXY.hom) ⊗ₘ qY.hom) ≫ eComp V RX RY m := by
      rw [hc]
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY m := by rw [← hm]
    _ = (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫
        (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY m := hr.symm

/-- The inverse weight comparison preserves the same complete original contravariant action. -/
@[reassoc]
theorem weight_inv_naturality (X Y : (I × I) × I) :
    MonoidalClosed.uncurry ((rightWeight d m).map (op Y) (op X)) ≫
        (weightIso d m X).inv =
      ((weightIso d m Y).inv ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((leftWeight d m).map (op Y) (op X)) := by
  apply (cancel_epi ((weightIso d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y))).1
  rw [← Category.assoc, ← weight_naturality, Category.assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, Category.comp_id, Category.id_comp, id_tensorHom_id]

end CategoryTheory.EnrichedDayKernel.AssociatorIndex
