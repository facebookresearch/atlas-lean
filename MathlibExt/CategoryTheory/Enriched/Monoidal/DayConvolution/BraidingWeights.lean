/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingIndex

/-!
# Full continuous Day weight transport by the original index braid

Precomposition with the original inverse index braid preserves the entire
contravariant Hom action. The resulting transport also retains the actual
swap map on the complete product-enriched Hom.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingWeights

section HomComposition
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]

/-- Enriched Hom congruence preserves the complete composition morphism. -/
theorem homComposition_congr {X Y Z X' Y' Z' : I}
    (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z') :
    eComp V X Y Z ≫ (Iso.eHomCongr V a c).hom =
      ((Iso.eHomCongr V a b).hom ⊗ₘ (Iso.eHomCongr V b c).hom) ≫
        eComp V X' Y' Z' := by
  simp only [Iso.eHomCongr, tensorHom_def, Category.assoc]
  rw [eComp_eHomWhiskerRight_assoc, eComp_eHomWhiskerLeft]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [← eComp_eHomWhiskerLeft]
  rw [eHom_whisker_cancel_assoc, eComp_eHomWhiskerLeft]

end HomComposition

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [BraidedCategory I]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d) (k : I)

/-- The entire weight is transported by precomposition with the original inverse braid. -/
def weightIso (X : I × I) :
    (d.tensorEnrichedFunctor.obj X ⟶[V] k) ≅ ((BraidingIndex.tensor d).obj X ⟶[V] k) :=
  Iso.eHomCongr V (β_ X.1 X.2) (Iso.refl k)

omit [MonoidalClosed V] in
/-- The weight transport is precisely original full-Hom precomposition. -/
@[simp]
theorem weightIso_hom (X : I × I) :
    (weightIso d k X).hom = eHomWhiskerRight V (β_ X.1 X.2).inv k := by
  simp only [weightIso, Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id, Category.comp_id]
  rfl

include b in
/-- The original weight action commutes with the entire index-braid transport. -/
theorem weight_naturality (X Y : I × I) :
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor k).map (op Y) (op X)) ≫
        (weightIso d k X).hom =
      ((weightIso d k Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight (BraidingIndex.tensor d) k).map (op Y) (op X)) := by
  let LX : I := X.1 ⊗ X.2
  let LY : I := Y.1 ⊗ Y.2
  let RX : I := X.2 ⊗ X.1
  let RY : I := Y.2 ⊗ Y.1
  let P : V := X ⟶[V] Y
  let W : V := LY ⟶[V] k
  let W' : V := RY ⟶[V] k
  let l : P ⟶ (LX ⟶[V] LY) := d.tensorEnrichedFunctor.map X Y
  let r : P ⟶ (RX ⟶[V] RY) := (BraidingIndex.tensor d).map X Y
  let qX : (LX ⟶[V] k) ≅ (RX ⟶[V] k) :=
    Iso.eHomCongr V (β_ X.1 X.2) (Iso.refl k)
  let qY : W ≅ W' := Iso.eHomCongr V (β_ Y.1 Y.2) (Iso.refl k)
  let qXY : (LX ⟶[V] LY) ≅ (RX ⟶[V] RY) :=
    Iso.eHomCongr V (β_ X.1 X.2) (β_ Y.1 Y.2)
  have hleft : MonoidalClosed.uncurry
      ((weight d.tensorEnrichedFunctor k).map (op Y) (op X)) =
      W ◁ l ≫ (β_ W (LX ⟶[V] LY)).hom ≫ eComp V LX LY k :=
    weight_uncurry_map d.tensorEnrichedFunctor k X Y
  have hright : MonoidalClosed.uncurry
      ((weight (BraidingIndex.tensor d) k).map (op Y) (op X)) =
      W' ◁ r ≫ (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY k :=
    weight_uncurry_map (BraidingIndex.tensor d) k X Y
  suffices h : (W ◁ l ≫ (β_ W (LX ⟶[V] LY)).hom ≫ eComp V LX LY k) ≫ qX.hom =
      (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫ (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY k by
    exact (congrArg (fun t => t ≫ qX.hom) hleft).trans
      (h.trans (congrArg (fun t => (qY.hom ⊗ₘ 𝟙 P) ≫ t) hright).symm)
  have hc : eComp V LX LY k ≫ qX.hom = (qXY.hom ⊗ₘ qY.hom) ≫ eComp V RX RY k :=
    homComposition_congr (β_ X.1 X.2) (β_ Y.1 Y.2) (Iso.refl k)
  have hm : r = l ≫ qXY.hom := BraidingIndex.indexMap_congr d b X Y
  have hr : (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫
      (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY k =
      (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY k := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp]
    exact BraidedCategory.braiding_naturality_assoc qY.hom r (eComp V RX RY k)
  calc
    _ = (β_ W P).hom ≫ (l ⊗ₘ 𝟙 W) ≫ eComp V LX LY k ≫ qX.hom := by
      simpa only [id_tensorHom, Category.assoc] using
        BraidedCategory.braiding_naturality_assoc (𝟙 W) l (eComp V LX LY k ≫ qX.hom)
    _ = (β_ W P).hom ≫ ((l ≫ qXY.hom) ⊗ₘ qY.hom) ≫ eComp V RX RY k := by
      rw [hc]
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY k := by rw [← hm]
    _ = _ := hr.symm

omit [BraidedCategory I] in
/-- The complete swapped-index weight action retains the actual swap of both Hom factors. -/
theorem weight_swap_uncurry (X Y : I × I) :
    MonoidalClosed.uncurry ((weight (BraidingIndex.tensor d) k).map (op Y) (op X)) =
      ((Y.2 ⊗ Y.1) ⟶[V] k) ◁ (BraidingIndex.swap (V := V)).map X Y ≫
        MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor k).map
          (op (Y.2, Y.1)) (op (X.2, X.1))) := by
  let s := (BraidingIndex.swap (V := V)).map X Y
  let t := d.tensorEnrichedFunctor.map (X.2, X.1) (Y.2, Y.1)
  let c := (EnrichedFunctor.contravariantRepresentable V I k).map
    (op (d.tensorEnrichedFunctor.obj (Y.2, Y.1)))
    (op (d.tensorEnrichedFunctor.obj (X.2, X.1)))
  have hmap : (weight (BraidingIndex.tensor d) k).map (op Y) (op X) =
      s ≫ (weight d.tensorEnrichedFunctor k).map (op (Y.2, Y.1)) (op (X.2, X.1)) :=
    Category.assoc s t c
  exact (congrArg MonoidalClosed.uncurry hmap).trans
    (MonoidalClosed.uncurry_natural_left s
      ((weight d.tensorEnrichedFunctor k).map (op (Y.2, Y.1)) (op (X.2, X.1))))

include b in
/-- Both entire coend weight faces commute with the original index and value braids. -/
theorem transport_weight_naturality (X Y : I × I) :
    MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor k).map (op Y) (op X)) ≫
        (weightIso d k X).hom =
      ((weightIso d k Y).hom ⊗ₘ (BraidingIndex.swap (V := V)).map X Y) ≫
        MonoidalClosed.uncurry ((weight d.tensorEnrichedFunctor k).map
          (op (Y.2, Y.1)) (op (X.2, X.1))) := by
  let P : V := X ⟶[V] Y
  let Q : V := (X.2, X.1) ⟶[V] (Y.2, Y.1)
  let W : V := (Y.1 ⊗ Y.2) ⟶[V] k
  let W' : V := (Y.2 ⊗ Y.1) ⟶[V] k
  let w : W ⟶ W' := (weightIso d k Y).hom
  let s : P ⟶ Q := (BraidingIndex.swap (V := V)).map X Y
  let r : W' ⊗ Q ⟶ ((X.2 ⊗ X.1) ⟶[V] k) := MonoidalClosed.uncurry
    ((weight d.tensorEnrichedFunctor k).map (op (Y.2, Y.1)) (op (X.2, X.1)))
  have hs : MonoidalClosed.uncurry ((weight (BraidingIndex.tensor d) k).map (op Y) (op X)) =
      W' ◁ s ≫ r := weight_swap_uncurry d k X Y
  have ht : (w ⊗ₘ 𝟙 P) ≫ W' ◁ s = w ⊗ₘ s := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have h := weight_naturality d b k X Y
  have h' := congrArg (fun t => (w ⊗ₘ 𝟙 P) ≫ t) hs
  have h'' := congrArg (fun t => t ≫ r) ht
  exact h.trans (h'.trans
    ((Category.assoc (w ⊗ₘ 𝟙 P) (W' ◁ s) r).symm.trans h''))

end CategoryTheory.EnrichedDayKernel.BraidingWeights
