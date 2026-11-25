/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison

/-!
# Associator Quad Coend Map

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI uA uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadMaps
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
attribute [local instance] Enriched.prodCategory

omit [SymmetricCategory V] [MonoidalClosed V] [EnrichedCategory V A] [EnrichedCategory V B] in
/-- The actual complete enriched Hom congruences preserve the original enriched composition. -/
@[reassoc]
theorem composition_congr {X Y Z X' Y' Z' : I} (a : X ≅ X') (b : Y ≅ Y') (c : Z ≅ Z') :
    eComp V X Y Z ≫ (Iso.eHomCongr V a c).hom =
      ((Iso.eHomCongr V a b).hom ⊗ₘ (Iso.eHomCongr V b c).hom) ≫ eComp V X' Y' Z' := by
  simp only [Iso.eHomCongr, tensorHom_def, Category.assoc]
  rw [eComp_eHomWhiskerRight_assoc, eComp_eHomWhiskerLeft]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [← eComp_eHomWhiskerLeft]
  rw [eHom_whisker_cancel_assoc, eComp_eHomWhiskerLeft]

variable (L R : EnrichedFunctor V (A × B) I) (e : ∀ X, L.obj X ≅ R.obj X)
  (h : ∀ X Y, R.map X Y = L.map X Y ≫ (Iso.eHomCongr V (e X) (e Y)).hom) (m : I)

/-- Transport the represented weight along the index comparison, retaining the identity
  of the represented target `m`. -/
abbrev weightIso (X : A × B) : (weight L m).obj (op X) ≅ (weight R m).obj (op X) :=
  Iso.eHomCongr V (e X) (Iso.refl m)

include h in
/-- An actual full index map congruence yields the original representable weight naturality. -/
@[reassoc]
theorem weight_naturality (X Y : A × B) :
    MonoidalClosed.uncurry ((weight L m).map (op Y) (op X)) ≫ (weightIso L R e m X).hom =
      ((weightIso L R e m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight R m).map (op Y) (op X)) := by
  rw [weight_uncurry_map, weight_uncurry_map]
  let LX := L.obj X
  let LY := L.obj Y
  let RX := R.obj X
  let RY := R.obj Y
  let P : V := X ⟶[V] Y
  let W : V := LY ⟶[V] m
  let W' : V := RY ⟶[V] m
  let l : P ⟶ (LX ⟶[V] LY) := L.map X Y
  let r : P ⟶ (RX ⟶[V] RY) := R.map X Y
  let qX : (LX ⟶[V] m) ≅ (RX ⟶[V] m) := weightIso L R e m X
  let qY : W ≅ W' := weightIso L R e m Y
  let qXY : (LX ⟶[V] LY) ≅ (RX ⟶[V] RY) := Iso.eHomCongr V (e X) (e Y)
  change (W ◁ l ≫ (β_ W (LX ⟶[V] LY)).hom ≫ eComp V LX LY m) ≫ qX.hom =
    (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫ (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY m
  simp only [Category.assoc]
  have hc : eComp V LX LY m ≫ qX.hom = (qXY.hom ⊗ₘ qY.hom) ≫ eComp V RX RY m :=
    composition_congr (e X) (e Y) (Iso.refl m)
  have hm : r = l ≫ qXY.hom := h X Y
  have hr : (qY.hom ⊗ₘ 𝟙 P) ≫ W' ◁ r ≫ (β_ W' (RX ⟶[V] RY)).hom ≫ eComp V RX RY m =
      (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY m := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
    exact BraidedCategory.braiding_naturality_assoc qY.hom r (eComp V RX RY m)
  calc
    _ = (β_ W P).hom ≫ (l ⊗ₘ 𝟙 W) ≫ eComp V LX LY m ≫ qX.hom := by
      simpa only [id_tensorHom, Category.assoc] using
        BraidedCategory.braiding_naturality_assoc (𝟙 W) l (eComp V LX LY m ≫ qX.hom)
    _ = (β_ W P).hom ≫ ((l ≫ qXY.hom) ⊗ₘ qY.hom) ≫ eComp V RX RY m := by
      rw [hc]
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (β_ W P).hom ≫ (r ⊗ₘ qY.hom) ≫ eComp V RX RY m := by rw [← hm]
    _ = _ := hr.symm

omit [Category I] [EnrichedOrdinaryCategory V I] [EnrichedCategory V B] [SymmetricCategory V] in
/-- A constructed full coefficient Hom congruence gives full uncurried coefficient naturality. -/
@[reassoc]
theorem coefficient_naturality (Q Q' : EnrichedFunctor V A V)
    (q : ∀ X, Q.obj X ≅ Q'.obj X)
    (hq : ∀ X Y, Q'.map X Y = Q.map X Y ≫ (Iso.eHomCongr V (q X) (q Y)).hom) (X Y : A) :
    MonoidalClosed.uncurry (Q.map X Y) ≫ (q Y).hom =
      ((q X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (Q'.map X Y) := by
  have hp : Q.map X Y ≫ eHomWhiskerLeft V (Q.obj X) (q Y).hom =
      Q'.map X Y ≫ eHomWhiskerRight V (q X).hom (Q'.obj Y) := by
    rw [hq X Y]
    simp only [Iso.eHomCongr, Category.assoc]
    rw [← eHom_whisker_exchange_assoc, ← eHomWhiskerRight_comp,
      Iso.hom_inv_id, eHomWhiskerRight_id, Category.comp_id]
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at hp
  have hu := congrArg MonoidalClosed.uncurry hp
  simp only [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app] at hu
  rw [tensorHom_id]
  exact hu

end CategoryTheory.EnrichedDayKernel.AssociatorQuadMaps
