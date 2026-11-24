/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorReconstructionNaturality
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMappedPoint

/-!
# Entire original reverse operator generator balance

The genuine sphere transformation supplies every coefficient. Its original
source naturality and the genuine I-space co-Yoneda composition identify the
two relation faces on every Hom unit point. The actual unit separator then
gives balance on the complete original continuous Hom object. The spectrum,
sphere and operator-weight factors remain entire.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.Reconstruction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

private theorem generator_square (M C₀ C₁ W₀ W₁ Y₀ Y₁ Z : V)
    (f : C₀ ⟶ C₁) (g : Y₀ ⟶ Y₁) (w : W₁ ⟶ W₀)
    (c₀ : M ⊗ C₀ ⟶ Y₀) (c₁ : M ⊗ C₁ ⟶ Y₁)
    (e₀ : Y₀ ⊗ W₀ ⟶ Z) (e₁ : Y₁ ⊗ W₁ ⟶ Z)
    (hCoefficient : (M ◁ f) ≫ c₁ = c₀ ≫ g)
    (hEvaluation : (Y₀ ◁ w) ≫ e₀ = (g ▷ W₁) ≫ e₁) :
    (M ◁ (w ⊗ₘ 𝟙 C₀)) ≫ (M ◁ (β_ W₀ C₀).hom) ≫
        (α_ M C₀ W₀).inv ≫ (c₀ ▷ W₀) ≫ e₀ =
      (M ◁ (𝟙 W₁ ⊗ₘ f)) ≫ (M ◁ (β_ W₁ C₁).hom) ≫
        (α_ M C₁ W₁).inv ≫ (c₁ ▷ W₁) ≫ e₁ := by
  have hBW : (w ▷ C₀) ≫ (β_ W₀ C₀).hom =
      (β_ W₁ C₀).hom ≫ (C₀ ◁ w) := by
    simpa only [tensorHom_id, id_tensorHom] using braiding_naturality w (𝟙 C₀)
  have hAW : (M ◁ (C₀ ◁ w)) ≫ (α_ M C₀ W₀).inv =
      (α_ M C₀ W₁).inv ≫ ((M ⊗ C₀) ◁ w) := by
    simpa only [id_tensorHom, id_tensorHom_id, whiskerLeft_id] using
      associator_inv_naturality (𝟙 M) (𝟙 C₀) w
  have hExchange : ((M ⊗ C₀) ◁ w) ≫ (c₀ ▷ W₀) =
      (c₀ ▷ W₁) ≫ (Y₀ ◁ w) :=
    (tensorHom_def' c₀ w).symm.trans (tensorHom_def c₀ w)
  have hLeft : (M ◁ (w ⊗ₘ 𝟙 C₀)) ≫ (M ◁ (β_ W₀ C₀).hom) ≫
      (α_ M C₀ W₀).inv ≫ (c₀ ▷ W₀) =
        (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫ (c₀ ▷ W₁) ≫ (Y₀ ◁ w) := by
    calc
      _ = (M ◁ ((w ▷ C₀) ≫ (β_ W₀ C₀).hom)) ≫
          (α_ M C₀ W₀).inv ≫ (c₀ ▷ W₀) := by
        simp only [tensorHom_id, whiskerLeft_comp, Category.assoc]
      _ = (M ◁ ((β_ W₁ C₀).hom ≫ C₀ ◁ w)) ≫
          (α_ M C₀ W₀).inv ≫ (c₀ ▷ W₀) :=
        congrArg (fun q => (M ◁ q) ≫ (α_ M C₀ W₀).inv ≫ (c₀ ▷ W₀)) hBW
      _ = (M ◁ (β_ W₁ C₀).hom) ≫
          ((M ◁ (C₀ ◁ w)) ≫ (α_ M C₀ W₀).inv) ≫ (c₀ ▷ W₀) := by
        simp only [whiskerLeft_comp, Category.assoc]
      _ = (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫
          ((M ⊗ C₀) ◁ w) ≫ (c₀ ▷ W₀) := by
        simpa only [Category.assoc] using congrArg
          (fun q => (M ◁ (β_ W₁ C₀).hom) ≫ q ≫ (c₀ ▷ W₀)) hAW
      _ = _ := by rw [hExchange]
  have hBC : (W₁ ◁ f) ≫ (β_ W₁ C₁).hom =
      (β_ W₁ C₀).hom ≫ (f ▷ W₁) := by
    simpa only [tensorHom_id, id_tensorHom] using braiding_naturality (𝟙 W₁) f
  have hAC : (M ◁ (f ▷ W₁)) ≫ (α_ M C₁ W₁).inv =
      (α_ M C₀ W₁).inv ≫ ((M ◁ f) ▷ W₁) := by
    simpa only [id_tensorHom, tensorHom_id] using
      associator_inv_naturality (𝟙 M) f (𝟙 W₁)
  have hRight : (M ◁ (𝟙 W₁ ⊗ₘ f)) ≫ (M ◁ (β_ W₁ C₁).hom) ≫
      (α_ M C₁ W₁).inv =
        (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫ ((M ◁ f) ▷ W₁) := by
    calc
      _ = M ◁ ((W₁ ◁ f) ≫ (β_ W₁ C₁).hom) ≫ (α_ M C₁ W₁).inv := by
        simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
      _ = M ◁ ((β_ W₁ C₀).hom ≫ (f ▷ W₁)) ≫ (α_ M C₁ W₁).inv :=
        congrArg (fun q => (M ◁ q) ≫ (α_ M C₁ W₁).inv) hBC
      _ = (M ◁ (β_ W₁ C₀).hom) ≫
          ((M ◁ (f ▷ W₁)) ≫ (α_ M C₁ W₁).inv) := by
        simp only [whiskerLeft_comp, Category.assoc]
      _ = _ := congrArg (fun q => (M ◁ (β_ W₁ C₀).hom) ≫ q) hAC
  have hCoefficientW : (c₀ ▷ W₁) ≫ (g ▷ W₁) =
      ((M ◁ f) ▷ W₁) ≫ (c₁ ▷ W₁) := by
    simpa only [comp_whiskerRight] using congrArg (fun q => q ▷ W₁) hCoefficient.symm
  calc
    _ = (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫
        (c₀ ▷ W₁) ≫ (Y₀ ◁ w) ≫ e₀ := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ e₀) hLeft
    _ = (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫
        (c₀ ▷ W₁) ≫ (g ▷ W₁) ≫ e₁ := by rw [hEvaluation]
    _ = (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫
        ((M ◁ f) ▷ W₁) ≫ (c₁ ▷ W₁) ≫ e₁ := by
      simpa only [Category.assoc] using congrArg
        (fun q => (M ◁ (β_ W₁ C₀).hom) ≫ (α_ M C₀ W₁).inv ≫ q ≫ e₁) hCoefficientW
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun q => q ≫ (c₁ ▷ W₁) ≫ e₁) hRight).symm

variable [MonoidalClosed V]
  {C : Type uI} [Category.{vI} C] [EnrichedOrdinaryCategory V C]

private theorem coyoneda_point_precompose (X : EnrichedFunctor V C V)
    {a b : C} (f : a ⟶ b) (k : C) :
    (((ρ_ (b ⟶[V] k)).inv ≫ (b ⟶[V] k) ◁ eHomEquiv V f ≫
        (β_ (b ⟶[V] k) (a ⟶[V] b)).hom ≫ eComp V a b k) ⊗ₘ 𝟙 (X.obj a)) ≫
        (β_ (a ⟶[V] k) (X.obj a)).hom ≫ MonoidalClosed.uncurry (X.map a k) =
      (𝟙 (b ⟶[V] k) ⊗ₘ X.toOrdinaryFunctor.map f) ≫
        (β_ (b ⟶[V] k) (X.obj b)).hom ≫ MonoidalClosed.uncurry (X.map b k) := by
  let U : V := b ⟶[V] k
  let U' : V := a ⟶[V] k
  let H : V := a ⟶[V] b
  let r := (β_ U H).hom ≫ eComp V a b k
  let s := MonoidalClosed.uncurry (X.map a b)
  let ta := (β_ U' (X.obj a)).hom ≫ MonoidalClosed.uncurry (X.map a k)
  let tb := (β_ U (X.obj b)).hom ≫ MonoidalClosed.uncurry (X.map b k)
  have hFull : ((α_ U H (X.obj a)).inv ≫ (r ⊗ₘ 𝟙 (X.obj a))) ≫ ta =
      (U ◁ ((β_ H (X.obj a)).hom ≫ s)) ≫ tb :=
    Enriched.weightedCoend.coyonedaCondition X k a b
  have hPoint := Enriched.weightedCoend.Mapped.relation_unitPoint
    U U' (X.obj a) (X.obj b) H (X.obj k) r s ta tb hFull (eHomEquiv V f)
  have hXMap : eHomEquiv V f ≫ X.map a b = eHomEquiv V (X.toOrdinaryFunctor.map f) :=
    (EnrichedFunctor.toOrdinaryFunctor_map X f).symm
  have hXPoint : (X.obj a ◁ eHomEquiv V f) ≫ s =
      (ρ_ (X.obj a)).hom ≫ X.toOrdinaryFunctor.map f :=
    uncurry_unitPoint (eHomEquiv V f) (X.map a b) (X.toOrdinaryFunctor.map f) hXMap
  have hX : (ρ_ (X.obj a)).inv ≫ X.obj a ◁ eHomEquiv V f ≫ s =
      X.toOrdinaryFunctor.map f :=
    (congrArg (fun q => (ρ_ (X.obj a)).inv ≫ q) hXPoint).trans
      (Iso.inv_hom_id_assoc (ρ_ (X.obj a)) (X.toOrdinaryFunctor.map f))
  have hRight := congrArg (fun q => (𝟙 U ⊗ₘ q) ≫ tb) hX
  exact hPoint.trans hRight

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S X : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
  (X.externalTensor S) (d.tensorEnrichedFunctor.comp V X))

/-- Every entire original operator relation is respected by the reconstructed generator. -/
theorem generator_balanced (hU : IsSeparator (𝟙_ V)) (n k : I) :
    Enriched.weightedCoend.Mapped.Balanced (weight d n k) S (tensorLeft (X.obj n))
      (generator d S X t n k) := by
  apply Enriched.weightedCoend.Mapped.balanced_of_unitPoints (weight d n k) S hU
  intro a b p
  let f : a ⟶ b := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := Equiv.apply_symm_apply _ p
  let U : V := (b ⊗ n) ⟶[V] k
  let U' : V := (a ⊗ n) ⟶[V] k
  let H : V := (a ⊗ n) ⟶[V] (b ⊗ n)
  let wa : U ⟶ U' := (ρ_ U).inv ≫ U ◁ p ≫
    MonoidalClosed.uncurry ((weight d n k).map (op b) (op a))
  let fa := (ρ_ (S.obj a)).inv ≫ S.obj a ◁ p ≫ MonoidalClosed.uncurry (S.map a b)
  let xs : S.obj a ⟶ S.obj b := S.toOrdinaryFunctor.map f
  let xy : X.obj (a ⊗ n) ⟶ X.obj (b ⊗ n) := X.toOrdinaryFunctor.map (f ▷ n)
  let ea := MonoidalClosed.uncurry (X.map (a ⊗ n) k)
  let eb := MonoidalClosed.uncurry (X.map (b ⊗ n) k)
  have hFixed : p ≫ (fixedRightTensor d n).map a b = eHomEquiv V (f ▷ n) := by
    have h := fixedRightTensor_point d n f
    rw [hp] at h
    exact h
  have hWeightMap :
      MonoidalClosed.uncurry ((weight d n k).map (op b) (op a)) =
        (U ◁ (fixedRightTensor d n).map a b) ≫ (β_ U H).hom ≫ eComp V (a ⊗ n) (b ⊗ n) k :=
    weight_uncurry_map d n k a b
  have hPrefix : (U ◁ p) ≫ (U ◁ (fixedRightTensor d n).map a b) =
      U ◁ eHomEquiv V (f ▷ n) :=
    (whiskerLeft_comp U p ((fixedRightTensor d n).map a b)).symm.trans
      (congrArg (fun q => U ◁ q) hFixed)
  have hWeight : wa = (ρ_ U).inv ≫ U ◁ eHomEquiv V (f ▷ n) ≫
      (β_ U H).hom ≫ eComp V (a ⊗ n) (b ⊗ n) k := by
    have h₁ := congrArg (fun q => (ρ_ U).inv ≫ U ◁ p ≫ q) hWeightMap
    have h₂ := congrArg (fun q => (ρ_ U).inv ≫ q ≫
      (β_ U H).hom ≫ eComp V (a ⊗ n) (b ⊗ n) k) hPrefix
    have hAssoc : (ρ_ U).inv ≫ (U ◁ p) ≫
        (U ◁ (fixedRightTensor d n).map a b) ≫ (β_ U H).hom ≫
          eComp V (a ⊗ n) (b ⊗ n) k =
      (ρ_ U).inv ≫ ((U ◁ p) ≫ (U ◁ (fixedRightTensor d n).map a b)) ≫
        (β_ U H).hom ≫ eComp V (a ⊗ n) (b ⊗ n) k :=
      congrArg (fun q => (ρ_ U).inv ≫ q)
        (Category.assoc (U ◁ p) (U ◁ (fixedRightTensor d n).map a b)
          ((β_ U H).hom ≫ eComp V (a ⊗ n) (b ⊗ n) k)).symm
    exact h₁.trans (hAssoc.trans h₂)
  have hAction : (wa ⊗ₘ 𝟙 (X.obj (a ⊗ n))) ≫
      (β_ U' (X.obj (a ⊗ n))).hom ≫ ea =
        (𝟙 U ⊗ₘ xy) ≫ (β_ U (X.obj (b ⊗ n))).hom ≫ eb :=
    (congrArg (fun q => (q ⊗ₘ 𝟙 (X.obj (a ⊗ n))) ≫
      (β_ U' (X.obj (a ⊗ n))).hom ≫ ea) hWeight).trans
        (coyoneda_point_precompose X (f ▷ n) k)
  have hEvaluation : (X.obj (a ⊗ n) ◁ wa) ≫ ea = (xy ▷ U) ≫ eb := by
    apply (cancel_epi (β_ U (X.obj (a ⊗ n))).hom).1
    have hLeftBeta : (wa ⊗ₘ 𝟙 (X.obj (a ⊗ n))) ≫
        (β_ U' (X.obj (a ⊗ n))).hom =
      (β_ U (X.obj (a ⊗ n))).hom ≫ (X.obj (a ⊗ n) ◁ wa) :=
      (braiding_naturality wa (𝟙 (X.obj (a ⊗ n)))).trans
        (congrArg (fun q => (β_ U (X.obj (a ⊗ n))).hom ≫ q)
          (id_tensorHom (X.obj (a ⊗ n)) wa))
    have hRightBeta : (𝟙 U ⊗ₘ xy) ≫ (β_ U (X.obj (b ⊗ n))).hom =
        (β_ U (X.obj (a ⊗ n))).hom ≫ (xy ▷ U) :=
      (braiding_naturality (𝟙 U) xy).trans
        (congrArg (fun q => (β_ U (X.obj (a ⊗ n))).hom ≫ q) (tensorHom_id xy U))
    have hLeft' : (β_ U (X.obj (a ⊗ n))).hom ≫ (X.obj (a ⊗ n) ◁ wa) ≫ ea =
        (wa ⊗ₘ 𝟙 (X.obj (a ⊗ n))) ≫ (β_ U' (X.obj (a ⊗ n))).hom ≫ ea :=
      (Category.assoc (β_ U (X.obj (a ⊗ n))).hom (X.obj (a ⊗ n) ◁ wa) ea).symm.trans
        ((congrArg (fun q => q ≫ ea) hLeftBeta.symm).trans
          (Category.assoc (wa ⊗ₘ 𝟙 (X.obj (a ⊗ n)))
            (β_ U' (X.obj (a ⊗ n))).hom ea))
    have hRight' : (β_ U (X.obj (a ⊗ n))).hom ≫ (xy ▷ U) ≫ eb =
        (𝟙 U ⊗ₘ xy) ≫ (β_ U (X.obj (b ⊗ n))).hom ≫ eb :=
      (Category.assoc (β_ U (X.obj (a ⊗ n))).hom (xy ▷ U) eb).symm.trans
        ((congrArg (fun q => q ≫ eb) hRightBeta.symm).trans
          (Category.assoc (𝟙 U ⊗ₘ xy) (β_ U (X.obj (b ⊗ n))).hom eb))
    exact hLeft'.trans (hAction.trans hRight'.symm)
  have hCoefficient : (X.obj n ◁ xs) ≫ coefficient d S X t n b =
      coefficient d S X t n a ≫ xy :=
    (coefficient_natural d S X t n a b f).trans
      (congrArg (fun q => coefficient d S X t n a ≫ X.toOrdinaryFunctor.map q)
        (tensorHom_id f n))
  have hSMap : p ≫ S.map a b = eHomEquiv V xs := by
    have h := EnrichedFunctor.toOrdinaryFunctor_map S f
    rw [hp] at h
    exact h.symm
  have hSPoint : (S.obj a ◁ p) ≫ MonoidalClosed.uncurry (S.map a b) =
      (ρ_ (S.obj a)).hom ≫ xs :=
    uncurry_unitPoint p (S.map a b) xs hSMap
  have hS : fa = xs :=
    (congrArg (fun q => (ρ_ (S.obj a)).inv ≫ q) hSPoint).trans
      (Iso.inv_hom_id_assoc (ρ_ (S.obj a)) xs)
  have hSquare := generator_square (X.obj n) (S.obj a) (S.obj b) U' U
    (X.obj (a ⊗ n)) (X.obj (b ⊗ n)) (X.obj k) xs xy wa
    (coefficient d S X t n a) (coefficient d S X t n b) ea eb hCoefficient hEvaluation
  have hRight := congrArg (fun q => (X.obj n ◁ (𝟙 U ⊗ₘ q)) ≫ generator d S X t n k b) hS
  exact hSquare.trans hRight.symm

end CategoryTheory.Enriched.SphereOperator.Reconstruction
