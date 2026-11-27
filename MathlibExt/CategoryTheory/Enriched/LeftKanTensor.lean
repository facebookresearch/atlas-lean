/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.LeftKanGradedAction
public import MathlibExt.CategoryTheory.Enriched.GradedTensor

/-!
# Left Kan extension commutes with the actual left tensor diagram

Both comparison maps use the original unit and the proved central-grade
Hom correspondence. Only the original foreach-X Lan coends are used.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private def leftKanTensorUnitMap (M : V) (X : EnrichedFunctorCat V A) :
    tensorLeftObject M X ⟶ restrictionObject j (tensorLeftObject M (leftKanObject j X)) :=
  tensorLeftMap M (leftKanUnit j X) ≫ (tensorLeftRestrictionIso M j (leftKanObject j X)).hom

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorUnitMap_component (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    component (leftKanTensorUnitMap j M X) a = M ◁ leftKanUnitComponent j X a := by
  have h0 := component_comp (tensorLeftMap M (leftKanUnit j X))
    (tensorLeftRestrictionIso M j (leftKanObject j X)).hom a
  have h1 := tensorLeftMap_component M (leftKanUnit j X) a
  have h2 := tensorLeftRestrictionIso_hom_component M j (leftKanObject j X) a
  have h : component (leftKanTensorUnitMap j M X) a =
      (M ◁ component (leftKanUnit j X) a) ≫
        𝟙 (M ⊗ (leftKanObject j X).toEnrichedFunctor.obj (j.obj a)) :=
    h0.trans (congrArg₂ (fun p q => p ≫ q) h1 h2)
  exact h.trans ((Category.comp_id _).trans
    (congrArg (fun p => M ◁ p) (leftKanUnit_component j X a)))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The forward comparison is the original ordinary Lan transpose of the tensored unit. -/
@[no_expose]
def leftKanTensorHom (M : V) (X : EnrichedFunctorCat V A) :
    leftKanObject j (tensorLeftObject M X) ⟶ tensorLeftObject M (leftKanObject j X) :=
  (leftKanHomEquiv j (tensorLeftObject M X) (tensorLeftObject M (leftKanObject j X))).symm
    (leftKanTensorUnitMap j M X)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorHom_unit_private (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    leftKanUnitComponent j (tensorLeftObject M X) a ≫
        component (leftKanTensorHom j M X) (j.obj a) = M ◁ leftKanUnitComponent j X a := by
  let P := leftKanTensorUnitMap j M X
  let H := leftKanTensorHom j M X
  have hE : leftKanHomEquiv j (tensorLeftObject M X)
      (tensorLeftObject M (leftKanObject j X)) H = P :=
    (leftKanHomEquiv j (tensorLeftObject M X)
      (tensorLeftObject M (leftKanObject j X))).apply_symm_apply P
  have hC : component (leftKanHomEquiv j (tensorLeftObject M X)
      (tensorLeftObject M (leftKanObject j X)) H) a =
        leftKanUnitComponent j (tensorLeftObject M X) a ≫ component H (j.obj a) :=
    (congrArg (fun p => component p a)
      (leftKanHomEquiv_apply j (tensorLeftObject M X)
        (tensorLeftObject M (leftKanObject j X)) H)).trans
      (leftKanHomToRestriction_component j (tensorLeftObject M X)
        (tensorLeftObject M (leftKanObject j X)) H a)
  exact hC.symm.trans ((congrArg (fun p => component p a) hE).trans
    (leftKanTensorUnitMap_component j M X a))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The actual unit characteristic determines the forward tensor comparison. -/
theorem leftKanTensorHom_unit (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    leftKanUnitComponent j (tensorLeftObject M X) a ≫
        component (leftKanTensorHom j M X) (j.obj a) = M ◁ leftKanUnitComponent j X a :=
  leftKanTensorHom_unit_private j M X a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The inverse comparison is the original graded Lan inverse applied to the
actual tensored-source unit. -/
@[no_expose]
def leftKanTensorInv (M : V) (X : EnrichedFunctorCat V A) :
    tensorLeftObject M (leftKanObject j X) ⟶ leftKanObject j (tensorLeftObject M X) :=
  gradedTensorToUnit ((Center.ofBraided V).obj M)
    ((leftKanGradedHomEquiv j ((Center.ofBraided V).obj M) X
      (leftKanObject j (tensorLeftObject M X))).symm
        (gradedTensorOfUnit ((Center.ofBraided V).obj M)
          (leftKanUnit j (tensorLeftObject M X))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorInv_unit_private (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    (M ◁ leftKanUnitComponent j X a) ≫ component (leftKanTensorInv j M X) (j.obj a) =
      leftKanUnitComponent j (tensorLeftObject M X) a := by
  let Γ := (Center.ofBraided V).obj M
  let Y := leftKanObject j (tensorLeftObject M X)
  let f := gradedTensorOfUnit Γ (leftKanUnit j (tensorLeftObject M X))
  let t := (leftKanGradedHomEquiv j Γ X Y).symm f
  have h0 : component (leftKanTensorInv j M X) (j.obj a) =
      GradedNatTrans.gradeFirstComponent Γ t (j.obj a) :=
    gradedTensorToUnit_component Γ t (j.obj a)
  have h1 : (M ◁ leftKanUnitComponent j X a) ≫
      GradedNatTrans.gradeFirstComponent Γ t (j.obj a) =
        GradedNatTrans.gradeFirstComponent Γ f a :=
    (leftKanGradedHomEquiv_gradeFirstComponent j Γ X Y t a).symm.trans
      (congrArg (fun p => GradedNatTrans.gradeFirstComponent Γ p a)
        ((leftKanGradedHomEquiv j Γ X Y).apply_symm_apply f))
  have h2 : GradedNatTrans.gradeFirstComponent Γ f a =
      leftKanUnitComponent j (tensorLeftObject M X) a :=
    (gradedTensorOfUnit_gradeFirstComponent Γ (leftKanUnit j (tensorLeftObject M X)) a).trans
      (leftKanUnit_component j (tensorLeftObject M X) a)
  exact (congrArg (fun p => (M ◁ leftKanUnitComponent j X a) ≫ p) h0).trans (h1.trans h2)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The inverse keeps the original restricted-unit characteristic in its full parameter. -/
theorem leftKanTensorInv_unit (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    (M ◁ leftKanUnitComponent j X a) ≫ component (leftKanTensorInv j M X) (j.obj a) =
      leftKanUnitComponent j (tensorLeftObject M X) a :=
  leftKanTensorInv_unit_private j M X a

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorHom_inv (M : V) (X : EnrichedFunctorCat V A) :
    leftKanTensorHom j M X ≫ leftKanTensorInv j M X =
      𝟙 (leftKanObject j (tensorLeftObject M X)) := by
  apply (leftKanHomEquiv j (tensorLeftObject M X)
    (leftKanObject j (tensorLeftObject M X))).injective
  apply hom_ext
  intro a
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply,
    leftKanHomToRestriction_component, leftKanHomToRestriction_component,
    component_comp, component_id]
  change leftKanUnitComponent j (tensorLeftObject M X) a ≫
      (component (leftKanTensorHom j M X) (j.obj a) ≫
        component (leftKanTensorInv j M X) (j.obj a)) =
    leftKanUnitComponent j (tensorLeftObject M X) a ≫
      𝟙 ((leftKanObject j (tensorLeftObject M X)).toEnrichedFunctor.obj (j.obj a))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun p => p ≫ component (leftKanTensorInv j M X) (j.obj a))
      (leftKanTensorHom_unit j M X a)).trans
        ((leftKanTensorInv_unit j M X a).trans (Category.comp_id _).symm))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorInv_hom (M : V) (X : EnrichedFunctorCat V A) :
    leftKanTensorInv j M X ≫ leftKanTensorHom j M X =
      𝟙 (tensorLeftObject M (leftKanObject j X)) := by
  let Γ := (Center.ofBraided V).obj M
  let Y := tensorLeftObject M (leftKanObject j X)
  let s := leftKanTensorInv j M X ≫ leftKanTensorHom j M X
  have ht : gradedTensorOfUnit Γ s = gradedTensorOfUnit Γ (𝟙 Y) := by
    apply (leftKanGradedHomEquiv j Γ X Y).injective
    apply GradedNatTrans.gradeFirstComponent_ext Γ
    intro a
    have h1 := leftKanGradedHomEquiv_gradeFirstComponent j Γ X Y (gradedTensorOfUnit Γ s) a
    have h2 := leftKanGradedHomEquiv_gradeFirstComponent j Γ X Y (gradedTensorOfUnit Γ (𝟙 Y)) a
    have h3 := congrArg (fun p => (M ◁ leftKanUnitComponent j X a) ≫ p)
      (gradedTensorOfUnit_gradeFirstComponent Γ s (j.obj a))
    have h4 := congrArg (fun p => (M ◁ leftKanUnitComponent j X a) ≫ p)
      (gradedTensorOfUnit_gradeFirstComponent Γ (𝟙 Y) (j.obj a))
    have hp : (M ◁ leftKanUnitComponent j X a) ≫ component s (j.obj a) =
        (M ◁ leftKanUnitComponent j X a) ≫ component (𝟙 Y) (j.obj a) := by
      rw [component_comp, component_id]
      change (M ◁ leftKanUnitComponent j X a) ≫
          (component (leftKanTensorInv j M X) (j.obj a) ≫
            component (leftKanTensorHom j M X) (j.obj a)) =
        (M ◁ leftKanUnitComponent j X a) ≫
          𝟙 (M ⊗ (leftKanObject j X).toEnrichedFunctor.obj (j.obj a))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun p => p ≫ component (leftKanTensorHom j M X) (j.obj a))
          (leftKanTensorInv_unit j M X a)).trans
            ((leftKanTensorHom_unit j M X a).trans (Category.comp_id _).symm))
    exact h1.trans (h3.trans (hp.trans (h4.symm.trans h2.symm)))
  apply hom_ext
  intro b
  have h := congrArg (fun p => GradedNatTrans.gradeFirstComponent Γ p b) ht
  exact (gradedTensorOfUnit_gradeFirstComponent Γ s b).symm.trans
    (h.trans (gradedTensorOfUnit_gradeFirstComponent Γ (𝟙 Y) b))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The actual comparison is an isomorphism of genuine enriched diagrams. -/
@[no_expose]
def leftKanTensorIso (M : V) (X : EnrichedFunctorCat V A) :
    leftKanObject j (tensorLeftObject M X) ≅ tensorLeftObject M (leftKanObject j X) where
  hom := leftKanTensorHom j M X
  inv := leftKanTensorInv j M X
  hom_inv_id := leftKanTensorHom_inv j M X
  inv_hom_id := leftKanTensorInv_hom j M X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorIso_hom_private (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorIso j M X).hom = leftKanTensorHom j M X := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorIso_inv_private (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorIso j M X).inv = leftKanTensorInv j M X := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorIso_hom (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorIso j M X).hom = leftKanTensorHom j M X :=
  leftKanTensorIso_hom_private j M X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorIso_inv (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorIso j M X).inv = leftKanTensorInv j M X :=
  leftKanTensorIso_inv_private j M X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
omit [MonoidalClosed V] in
private def leftKanTensorWeightSwap (M W Z : V) : W ⊗ (M ⊗ Z) ≅ M ⊗ (W ⊗ Z) :=
  (α_ W M Z).symm ≪≫ whiskerRightIso (β_ W M) Z ≪≫ α_ M W Z

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
omit [MonoidalClosed V] in
private theorem leftKanTensorWeightSwap_hom (M W Z : V) :
    (leftKanTensorWeightSwap M W Z).hom =
      (α_ W M Z).inv ≫ ((β_ W M).hom ▷ Z) ≫ (α_ M W Z).hom := by
  simp only [leftKanTensorWeightSwap, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
omit [MonoidalClosed V] in
private theorem leftKanTensorWeightSwap_inv (M W Z : V) :
    (leftKanTensorWeightSwap M W Z).inv =
      (α_ M W Z).inv ≫ ((β_ W M).inv ▷ Z) ≫ (α_ W M Z).hom := by
  simp only [leftKanTensorWeightSwap, Iso.trans_inv, Iso.symm_inv,
    whiskerRightIso_inv, Category.assoc]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorUnit_generator
    (X : EnrichedFunctorCat V A) (a : A) (b : B) :
    ((j.obj a ⟶[V] b) ◁ leftKanUnitComponent j X a) ≫
        (β_ (j.obj a ⟶[V] b) (leftKanCoendObject j X.toEnrichedFunctor (j.obj a))).hom ≫
        MonoidalClosed.uncurry (leftKanCoendMap j X.toEnrichedFunctor (j.obj a) b) =
      Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a := by
  rw [leftKanCoendMap_uncurry]
  simp only [Iso.hom_inv_id_assoc]
  exact leftKanUnitComponent_action j X a b

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The inverse tensor comparison descends the original generator with the inverse ambient braid. -/
theorem leftKanTensorInv_ι (M : V) (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    (M ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        component (leftKanTensorInv j M X) b =
      (α_ M (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) M).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) M (X.toEnrichedFunctor.obj a)).hom ≫
        Enriched.weightedCoend.ι (leftKanWeight j b)
          (tensorLeftObject M X).toEnrichedFunctor a := by
  let Γ := (Center.ofBraided V).obj M
  let T := tensorLeftObject M X
  let Y := leftKanObject j T
  let f := gradedTensorOfUnit Γ (leftKanUnit j T)
  let t := (leftKanGradedHomEquiv j Γ X Y).symm f
  let W := (j.obj a ⟶[V] b)
  have h0 := congrArg (fun q => (M ◁ Enriched.weightedCoend.ι (leftKanWeight j b)
      X.toEnrichedFunctor a) ≫ q) (gradedTensorToUnit_component Γ t b)
  have h1 := leftKanGradedHomEquiv_symm_gradeFirstComponent_ι j Γ X Y f b a
  have hη : GradedNatTrans.gradeFirstComponent Γ f a = leftKanUnitComponent j T a :=
    (gradedTensorOfUnit_gradeFirstComponent Γ (leftKanUnit j T) a).trans
      (leftKanUnit_component j T a)
  have htail : (W ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫
      (β_ W (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) =
        Enriched.weightedCoend.ι (leftKanWeight j b) T.toEnrichedFunctor a :=
    (congrArg (fun q => (W ◁ q) ≫ (β_ W (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b)) hη).trans
        (leftKanTensorUnit_generator j T a b)
  exact h0.trans (h1.trans (congrArg (fun q =>
    (α_ M W (X.toEnrichedFunctor.obj a)).inv ≫
      ((β_ W M).inv ▷ X.toEnrichedFunctor.obj a) ≫
      (α_ W M (X.toEnrichedFunctor.obj a)).hom ≫ q) htail))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The forward comparison uses the positive ambient weight braid on the original
tensor generator. -/
theorem leftKanTensorHom_ι (M : V) (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) (tensorLeftObject M X).toEnrichedFunctor a ≫
        component (leftKanTensorHom j M X) b =
      (α_ (j.obj a ⟶[V] b) M (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) M).hom ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ M (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).hom ≫
        (M ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) := by
  let W := (j.obj a ⟶[V] b)
  let σ := leftKanTensorWeightSwap M W (X.toEnrichedFunctor.obj a)
  let i := Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a
  let iT := Enriched.weightedCoend.ι (leftKanWeight j b) (tensorLeftObject M X).toEnrichedFunctor a
  let h := component (leftKanTensorHom j M X) b
  let g := component (leftKanTensorInv j M X) b
  have hσ : σ.inv ≫ iT =
      (α_ M W (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ W M).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ W M (X.toEnrichedFunctor.obj a)).hom ≫ iT :=
    (congrArg (fun q => q ≫ iT) (leftKanTensorWeightSwap_inv M W (X.toEnrichedFunctor.obj a))).trans
      ((Category.assoc (α_ M W (X.toEnrichedFunctor.obj a)).inv
        (((β_ W M).inv ▷ X.toEnrichedFunctor.obj a) ≫ (α_ W M (X.toEnrichedFunctor.obj a)).hom)
        iT).trans (congrArg (fun q => (α_ M W (X.toEnrichedFunctor.obj a)).inv ≫ q)
          (Category.assoc ((β_ W M).inv ▷ X.toEnrichedFunctor.obj a)
            (α_ W M (X.toEnrichedFunctor.obj a)).hom iT)))
  have hg : (M ◁ i) ≫ g = σ.inv ≫ iT :=
    (leftKanTensorInv_ι j M X b a).trans hσ.symm
  have hs : (σ.hom ≫ (M ◁ i)) ≫ g = iT :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => σ.hom ≫ q) hg).trans (σ.hom_inv_id_assoc iT))
  have hgh : g ≫ h = 𝟙 (M ⊗ (leftKanObject j X).toEnrichedFunctor.obj b) :=
    (component_comp (leftKanTensorInv j M X) (leftKanTensorHom j M X) b).symm.trans
      ((congrArg (fun q => component q b) (leftKanTensorInv_hom j M X)).trans
        (component_id (tensorLeftObject M (leftKanObject j X)) b))
  have hc : ((σ.hom ≫ (M ◁ i)) ≫ g) ≫ h = σ.hom ≫ (M ◁ i) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => (σ.hom ≫ (M ◁ i)) ≫ q) hgh).trans (Category.comp_id _))
  have hp : iT ≫ h = σ.hom ≫ (M ◁ i) :=
    (congrArg (fun q => q ≫ h) hs).symm.trans hc
  exact hp.trans ((congrArg (fun q => q ≫ (M ◁ i)) (leftKanTensorWeightSwap_hom M W
    (X.toEnrichedFunctor.obj a))).trans
      ((Category.assoc (α_ W M (X.toEnrichedFunctor.obj a)).inv
        (((β_ W M).hom ▷ X.toEnrichedFunctor.obj a) ≫ (α_ M W (X.toEnrichedFunctor.obj a)).hom)
        (M ◁ i)).trans (congrArg (fun q => (α_ W M (X.toEnrichedFunctor.obj a)).inv ≫ q)
          (Category.assoc ((β_ W M).hom ▷ X.toEnrichedFunctor.obj a)
            (α_ M W (X.toEnrichedFunctor.obj a)).hom (M ◁ i)))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorUnit_naturalComponent
    {X X' : EnrichedFunctorCat V A} (p : X ⟶ X') (a : A) :
    component p a ≫ leftKanUnitComponent j X' a =
      leftKanUnitComponent j X a ≫ component ((leftKan j).map p) (j.obj a) := by
  have h := congrArg (fun q => component q a) (leftKanUnit_natural j p)
  rw [component_comp, component_comp, leftKanUnit_component,
    leftKanUnit_component, restrictionMap_component] at h
  exact h

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The forward tensor comparison is natural in the original full enriched diagram map. -/
theorem leftKanTensorHom_naturality (M : V) {X X' : EnrichedFunctorCat V A} (p : X ⟶ X') :
    (leftKan j).map (tensorLeftMap M p) ≫ leftKanTensorHom j M X' =
      leftKanTensorHom j M X ≫ tensorLeftMap M ((leftKan j).map p) := by
  apply (leftKanHomEquiv j (tensorLeftObject M X)
    (tensorLeftObject M (leftKanObject j X'))).injective
  apply hom_ext
  intro a
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply,
    leftKanHomToRestriction_component, leftKanHomToRestriction_component,
    component_comp, component_comp, tensorLeftMap_component]
  have hT := leftKanTensorUnit_naturalComponent j (tensorLeftMap M p) a
  have hX := leftKanTensorUnit_naturalComponent j p a
  have hTc : (M ◁ component p a) ≫ leftKanUnitComponent j (tensorLeftObject M X') a =
      leftKanUnitComponent j (tensorLeftObject M X) a ≫
        component ((leftKan j).map (tensorLeftMap M p)) (j.obj a) :=
    (congrArg (fun q => q ≫ leftKanUnitComponent j (tensorLeftObject M X') a)
      (tensorLeftMap_component M p a)).symm.trans hT
  have h0 := (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ component (leftKanTensorHom j M X') (j.obj a)) hTc.symm)
  have h1 := (Category.assoc _ _ _).trans
    (congrArg (fun q => (M ◁ component p a) ≫ q) (leftKanTensorHom_unit j M X' a))
  have h2 := (whiskerLeft_comp M (component p a) (leftKanUnitComponent j X' a)).symm
  have h3 := congrArg (fun q => M ◁ q) hX
  have h4 := whiskerLeft_comp M (leftKanUnitComponent j X a)
    (component ((leftKan j).map p) (j.obj a))
  have h5 := congrArg (fun q => q ≫ (M ◁ component ((leftKan j).map p) (j.obj a)))
    (leftKanTensorHom_unit j M X a).symm
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (Category.assoc _ _ _))))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The forward tensor comparison is natural in every actual coefficient map. -/
theorem leftKanTensorHom_scalar_naturality {M N : V} (u : M ⟶ N) (X : EnrichedFunctorCat V A) :
    (leftKan j).map (scalarTensorMap u X) ≫ leftKanTensorHom j N X =
      leftKanTensorHom j M X ≫ scalarTensorMap u (leftKanObject j X) := by
  apply (leftKanHomEquiv j (tensorLeftObject M X)
    (tensorLeftObject N (leftKanObject j X))).injective
  apply hom_ext
  intro a
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply,
    leftKanHomToRestriction_component, leftKanHomToRestriction_component,
    component_comp, component_comp, scalarTensorMap_component]
  have hT := leftKanTensorUnit_naturalComponent j (scalarTensorMap u X) a
  have hTc : (u ▷ X.toEnrichedFunctor.obj a) ≫ leftKanUnitComponent j (tensorLeftObject N X) a =
      leftKanUnitComponent j (tensorLeftObject M X) a ≫
        component ((leftKan j).map (scalarTensorMap u X)) (j.obj a) :=
    (congrArg (fun q => q ≫ leftKanUnitComponent j (tensorLeftObject N X) a)
      (scalarTensorMap_component u X a)).symm.trans hT
  have h0 := (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ component (leftKanTensorHom j N X) (j.obj a)) hTc.symm)
  have h1 := (Category.assoc _ _ _).trans
    (congrArg (fun q => (u ▷ X.toEnrichedFunctor.obj a) ≫ q) (leftKanTensorHom_unit j N X a))
  have h2 := (whisker_exchange u (leftKanUnitComponent j X a)).symm
  have h3 := congrArg (fun q => q ≫ (u ▷ (leftKanObject j X).toEnrichedFunctor.obj (j.obj a)))
    (leftKanTensorHom_unit j M X a).symm
  exact h0.trans (h1.trans (h2.trans (h3.trans (Category.assoc _ _ _))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorIso_inverse_square
    {P P' Q Q' : EnrichedFunctorCat V B} (i : P ≅ Q) (i' : P' ≅ Q')
    (l : P ⟶ P') (r : Q ⟶ Q') (h : l ≫ i'.hom = i.hom ≫ r) :
    r ≫ i'.inv = i.inv ≫ l := by
  have h0 := congrArg (fun q => i.inv ≫ q) h
  have h1 : (i.inv ≫ l) ≫ i'.hom = r :=
    (Category.assoc _ _ _).trans (h0.trans (i.inv_hom_id_assoc r))
  exact i'.comp_inv_eq.mpr h1.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The inverse tensor comparison is natural in every original diagram map. -/
theorem leftKanTensorInv_naturality (M : V) {X X' : EnrichedFunctorCat V A} (p : X ⟶ X') :
    tensorLeftMap M ((leftKan j).map p) ≫ leftKanTensorInv j M X' =
      leftKanTensorInv j M X ≫ (leftKan j).map (tensorLeftMap M p) := by
  let i := leftKanTensorIso j M X
  let i' := leftKanTensorIso j M X'
  let l := (leftKan j).map (tensorLeftMap M p)
  let r := tensorLeftMap M ((leftKan j).map p)
  have h : l ≫ i'.hom = i.hom ≫ r :=
    (congrArg (fun q => l ≫ q) (leftKanTensorIso_hom j M X')).trans
      ((leftKanTensorHom_naturality j M p).trans
        (congrArg (fun q => q ≫ r) (leftKanTensorIso_hom j M X)).symm)
  exact (congrArg (fun q => r ≫ q) (leftKanTensorIso_inv j M X')).symm.trans
    ((leftKanTensorIso_inverse_square i i' l r h).trans
      (congrArg (fun q => q ≫ l) (leftKanTensorIso_inv j M X)))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The inverse tensor comparison is natural in every actual coefficient map. -/
theorem leftKanTensorInv_scalar_naturality {M N : V} (u : M ⟶ N) (X : EnrichedFunctorCat V A) :
    scalarTensorMap u (leftKanObject j X) ≫ leftKanTensorInv j N X =
      leftKanTensorInv j M X ≫ (leftKan j).map (scalarTensorMap u X) := by
  let i := leftKanTensorIso j M X
  let i' := leftKanTensorIso j N X
  let l := (leftKan j).map (scalarTensorMap u X)
  let r := scalarTensorMap u (leftKanObject j X)
  have h : l ≫ i'.hom = i.hom ≫ r :=
    (congrArg (fun q => l ≫ q) (leftKanTensorIso_hom j N X)).trans
      ((leftKanTensorHom_scalar_naturality j u X).trans
        (congrArg (fun q => q ≫ r) (leftKanTensorIso_hom j M X)).symm)
  exact (congrArg (fun q => r ≫ q) (leftKanTensorIso_inv j N X)).symm.trans
    ((leftKanTensorIso_inverse_square i i' l r h).trans
      (congrArg (fun q => q ≫ l) (leftKanTensorIso_inv j M X)))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Actual tensoring before and after Lan are naturally isomorphic on the original
enriched diagram category. -/
@[no_expose]
def leftKanTensorNatIso (M : V) : tensorLeft M ⋙ leftKan j ≅ leftKan j ⋙ tensorLeft M :=
  NatIso.ofComponents (fun X => leftKanTensorIso j M X) (by
    intro X X' p
    exact (congrArg (fun q => (leftKan j).map (tensorLeftMap M p) ≫ q)
      (leftKanTensorIso_hom j M X')).trans
        ((leftKanTensorHom_naturality j M p).trans
          (congrArg (fun q => q ≫ tensorLeftMap M ((leftKan j).map p))
            (leftKanTensorIso_hom j M X)).symm))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorNatIso_hom_app_private (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorNatIso j M).hom.app X = leftKanTensorHom j M X := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanTensorNatIso_inv_app_private (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorNatIso j M).inv.app X = leftKanTensorInv j M X := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorNatIso_hom_app (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorNatIso j M).hom.app X = leftKanTensorHom j M X :=
  leftKanTensorNatIso_hom_app_private j M X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanTensorNatIso_inv_app (M : V) (X : EnrichedFunctorCat V A) :
    (leftKanTensorNatIso j M).inv.app X = leftKanTensorInv j M X :=
  leftKanTensorNatIso_inv_app_private j M X

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Every complete central-graded Lan map is the actual tensor comparison followed
by Lan of its tensor transform. -/
theorem leftKanTensorInv_gradedMap
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    gradedTensorToUnit Γ (leftKanGradedMap j Γ t) =
      leftKanTensorInv j Γ.1 X ≫ (leftKan j).map (gradedTensorToUnit Γ t) := by
  let M := Γ.1
  let p := gradedTensorToUnit Γ t
  let s := leftKanTensorInv j M X ≫ (leftKan j).map p
  have hs : leftKanGradedMap j Γ t = gradedTensorOfUnit Γ s := by
    apply (leftKanGradedHomEquiv j Γ X (leftKanObject j X')).injective
    apply GradedNatTrans.gradeFirstComponent_ext Γ
    intro a
    have h0 := congrArg (fun q => GradedNatTrans.gradeFirstComponent Γ q a)
      (leftKanGradedMap_homEquiv j Γ t)
    have h1 := gradeFirstComponent_gradedPostcomp Γ t (leftKanUnit j X') a
    have h2 := congrArg (fun q => GradedNatTrans.gradeFirstComponent Γ t a ≫ q)
      (leftKanUnit_component j X' a)
    have h3 := congrArg (fun q => q ≫ leftKanUnitComponent j X' a)
      (gradedTensorToUnit_component Γ t a)
    have h4 := leftKanTensorUnit_naturalComponent j p a
    have h5 := congrArg (fun q => q ≫ component ((leftKan j).map p) (j.obj a))
      (leftKanTensorInv_unit j M X a).symm
    have h6 := Category.assoc (M ◁ leftKanUnitComponent j X a)
      (component (leftKanTensorInv j M X) (j.obj a)) (component ((leftKan j).map p) (j.obj a))
    have h7 := congrArg (fun q => (M ◁ leftKanUnitComponent j X a) ≫ q)
      (component_comp (leftKanTensorInv j M X) ((leftKan j).map p) (j.obj a)).symm
    have h8 := congrArg (fun q => (M ◁ leftKanUnitComponent j X a) ≫ q)
      (gradedTensorOfUnit_gradeFirstComponent Γ s (j.obj a)).symm
    have h9 := (leftKanGradedHomEquiv_gradeFirstComponent j Γ X (leftKanObject j X')
      (gradedTensorOfUnit Γ s) a).symm
    exact h0.trans (h1.trans (h2.trans (h3.symm.trans (h4.trans
      (h5.trans (h6.trans (h7.trans (h8.trans h9))))))))
  apply hom_ext
  intro b
  exact (gradedTensorToUnit_component Γ (leftKanGradedMap j Γ t) b).trans
    ((congrArg (fun q => GradedNatTrans.gradeFirstComponent Γ q b) hs).trans
      (gradedTensorOfUnit_gradeFirstComponent Γ s b))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The forward tensor comparison gives the converse exact tensor-transform
factorization for every central grade. -/
theorem leftKanTensorHom_gradedMap
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanTensorHom j Γ.1 X ≫ gradedTensorToUnit Γ (leftKanGradedMap j Γ t) =
      (leftKan j).map (gradedTensorToUnit Γ t) := by
  have h0 := congrArg (fun q => leftKanTensorHom j Γ.1 X ≫ q)
    (leftKanTensorInv_gradedMap j Γ t)
  have h1 := (Category.assoc (leftKanTensorHom j Γ.1 X) (leftKanTensorInv j Γ.1 X)
    ((leftKan j).map (gradedTensorToUnit Γ t))).symm
  have h2 := congrArg (fun q => q ≫ (leftKan j).map (gradedTensorToUnit Γ t))
    (leftKanTensorHom_inv j Γ.1 X)
  exact h0.trans (h1.trans (h2.trans (Category.id_comp _)))

end CategoryTheory.EnrichedFunctorCat
