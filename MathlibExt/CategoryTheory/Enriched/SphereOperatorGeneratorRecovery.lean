/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionRecovery
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Entire original operator recovery from right sphere and index actions

The source generator keeps the entire index Hom and coefficient. Its action
is reconstructed from the original right sphere action and restricted full
index Hom action. The tensor unit separator tests the index parameter while
retaining all spectrum and coefficient values. The original mapped coend
recovers the whole operator Hom map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

private theorem coefficientPoint_reorder (X H A : V) (p : 𝟙_ V ⟶ H) :
    (X ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) ≫
      (X ◁ (β_ H A).hom) ≫ (α_ X A H).inv =
        (ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p := by
  let i : A ⟶ H ⊗ A := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  have hB : i ≫ (β_ H A).hom = (ρ_ A).inv ≫ A ◁ p := by
    dsimp only [i]
    rw [tensorHom_id, Category.assoc, BraidedCategory.braiding_naturality_left,
      braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (X ◁ i) ≫ (X ◁ (β_ H A).hom) ≫ (α_ X A H).inv = _
  calc
    _ = (X ◁ (i ≫ (β_ H A).hom)) ≫ (α_ X A H).inv :=
      (Category.assoc (X ◁ i) (X ◁ (β_ H A).hom) (α_ X A H).inv).symm.trans
        (congrArg (fun z => z ≫ (α_ X A H).inv)
          (whiskerLeft_comp X i (β_ H A).hom).symm)
    _ = (X ◁ ((ρ_ A).inv ≫ A ◁ p)) ≫ (α_ X A H).inv :=
      congrArg (fun z => (X ◁ z) ≫ (α_ X A H).inv) hB
    _ = (X ◁ (ρ_ A).inv) ≫ (X ◁ (A ◁ p)) ≫ (α_ X A H).inv := by
      rw [whiskerLeft_comp, Category.assoc]
    _ = (X ◁ (ρ_ A).inv) ≫ (α_ X A (𝟙_ V)).inv ≫ (X ⊗ A) ◁ p :=
      congrArg (fun z => (X ◁ (ρ_ A).inv) ≫ z)
        (associator_inv_naturality_right X A p)
    _ = _ := by
      rw [whiskerLeft_rightUnitor_inv]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The source coefficient is the original right sphere action followed by its index swap. -/
def coefficientFromRightSphere (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n a : I) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⊗ S.obj a ⟶ F.toEnrichedFunctor.obj ⟨a ⊗ n⟩ :=
  rightSphereAction d S L F n a ≫
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv

/-- Its whole original value is the coefficient action with the actual identity label. -/
theorem coefficientFromRightSphere_original
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n a : I) :
    coefficientFromRightSphere d S L F n a =
      coefficientAction d S L F n (a ⊗ n) a (𝟙 (a ⊗ n)) := by
  have h := coefficientAction_from_rightSphere_and_index d S L F n (a ⊗ n) a
    (𝟙 (a ⊗ n))
  exact (h.trans (congrArg (fun f => rightSphereAction d S L F n a ≫
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f)
      (Category.comp_id (β_ a n).inv))).symm

/-- The entire generator uses the original right sphere and complete restricted index action. -/
def recoveredGenerator (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a : I) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⊗ (((a ⊗ n) ⟶[V] k) ⊗ S.obj a) ⟶
      F.toEnrichedFunctor.obj ⟨k⟩ :=
  (F.toEnrichedFunctor.obj ⟨n⟩ ◁ (β_ ((a ⊗ n) ⟶[V] k) (S.obj a)).hom) ≫
    (α_ (F.toEnrichedFunctor.obj ⟨n⟩) (S.obj a) ((a ⊗ n) ⟶[V] k)).inv ≫
    (coefficientFromRightSphere d S L F n a ▷ ((a ⊗ n) ⟶[V] k)) ≫
    MonoidalClosed.uncurry (((indexRestriction d S L).obj F).toEnrichedFunctor.map (a ⊗ n) k)

/-- Each index point recovers the action on the entire original coefficient object. -/
theorem recoveredGenerator_coefficient
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a : I) (f : a ⊗ n ⟶ k) :
    (F.toEnrichedFunctor.obj ⟨n⟩ ◁
      ((λ_ (S.obj a)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (S.obj a)))) ≫
      recoveredGenerator d S L F n k a = coefficientAction d S L F n k a f := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let A := S.obj a
  let H := (a ⊗ n) ⟶[V] k
  let Y := F.toEnrichedFunctor.obj (⟨a ⊗ n⟩ : OperatorIndex d S L)
  let p := eHomEquiv V f
  let i : A ⟶ H ⊗ A := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  let c := coefficientFromRightSphere d S L F n a
  let R := (X ◁ (β_ H A).hom) ≫ (α_ X A H).inv
  let r : Y ⟶ F.toEnrichedFunctor.obj ⟨k⟩ :=
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f
  let z : Y ⊗ H ⟶ F.toEnrichedFunctor.obj ⟨k⟩ := MonoidalClosed.uncurry
    (((indexRestriction d S L).obj F).toEnrichedFunctor.map (a ⊗ n) k)
  have hReorder : (X ◁ i) ≫ R = (ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p :=
    coefficientPoint_reorder X H A p
  have hNatural : ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ (c ▷ H) =
      c ≫ (ρ_ Y).inv ≫ Y ◁ p :=
    (Category.assoc (ρ_ (X ⊗ A)).inv ((X ⊗ A) ◁ p) (c ▷ H)).trans
      ((congrArg (fun t => (ρ_ (X ⊗ A)).inv ≫ t) (tensorHom_def' c p).symm).trans
        (rightUnitor_inv_comp_tensorHom c p))
  have hPointRaw : (𝟙 Y ⊗ₘ p) ≫ z = (ρ_ Y).hom ≫ r :=
    EnrichedFunctor.uncurry_map_point ((indexRestriction d S L).obj F).toEnrichedFunctor f
  have hPoint : (Y ◁ p) ≫ z = (ρ_ Y).hom ≫ r :=
    (congrArg (fun t => t ≫ z) (id_tensorHom Y p)).symm.trans hPointRaw
  have hCoefficient : c ≫ r = coefficientAction d S L F n k a f :=
    (congrArg (fun t => t ≫ r) (coefficientFromRightSphere_original d S L F n a)).trans
      (coefficientAction_from_sphere_and_index d S L F n k a f).symm
  have hValue : recoveredGenerator d S L F n k a = R ≫ (c ▷ H) ≫ z :=
    (Category.assoc (X ◁ (β_ H A).hom) (α_ X A H).inv ((c ▷ H) ≫ z)).symm
  calc
    _ = (X ◁ i) ≫ (R ≫ (c ▷ H) ≫ z) := congrArg (fun t => (X ◁ i) ≫ t) hValue
    _ = ((X ◁ i) ≫ R) ≫ ((c ▷ H) ≫ z) := (Category.assoc _ _ _).symm
    _ = ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ ((c ▷ H) ≫ z) :=
      congrArg (fun t => t ≫ ((c ▷ H) ≫ z)) hReorder
    _ = (((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ (c ▷ H)) ≫ z :=
      (Category.assoc _ _ _).symm
    _ = (c ≫ (ρ_ Y).inv ≫ Y ◁ p) ≫ z := congrArg (fun t => t ≫ z) hNatural
    _ = c ≫ (ρ_ Y).inv ≫ ((Y ◁ p) ≫ z) :=
      (Category.assoc c ((ρ_ Y).inv ≫ Y ◁ p) z).trans
        (congrArg (fun t => c ≫ t) (Category.assoc (ρ_ Y).inv (Y ◁ p) z))
    _ = c ≫ (ρ_ Y).inv ≫ ((ρ_ Y).hom ≫ r) :=
      congrArg (fun t => c ≫ (ρ_ Y).inv ≫ t) hPoint
    _ = c ≫ r := congrArg (fun t => c ≫ t) (Iso.inv_hom_id_assoc (ρ_ Y) r)
    _ = _ := hCoefficient

/-- The original unit separator recovers every complete index Hom generator. -/
theorem generatorAction_eq_recoveredGenerator (hU : IsSeparator (𝟙_ V))
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a : I) :
    generatorAction d S L F n k a = recoveredGenerator d S L F n k a := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let A := S.obj a
  let H := (a ⊗ n) ⟶[V] k
  let R : X ⊗ (H ⊗ A) ⟶ (X ⊗ A) ⊗ H :=
    (X ◁ (β_ H A).hom) ≫ (α_ X A H).inv
  let T : (X ⊗ A) ⊗ H ⟶ X ⊗ (H ⊗ A) :=
    (α_ X A H).hom ≫ X ◁ (β_ H A).inv
  have hRT : R ≫ T = 𝟙 (X ⊗ (H ⊗ A)) := by
    dsimp only [R, T]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv]
  let e : (X ⊗ A) ⊗ H ≅ X ⊗ (H ⊗ A) :=
    (α_ X A H) ≪≫ (tensorLeft X).mapIso (β_ H A).symm
  have he : e.hom = T := rfl
  apply (cancel_epi e.hom).1
  rw [he]
  apply MonoidalClosed.curry_injective
  apply hU.def
  intro p
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  apply (cancel_epi (ρ_ (X ⊗ A)).inv).1
  let i : A ⟶ H ⊗ A := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  have hReorder : (X ◁ i) ≫ R = (ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p :=
    coefficientPoint_reorder X H A p
  have hPrefix : ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ T = X ◁ i := by
    calc
      _ = ((X ◁ i) ≫ R) ≫ T := congrArg (fun t => t ≫ T) hReorder.symm
      _ = (X ◁ i) ≫ (R ≫ T) := Category.assoc _ _ _
      _ = (X ◁ i) ≫ 𝟙 (X ⊗ (H ⊗ A)) := congrArg (fun t => (X ◁ i) ≫ t) hRT
      _ = _ := Category.comp_id _
  let f : a ⊗ n ⟶ k := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := Equiv.apply_symm_apply _ p
  have hOriginal : (X ◁ i) ≫ generatorAction d S L F n k a =
      coefficientAction d S L F n k a f := by
    have h := coefficientAction_eq_generator d S L F n k a f
    rw [hp] at h
    exact h.symm
  have hRecovered : (X ◁ i) ≫ recoveredGenerator d S L F n k a =
      coefficientAction d S L F n k a f := by
    have h := recoveredGenerator_coefficient d S L F n k a f
    rw [hp] at h
    exact h
  calc
    _ = ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫
        (T ≫ generatorAction d S L F n k a) := (Category.assoc _ _ _).symm
    _ = (((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ T) ≫
        generatorAction d S L F n k a := (Category.assoc _ _ _).symm
    _ = (X ◁ i) ≫ generatorAction d S L F n k a :=
      congrArg (fun t => t ≫ generatorAction d S L F n k a) hPrefix
    _ = (X ◁ i) ≫ recoveredGenerator d S L F n k a := hOriginal.trans hRecovered.symm
    _ = (((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ T) ≫
        recoveredGenerator d S L F n k a :=
      congrArg (fun t => t ≫ recoveredGenerator d S L F n k a) hPrefix.symm
    _ = ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫
        (T ≫ recoveredGenerator d S L F n k a) := Category.assoc _ _ _
    _ = _ := Category.assoc _ _ _

/-- The recovered family satisfies the entire original coefficient-index relation. -/
theorem recoveredGenerator_balanced (hU : IsSeparator (𝟙_ V))
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    weightedCoend.Mapped.Balanced (weight d n k) S
      (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)) (recoveredGenerator d S L F n k) := by
  have h : generatorAction d S L F n k = recoveredGenerator d S L F n k := by
    funext a
    exact generatorAction_eq_recoveredGenerator d S L hU F n k a
  exact h ▸ generatorAction_balanced d S L F n k

/-- The actual mapped coend reconstructs the entire original operator Hom map. -/
theorem full_operator_map_recovery (hU : IsSeparator (𝟙_ V))
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    MonoidalClosed.curry
      (weightedCoend.Mapped.desc (weight d n k) S
        (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)) (recoveredGenerator d S L F n k)
        (recoveredGenerator_balanced d S L hU F n k)) = F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  apply weightedCoend.Mapped.hom_ext (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩))
  intro a
  exact (weightedCoend.Mapped.gen_desc (weight d n k) S
    (tensorLeft (F.toEnrichedFunctor.obj ⟨n⟩)) (recoveredGenerator d S L F n k)
    (recoveredGenerator_balanced d S L hU F n k) a).trans
      (generatorAction_eq_recoveredGenerator d S L hU F n k a).symm

end CategoryTheory.Enriched.SphereOperator
