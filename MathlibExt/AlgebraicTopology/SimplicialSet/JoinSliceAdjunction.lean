/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Structured join-division adjunctions

This file constructs the whole-map universal property of general join slices.
The implementation assembles the evaluation map at the augmented Day level,
uses the Day tensor left Kan extension to recover the entire join map, and then
packages the resulting strict Hom equivalences as adjunctions through the
under-category of the fixed factor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor
  ExternalProduct CategoryTheory.Prod

universe u

namespace SSet
namespace Join


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma rightUnitor_inv_app_of_generalF (F : DayCat.{u}) (m : SimplexCategory)
    (z : F.functor.obj (op (WithInitial.of m))) :
    (ρ_ F).inv.natTrans.app (op (WithInitial.of m)) z =
      (DayFunctor.η F (𝟙_ DayCat.{u})).app
        (op (WithInitial.of m), op WithInitial.star)
        (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) := by
  cases m with
  | mk m =>
    have hstruct :=
      LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
        (Type u) F (op (WithInitial.of ⦋m⦌))
    have h2 := types_congr_hom hstruct
      (z, (PUnit.unit : (PUnit : Type u)))
    simp only [comp_apply] at h2
    have hmapid : F.functor.map
          (ρ_ (op (WithInitial.of ⦋m⦌))).inv z = z := by
      rw [rightUnitor_op_of_inv]
      simp only [CategoryTheory.Functor.map_id]
      rfl
    have h2' : (ρ_ F).hom.natTrans.app (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η F (𝟙_ DayCat.{u})).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)) = z := by
      exact h2.trans hmapid
    have hcomp : (ρ_ F).inv.natTrans.app (op (WithInitial.of ⦋m⦌))
          ((ρ_ F).hom.natTrans.app (op (WithInitial.of ⦋m⦌))
            ((DayFunctor.η F (𝟙_ DayCat.{u})).app
              (op (WithInitial.of ⦋m⦌), op WithInitial.star)
              (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
                (Type u) PUnit.unit))) =
        (DayFunctor.η F (𝟙_ DayCat.{u})).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
            (Type u) PUnit.unit) := by
      have hid : ((ρ_ F).hom ≫ (ρ_ F).inv).natTrans = 𝟙 _ := by
        have hcong := congrArg DayFunctor.Hom.natTrans (ρ_ F).hom_inv_id
        rwa [dayIdNatTrans] at hcong
      have happ := types_congr_hom
        (NatTrans.congr_app hid (op (WithInitial.of ⦋m⦌)))
        ((DayFunctor.η F (𝟙_ DayCat.{u})).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit))
      simp only [NatTrans.id_app, types_id_apply] at happ
      exact happ
    rw [h2'] at hcomp
    exact hcomp


private noncomputable def joinInlDayMap (K Y : SSet.{u}) :
    augDay.obj K ⟶ augDay.obj K ⊗ augDay.obj Y :=
  (ρ_ (augDay.obj K)).inv ≫
    (augDay.obj K ◁ dayUnitYonedaIso.{u}.hom) ≫
    (augDay.obj K ◁ augDayBotIso.{u}.inv) ≫
    (augDay.obj K ◁ augDay.map (initial.to Y))

private lemma augDay_map_joinInl_comp_augDayJoinIso_hom (K Y : SSet.{u}) :
    augDay.map (SSet.joinInl K Y) ≫ (augDayJoinIso K Y).hom =
      joinInlDayMap K Y := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      simp only [SSet.joinInl]
      rw [SSet.join_obj_map_eq]
      simp only [SSet.joinBotIso, DayFunctor.comp_natTrans, NatTrans.comp_app, joinInlDayMap]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj K) (augDay.obj Y)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma joinInl_app_eq_η (K Y : SSet.{u}) (m : SimplexCategory)
    (z : K.obj (op m)) :
    (SSet.joinInl K Y).app (op m) z =
      (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
        (op (WithInitial.of m), op WithInitial.star) (z, PUnit.unit) := by
  cases m with
  | mk m =>
    have s1 := rightUnitor_inv_app_of_generalF (augDay.obj K) ⦋m⦌ z
    have s2 : (augDay.obj K ◁ dayUnitYonedaIso.{u}.hom).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.obj K) (𝟙_ DayCat.{u})).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
              (Type u) PUnit.unit)) =
        (DayFunctor.η (augDay.obj K)
          (dayYoneda.{u} WithInitial.star)).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (z, ULift.up (𝟙 WithInitial.star)) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.obj K) (𝟙_ DayCat.{u})
          (dayYoneda.{u} WithInitial.star) dayUnitYonedaIso.{u}.hom
          (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
        (z, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s3 : (augDay.obj K ◁ augDayBotIso.{u}.inv).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.obj K)
            (dayYoneda.{u} WithInitial.star)).app
              (op (WithInitial.of ⦋m⦌), op WithInitial.star)
              (z, ULift.up (𝟙 WithInitial.star))) =
        (DayFunctor.η (augDay.obj K)
          (augDay.obj (⊥_ SSet.{u}))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (z, PUnit.unit) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.obj K)
          (dayYoneda.{u} WithInitial.star)
          (augDay.obj (⊥_ SSet.{u})) augDayBotIso.{u}.inv
          (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
        (z, ULift.up (𝟙 WithInitial.star))
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s4 : (augDay.obj K ◁ augDay.map (initial.to Y)).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (⊥_ SSet.{u}))).app
              (op (WithInitial.of ⦋m⦌), op WithInitial.star)
              (z, PUnit.unit)) =
        (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (z, PUnit.unit) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.obj K)
          (augDay.obj (⊥_ SSet.{u})) (augDay.obj Y)
          (augDay.map (initial.to Y))
          (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
        (z, PUnit.unit)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have hj := congrArg DayFunctor.Hom.natTrans
      (augDay_map_joinInl_comp_augDayJoinIso_hom K Y)
    have hjapp := types_congr_hom
      (NatTrans.congr_app hj (op (WithInitial.of ⦋m⦌))) z
    change (SSet.joinInl K Y).app (op ⦋m⦌) z =
      (joinInlDayMap K Y).natTrans.app
        (op (WithInitial.of ⦋m⦌)) z at hjapp
    rw [hjapp]
    change
      (((ρ_ (augDay.obj K)).inv ≫
          (augDay.obj K ◁ dayUnitYonedaIso.{u}.hom) ≫
          (augDay.obj K ◁ augDayBotIso.{u}.inv) ≫
          (augDay.obj K ◁ augDay.map (initial.to Y))).natTrans.app
        (op (WithInitial.of ⦋m⦌))) z = _
    simp only [dayCompNatTrans, NatTrans.comp_app, types_comp_apply]
    rw [s1, s2, s3, s4]



private lemma joinInlDayMap_app_of (K Y : SSet.{u}) (m : SimplexCategory)
    (z : K.obj (op m)) :
    (joinInlDayMap K Y).natTrans.app (op (WithInitial.of m)) z =
      (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
        (op (WithInitial.of m), op WithInitial.star) (z, PUnit.unit) := by
  have hj := congrArg DayFunctor.Hom.natTrans
    (augDay_map_joinInl_comp_augDayJoinIso_hom K Y)
  have hjapp := types_congr_hom
    (NatTrans.congr_app hj (op (WithInitial.of m))) z
  change (SSet.joinInl K Y).app (op m) z =
    (joinInlDayMap K Y).natTrans.app (op (WithInitial.of m)) z at hjapp
  exact hjapp.symm.trans (joinInl_app_eq_η K Y m z)

private noncomputable def wholeDayMap {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceUnder X f).obj (op n)) :
    augDay.obj K ⊗ augDay.obj (SSet.stdSimplex.obj n) ⟶ augDay.obj X :=
  (augDayJoinIso K (SSet.stdSimplex.obj n)).inv ≫ augDay.map g.1

private lemma joinInlDayMap_comp_wholeDayMap {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceUnder X f).obj (op n)) :
    joinInlDayMap K (SSet.stdSimplex.obj n) ≫ wholeDayMap f n g =
      augDay.map f := by
  rw [← augDay_map_joinInl_comp_augDayJoinIso_hom]
  simp only [wholeDayMap, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp]
  rw [g.2]


private lemma sliceUnderTensorComponent_boundary_right
    {K X : SSet.{u}} (f : K ⟶ X)
    {a c n : SimplexCategory}
    (h1 : op (WithInitial.of a) ⟶ op (WithInitial.of c))
    (h2 : op (WithInitial.of n) ⟶ op WithInitial.star)
    (q1 : (augDay.obj K).functor.obj (op (WithInitial.of a)))
    (q2 : (SSet.sliceUnder X f).obj (op n)) :
    (augDay.obj X).functor.map (h1 ⊗ₘ h2)
        ((wholeDayMap f n q2).natTrans.app
          (op (WithInitial.of a) ⊗ op (WithInitial.of n))
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (SSet.stdSimplex.obj n))).app
              (op (WithInitial.of a), op (WithInitial.of n))
              (q1, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))))) =
      (augDay.map f).natTrans.app (op (WithInitial.of c))
        ((augDay.obj K).functor.map h1 q1) := by
  let θ := wholeDayMap f n q2
  let e := SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))
  have hη := types_congr_hom
    ((DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj n))).naturality
        ((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of n)) ⟶
            (op (WithInitial.of c), op WithInitial.star))) (q1, e)
  have hθ := types_congr_hom
    (θ.natTrans.naturality (h1 ⊗ₘ h2))
    ((DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj n))).app
        (op (WithInitial.of a), op (WithInitial.of n)) (q1, e))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      (DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj n))).app
          (op (WithInitial.of c), op WithInitial.star)
          (((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj n)).functor).map (h1, h2)
            ((q1, e) :
              ((augDay.obj K).functor ⊠
                (augDay.obj (SSet.stdSimplex.obj n)).functor).obj
                  (op (WithInitial.of a), op (WithInitial.of n)))) =
        (augDay.obj K ⊗ augDay.obj (SSet.stdSimplex.obj n)).functor.map
          (h1 ⊗ₘ h2)
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (SSet.stdSimplex.obj n))).app
              (op (WithInitial.of a), op (WithInitial.of n)) (q1, e)) := by
    exact hη
  rw [← hθ]
  rw [← hη']
  have he : (augDay.obj (SSet.stdSimplex.obj n)).functor.map h2 e =
      PUnit.unit := by
    change (PUnit.unit : PUnit) = PUnit.unit
    rfl
  have hext :
      ((augDay.obj K).functor ⊠
        (augDay.obj (SSet.stdSimplex.obj n)).functor).map
        (((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of n)) ⟶
            (op (WithInitial.of c), op WithInitial.star)))
        ((q1, e) :
          ((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj n)).functor).obj
              (op (WithInitial.of a), op (WithInitial.of n))) =
        (((augDay.obj K).functor.map h1 q1, PUnit.unit) :
          ((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj n)).functor).obj
              (op (WithInitial.of c), op WithInitial.star)) := by
    simp only [externalProductBifunctor_obj_map]
    rw [CategoryTheory.comp_apply, CategoryTheory.whiskerRight_apply,
      CategoryTheory.whiskerLeft_apply]
    exact Prod.ext rfl he
  rw [hext]
  rw [← joinInlDayMap_app_of K (SSet.stdSimplex.obj n) c
    ((augDay.obj K).functor.map h1 q1)]
  have hr := congrArg DayFunctor.Hom.natTrans
    (joinInlDayMap_comp_wholeDayMap f n q2)
  exact types_congr_hom
    (NatTrans.congr_app hr (op (WithInitial.of c)))
    ((augDay.obj K).functor.map h1 q1)


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma leftUnitor_inv_app_of_generalF (F : DayCat.{u}) (m : SimplexCategory)
    (z : F.functor.obj (op (WithInitial.of m))) :
    (λ_ F).inv.natTrans.app (op (WithInitial.of m)) z =
      (DayFunctor.η (𝟙_ DayCat.{u}) F).app
        (op WithInitial.star, op (WithInitial.of m))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, z) := by
  cases m with
  | mk m =>
    have hstruct :=
      LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
        (Type u) F (op (WithInitial.of ⦋m⦌))
    have h2 := types_congr_hom hstruct
      ((PUnit.unit : (PUnit : Type u)), z)
    simp only [comp_apply] at h2
    have hmapid : F.functor.map
          (λ_ (op (WithInitial.of ⦋m⦌))).inv z = z := by
      rw [leftUnitor_op_of_inv]
      simp only [CategoryTheory.Functor.map_id]
      rfl
    have h2' : (λ_ F).hom.natTrans.app (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (𝟙_ DayCat.{u}) F).app
            (op WithInitial.star, op (WithInitial.of ⦋m⦌))
            (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, z)) = z := by
      exact h2.trans hmapid
    have hcomp : (λ_ F).inv.natTrans.app (op (WithInitial.of ⦋m⦌))
          ((λ_ F).hom.natTrans.app (op (WithInitial.of ⦋m⦌))
            ((DayFunctor.η (𝟙_ DayCat.{u}) F).app
              (op WithInitial.star, op (WithInitial.of ⦋m⦌))
              (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
                (Type u) PUnit.unit, z))) =
        (DayFunctor.η (𝟙_ DayCat.{u}) F).app
          (op WithInitial.star, op (WithInitial.of ⦋m⦌))
          (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
            (Type u) PUnit.unit, z) := by
      have hid : ((λ_ F).hom ≫ (λ_ F).inv).natTrans = 𝟙 _ := by
        have hcong := congrArg DayFunctor.Hom.natTrans (λ_ F).hom_inv_id
        rwa [dayIdNatTrans] at hcong
      have happ := types_congr_hom
        (NatTrans.congr_app hid (op (WithInitial.of ⦋m⦌)))
        ((DayFunctor.η (𝟙_ DayCat.{u}) F).app
          (op WithInitial.star, op (WithInitial.of ⦋m⦌))
          (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, z))
      simp only [NatTrans.id_app, types_id_apply] at happ
      exact happ
    rw [h2'] at hcomp
    exact hcomp

private noncomputable def joinInrDayMap (K Y : SSet.{u}) :
    augDay.obj Y ⟶ augDay.obj K ⊗ augDay.obj Y :=
  (λ_ (augDay.obj Y)).inv ≫
    (dayUnitYonedaIso.{u}.hom ▷ augDay.obj Y) ≫
    (augDayBotIso.{u}.inv ▷ augDay.obj Y) ≫
    (augDay.map (initial.to K) ▷ augDay.obj Y)

private lemma augDay_map_joinInr_comp_augDayJoinIso_hom (K Y : SSet.{u}) :
    augDay.map (SSet.joinInr K Y) ≫ (augDayJoinIso K Y).hom =
      joinInrDayMap K Y := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      simp only [SSet.joinInr]
      rw [SSet.join_map_app_eq]
      simp only [SSet.botJoinIso, DayFunctor.comp_natTrans,
        NatTrans.comp_app, joinInrDayMap]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj K) (augDay.obj Y)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext



set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma joinInr_app_eq_η (K Y : SSet.{u}) (m : SimplexCategory)
    (z : Y.obj (op m)) :
    (SSet.joinInr K Y).app (op m) z =
      (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
        (op WithInitial.star, op (WithInitial.of m)) (PUnit.unit, z) := by
  cases m with
  | mk m =>
    have s1 := leftUnitor_inv_app_of_generalF (augDay.obj Y) ⦋m⦌ z
    have s2 : (dayUnitYonedaIso.{u}.hom ▷ augDay.obj Y).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (𝟙_ DayCat.{u}) (augDay.obj Y)).app
            (op WithInitial.star, op (WithInitial.of ⦋m⦌))
            (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ
              (Type u) PUnit.unit, z)) =
        (DayFunctor.η (dayYoneda.{u} WithInitial.star)
          (augDay.obj Y)).app
            (op WithInitial.star, op (WithInitial.of ⦋m⦌))
            (ULift.up (𝟙 WithInitial.star), z) := by
      have h := types_congr_hom
        (η_whiskerRight_app (𝟙_ DayCat.{u})
          (dayYoneda.{u} WithInitial.star) (augDay.obj Y)
          dayUnitYonedaIso.{u}.hom (op WithInitial.star)
          (op (WithInitial.of ⦋m⦌)))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, z)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s3 : (augDayBotIso.{u}.inv ▷ augDay.obj Y).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (dayYoneda.{u} WithInitial.star)
            (augDay.obj Y)).app
              (op WithInitial.star, op (WithInitial.of ⦋m⦌))
              (ULift.up (𝟙 WithInitial.star), z)) =
        (DayFunctor.η (augDay.obj (⊥_ SSet.{u}))
          (augDay.obj Y)).app
            (op WithInitial.star, op (WithInitial.of ⦋m⦌))
            (PUnit.unit, z) := by
      have h := types_congr_hom
        (η_whiskerRight_app (dayYoneda.{u} WithInitial.star)
          (augDay.obj (⊥_ SSet.{u})) (augDay.obj Y)
          augDayBotIso.{u}.inv (op WithInitial.star)
          (op (WithInitial.of ⦋m⦌)))
        (ULift.up (𝟙 WithInitial.star), z)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s4 : (augDay.map (initial.to K) ▷ augDay.obj Y).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.obj (⊥_ SSet.{u}))
            (augDay.obj Y)).app
              (op WithInitial.star, op (WithInitial.of ⦋m⦌))
              (PUnit.unit, z)) =
        (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
          (op WithInitial.star, op (WithInitial.of ⦋m⦌))
          (PUnit.unit, z) := by
      have h := types_congr_hom
        (η_whiskerRight_app (augDay.obj (⊥_ SSet.{u}))
          (augDay.obj K) (augDay.obj Y)
          (augDay.map (initial.to K))
          (op WithInitial.star) (op (WithInitial.of ⦋m⦌)))
        (PUnit.unit, z)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have hj := congrArg DayFunctor.Hom.natTrans
      (augDay_map_joinInr_comp_augDayJoinIso_hom K Y)
    have hjapp := types_congr_hom
      (NatTrans.congr_app hj (op (WithInitial.of ⦋m⦌))) z
    change (SSet.joinInr K Y).app (op ⦋m⦌) z =
      (joinInrDayMap K Y).natTrans.app
        (op (WithInitial.of ⦋m⦌)) z at hjapp
    rw [hjapp]
    change
      (((λ_ (augDay.obj Y)).inv ≫
          (dayUnitYonedaIso.{u}.hom ▷ augDay.obj Y) ≫
          (augDayBotIso.{u}.inv ▷ augDay.obj Y) ≫
          (augDay.map (initial.to K) ▷ augDay.obj Y)).natTrans.app
        (op (WithInitial.of ⦋m⦌))) z = _
    simp only [dayCompNatTrans, NatTrans.comp_app, types_comp_apply]
    rw [s1, s2, s3, s4]



private lemma joinInrDayMap_app_of (K Y : SSet.{u}) (m : SimplexCategory)
    (z : Y.obj (op m)) :
    (joinInrDayMap K Y).natTrans.app (op (WithInitial.of m)) z =
      (DayFunctor.η (augDay.obj K) (augDay.obj Y)).app
        (op WithInitial.star, op (WithInitial.of m)) (PUnit.unit, z) := by
  have hj := congrArg DayFunctor.Hom.natTrans
    (augDay_map_joinInr_comp_augDayJoinIso_hom K Y)
  have hjapp := types_congr_hom
    (NatTrans.congr_app hj (op (WithInitial.of m))) z
  change (SSet.joinInr K Y).app (op m) z =
    (joinInrDayMap K Y).natTrans.app (op (WithInitial.of m)) z at hjapp
  exact hjapp.symm.trans (joinInr_app_eq_η K Y m z)

private lemma joinInrDayMap_comp_wholeDayMap {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceUnder X f).obj (op n)) :
    joinInrDayMap K (SSet.stdSimplex.obj n) ≫ wholeDayMap f n g =
      augDay.map (SSet.joinInr K (SSet.stdSimplex.obj n) ≫ g.1) := by
  rw [← augDay_map_joinInr_comp_augDayJoinIso_hom]
  simp only [wholeDayMap, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.map_comp]

private lemma sliceUnderTensorComponent_boundary_left
    {K X : SSet.{u}} (f : K ⟶ X)
    {a b d : SimplexCategory}
    (h1 : op (WithInitial.of a) ⟶ op WithInitial.star)
    (h2 : op (WithInitial.of b) ⟶ op (WithInitial.of d))
    (q1 : (augDay.obj K).functor.obj (op (WithInitial.of a)))
    (q2 : (SSet.sliceUnder X f).obj (op b)) :
    (augDay.obj X).functor.map (h1 ⊗ₘ h2)
        ((wholeDayMap f b q2).natTrans.app
          (op (WithInitial.of a) ⊗ op (WithInitial.of b))
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (SSet.stdSimplex.obj b))).app
              (op (WithInitial.of a), op (WithInitial.of b))
              (q1, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj b))))) =
      (SSet.sliceUnder.proj X f).app (op d)
        ((SSet.sliceUnder X f).map
          (WithInitial.down h2.unop).op q2) := by
  let θ := wholeDayMap f b q2
  let e := SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj b))
  let α : op b ⟶ op d := (WithInitial.down h2.unop).op
  have hη := types_congr_hom
    ((DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj b))).naturality
        ((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op WithInitial.star, op (WithInitial.of d)))) (q1, e)
  have hθ := types_congr_hom
    (θ.natTrans.naturality (h1 ⊗ₘ h2))
    ((DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj b))).app
        (op (WithInitial.of a), op (WithInitial.of b)) (q1, e))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      (DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj b))).app
          (op WithInitial.star, op (WithInitial.of d))
          (((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj b)).functor).map (h1, h2)
            ((q1, e) :
              ((augDay.obj K).functor ⊠
                (augDay.obj (SSet.stdSimplex.obj b)).functor).obj
                  (op (WithInitial.of a), op (WithInitial.of b)))) =
        (augDay.obj K ⊗ augDay.obj (SSet.stdSimplex.obj b)).functor.map
          (h1 ⊗ₘ h2)
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (SSet.stdSimplex.obj b))).app
              (op (WithInitial.of a), op (WithInitial.of b)) (q1, e)) := hη
  rw [← hθ, ← hη']
  have hk : (augDay.obj K).functor.map h1 q1 = PUnit.unit := by
    change (PUnit.unit : PUnit) = PUnit.unit
    rfl
  let e' := (augDay.obj (SSet.stdSimplex.obj b)).functor.map h2 e
  have hext :
      ((augDay.obj K).functor ⊠
        (augDay.obj (SSet.stdSimplex.obj b)).functor).map
        (((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op WithInitial.star, op (WithInitial.of d))))
        ((q1, e) :
          ((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj b)).functor).obj
              (op (WithInitial.of a), op (WithInitial.of b))) =
        ((PUnit.unit, e') :
          ((augDay.obj K).functor ⊠
            (augDay.obj (SSet.stdSimplex.obj b)).functor).obj
              (op WithInitial.star, op (WithInitial.of d))) := by
    simp only [externalProductBifunctor_obj_map]
    rw [CategoryTheory.comp_apply, CategoryTheory.whiskerRight_apply,
      CategoryTheory.whiskerLeft_apply]
    exact Prod.ext hk rfl
  rw [hext]
  rw [← joinInrDayMap_app_of K (SSet.stdSimplex.obj b) d e']
  have hr := congrArg DayFunctor.Hom.natTrans
    (joinInrDayMap_comp_wholeDayMap f b q2)
  rw [show θ = wholeDayMap f b q2 from rfl]
  change (wholeDayMap f b q2).natTrans.app (op (WithInitial.of d))
      ((joinInrDayMap K (SSet.stdSimplex.obj b)).natTrans.app
        (op (WithInitial.of d)) e') = _
  have hrapp := types_congr_hom (NatTrans.congr_app hr
    (op (WithInitial.of d))) e'
  rw [dayCompNatTrans, NatTrans.comp_app] at hrapp
  simp only [types_comp_apply] at hrapp
  rw [hrapp]
  change (SSet.joinInr K (SSet.stdSimplex.obj b) ≫ q2.1).app (op d) e' = _
  change SSet.yonedaEquiv
      (SSet.stdSimplex.map α.unop ≫
        SSet.joinInr K (SSet.stdSimplex.obj b) ≫ q2.1) = _
  rw [← Category.assoc, SSet.map_comp_joinInr]
  rfl

private def sliceUnderTensorComponent {K X : SSet.{u}} (f : K ⟶ X)
    (a : AugmentedSimplexCategory) (n : SimplexCategory) :
    ((augDay.obj K).functor ⊠
      (augDay.obj (sliceUnder X f)).functor).obj (op a, op (WithInitial.of n)) ⟶
      (augDay.obj X).functor.obj (op (a ⊗ WithInitial.of n)) :=
  ↾fun q =>
    ((((augDayJoinIso K (SSet.stdSimplex.obj n)).inv ≫
        augDay.map q.2.1).natTrans.app (op (a ⊗ WithInitial.of n)))
      ((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj n))).app
          (op a, op (WithInitial.of n))
          (q.1, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))))


private lemma wholeDayMap_map {K X : SSet.{u}} (f : K ⟶ X)
    {n m : SimplexCategory} (α : op n ⟶ op m)
    (g : (sliceUnder X f).obj (op n)) :
    (augDay.obj K ◁ augDay.map (SSet.stdSimplex.map α.unop)) ≫
        wholeDayMap f n g =
      wholeDayMap f m ((sliceUnder X f).map α g) := by
  apply (cancel_epi (augDayJoinIso K (SSet.stdSimplex.obj m)).hom).mp
  simp only [wholeDayMap, sliceUnder.map_val, Functor.map_comp]
  slice_lhs 1 2 => rw [← augDayJoinIso_naturality_right]
  simp

private noncomputable def underTensorOfComponent {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (sliceUnder X f).obj (op n))
    (a : AugmentedSimplexCategoryᵒᵖ) :
    (augDay.obj K).functor.obj a ⟶
      (augDay.obj X).functor.obj (a ⊗ op (WithInitial.of n)) :=
  ↾fun z =>
    (wholeDayMap f n g).natTrans.app (a ⊗ op (WithInitial.of n))
      ((DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj n))).app
          (a, op (WithInitial.of n))
          (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))))

private lemma underTensorOfComponent_naturality_right
    {K X : SSet.{u}} (f : K ⟶ X)
    {n m : SimplexCategory} (α : op n ⟶ op m)
    (g : (sliceUnder X f).obj (op n))
    (a : AugmentedSimplexCategoryᵒᵖ) :
    underTensorOfComponent f m ((sliceUnder X f).map α g) a =
      underTensorOfComponent f n g a ≫
        (augDay.obj X).functor.map
          (𝟙 a ⊗ₘ AugmentedSimplexCategory.inclusion.op.map α) := by
  apply TypeCat.homEquiv.injective
  funext z
  have hmap := congrArg DayFunctor.Hom.natTrans
    (wholeDayMap_map f α g)
  change (wholeDayMap f m ((sliceUnder X f).map α g)).natTrans.app
        (a ⊗ op (WithInitial.of m))
      ((DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj m))).app
          (a, op (WithInitial.of m))
          (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)))) =
    (augDay.obj X).functor.map
        (𝟙 a ⊗ₘ AugmentedSimplexCategory.inclusion.op.map α)
      ((wholeDayMap f n g).natTrans.app (a ⊗ op (WithInitial.of n))
        ((DayFunctor.η (augDay.obj K)
          (augDay.obj (SSet.stdSimplex.obj n))).app
            (a, op (WithInitial.of n))
            (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))))
  rw [← hmap]
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app, types_comp_apply]
  have hη := types_congr_hom
    (η_whiskerLeft_app (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj m))
      (augDay.obj (SSet.stdSimplex.obj n))
      (augDay.map (SSet.stdSimplex.map α.unop))
      a (op (WithInitial.of m)))
    (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)))
  simp only [types_comp_apply] at hη
  rw [hη]
  have hident :
      (augDay.map (SSet.stdSimplex.map α.unop)).natTrans.app
          (op (WithInitial.of m))
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) =
        (augDay.obj (SSet.stdSimplex.obj n)).functor.map
          (AugmentedSimplexCategory.inclusion.op.map α)
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) := by
    rfl
  rw [CategoryTheory.whiskerLeft_apply, hident]
  let τ := DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj n)) ≫
    Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      (wholeDayMap f n g).natTrans
  have h := types_congr_hom
    (τ.naturality
      (𝟙 a ×ₘ AugmentedSimplexCategory.inclusion.op.map α))
    (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))
  simp only [types_comp_apply, Functor.comp_map, tensor_map,
    externalProductBifunctor_obj_map] at h
  rw [CategoryTheory.whiskerLeft_apply] at h
  simp [τ, NatTrans.comp_app] at h
  change
    (wholeDayMap f n g).natTrans.app (a ⊗ op (WithInitial.of m))
        ((DayFunctor.η (augDay.obj K)
          (augDay.obj (SSet.stdSimplex.obj n))).app
            (a, op (WithInitial.of m))
            (z, (augDay.obj (SSet.stdSimplex.obj n)).functor.map
              (AugmentedSimplexCategory.inclusion.op.map α)
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))))) =
      (augDay.obj X).functor.map
          (𝟙 a ⊗ₘ AugmentedSimplexCategory.inclusion.op.map α)
        ((wholeDayMap f n g).natTrans.app (a ⊗ op (WithInitial.of n))
          ((DayFunctor.η (augDay.obj K)
            (augDay.obj (SSet.stdSimplex.obj n))).app
              (a, op (WithInitial.of n))
              (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))))) at h
  exact h

private lemma sliceUnderTensorComponent_naturality_right {K X : SSet.{u}}
    (f : K ⟶ X) (a : AugmentedSimplexCategory)
    {n m : SimplexCategory}
    (β : op (WithInitial.of n) ⟶ op (WithInitial.of m)) :
    (augDay.obj K).functor.obj (op a) ◁
        (augDay.obj (sliceUnder X f)).functor.map β ≫
        sliceUnderTensorComponent f a m =
      sliceUnderTensorComponent f a n ≫
        (augDay.obj X).functor.map (𝟙 (op a) ⊗ₘ β) := by
  let α : op n ⟶ op m := (WithInitial.down β.unop).op
  have hβ : AugmentedSimplexCategory.inclusion.op.map α = β := rfl
  apply TypeCat.homEquiv.injective
  funext q
  obtain ⟨z, g⟩ := q
  simp [TypeCat.homEquiv_apply, comp_apply]
  change underTensorOfComponent f m ((sliceUnder X f).map α g) (op a) z =
    (augDay.obj X).functor.map (𝟙 (op a) ⊗ₘ β)
      (underTensorOfComponent f n g (op a) z)
  rw [← hβ]
  exact types_congr_hom
    (underTensorOfComponent_naturality_right f α g (op a)) z

private lemma sliceUnderTensorComponent_naturality_left {K X : SSet.{u}}
    (f : K ⟶ X) {a c : AugmentedSimplexCategory}
    (h : op a ⟶ op c) (n : SimplexCategory) :
    (augDay.obj K).functor.map h ▷
      (augDay.obj (sliceUnder X f)).functor.obj (op (WithInitial.of n)) ≫
        sliceUnderTensorComponent f c n =
      sliceUnderTensorComponent f a n ≫
        (augDay.obj X).functor.map (h ⊗ₘ 𝟙 (op (WithInitial.of n))) := by
  apply TypeCat.homEquiv.injective
  funext q
  change ((augDay.obj K).functor.obj (op a) ×
    (sliceUnder X f).obj (op n)) at q
  obtain ⟨q1, q2⟩ := q
  let θ := (augDayJoinIso K (SSet.stdSimplex.obj n)).inv ≫
    augDay.map q2.1
  let e : (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
      (op (WithInitial.of n)) :=
    SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))
  have hη := types_congr_hom
    ((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj n))).naturality
        ((h, 𝟙 (op (WithInitial.of n))) :
          (op a, op (WithInitial.of n)) ⟶
            (op c, op (WithInitial.of n)))) (q1, e)
  have hθ := types_congr_hom
    (θ.natTrans.naturality (h ⊗ₘ 𝟙 (op (WithInitial.of n))))
    (((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
      (augDay.obj (SSet.stdSimplex.obj n))).app
        (op a, op (WithInitial.of n))) (q1, e))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      ((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj n))).app
          (op c, op (WithInitial.of n)))
        (((augDay.obj K).functor.map h ▷
          (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
            (op (WithInitial.of n))) (q1, e)) =
      ((augDay.obj K ⊗ augDay.obj (SSet.stdSimplex.obj n)).functor.map
        (h ⊗ₘ 𝟙 (op (WithInitial.of n))))
        (((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
          (augDay.obj (SSet.stdSimplex.obj n))).app
            (op a, op (WithInitial.of n))) (q1, e)) := by
    exact hη
  change θ.natTrans.app (op c ⊗ op (WithInitial.of n))
      (((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
        (augDay.obj (SSet.stdSimplex.obj n))).app
          (op c, op (WithInitial.of n)))
        (((augDay.obj K).functor.map h ▷
          (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
            (op (WithInitial.of n))) (q1, e))) =
    (augDay.obj X).functor.map (h ⊗ₘ 𝟙 (op (WithInitial.of n)))
      (θ.natTrans.app (op a ⊗ op (WithInitial.of n))
        (((CategoryTheory.MonoidalCategory.DayFunctor.η (augDay.obj K)
          (augDay.obj (SSet.stdSimplex.obj n))).app
            (op a, op (WithInitial.of n))) (q1, e)))
  rw [hη']
  exact hθ

private def sliceUnderTensorNatTrans {K X : SSet.{u}} (f : K ⟶ X) :
    ((augDay.obj K).functor ⊠ (augDay.obj (sliceUnder X f)).functor) ⟶
      tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor where
  app z := WithInitial.rec
    (motive := fun a : AugmentedSimplexCategory =>
      ((augDay.obj K).functor ⊠ (augDay.obj (sliceUnder X f)).functor).obj (op a, z.2) ⟶
        (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj (op a, z.2))
    (fun m => WithInitial.rec
      (motive := fun b : AugmentedSimplexCategory =>
        ((augDay.obj K).functor ⊠
            (augDay.obj (sliceUnder X f)).functor).obj (op (WithInitial.of m), op b) ⟶
          (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj
            (op (WithInitial.of m), op b))
      (fun n => sliceUnderTensorComponent f (WithInitial.of m) n)
      (↾fun q => f.app (op m) q.1)
      z.2.unop)
    (WithInitial.rec
      (motive := fun b : AugmentedSimplexCategory =>
        ((augDay.obj K).functor ⊠
            (augDay.obj (sliceUnder X f)).functor).obj (op WithInitial.star, op b) ⟶
          (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj
            (op WithInitial.star, op b))
      (fun n => ↾fun q => (sliceUnder.proj X f).app (op n) q.2)
      (↾fun _ => PUnit.unit)
      z.2.unop)
    z.1.unop
  naturality := by
    intro x y h
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = op c' := ⟨c.unop, rfl⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = op d' := ⟨d.unop, rfl⟩
    cases a' <;> cases b' <;> cases c' <;> cases d' <;>
      try { exact (WithInitial.false_of_to_star h.1.unop).elim } <;>
      try { exact (WithInitial.false_of_to_star h.2.unop).elim }
    case of.of.of.of =>
      rename_i a b c d
      rw [externalProductBifunctor_obj_map]
      dsimp
      rw [Category.assoc]
      slice_lhs 2 3 =>
        rw [sliceUnderTensorComponent_naturality_right f
          (WithInitial.of c) h.2]
      rw [← Category.assoc]
      rw [sliceUnderTensorComponent_naturality_left f h.1 b]
      rw [Category.assoc, ← Functor.map_comp]
      congr 2
      simp [MonoidalCategory.tensorHom_def]

    case of.of.of.star =>
      apply TypeCat.homEquiv.injective
      funext q
      obtain ⟨q1, q2⟩ := q
      dsimp [sliceUnderTensorComponent]
      exact (sliceUnderTensorComponent_boundary_right
        f h.1 h.2 q1 q2).symm
    case of.of.star.of =>
      apply TypeCat.homEquiv.injective
      funext q
      obtain ⟨q1, q2⟩ := q
      dsimp [sliceUnderTensorComponent]
      exact (sliceUnderTensorComponent_boundary_left
        f h.1 h.2 q1 q2).symm
    case of.of.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case of.star.of.star =>
      apply TypeCat.homEquiv.injective
      funext q
      dsimp
      have h2id : h.2 = 𝟙 _ := Subsingleton.elim _ _
      rw [h2id]
      have hf := types_congr_hom (f.naturality h.1) q.1
      exact hf
    case of.star.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case star.of.star.of =>
      apply TypeCat.homEquiv.injective
      funext q
      dsimp
      have h1id : h.1 = 𝟙 _ := Subsingleton.elim _ _
      rw [h1id]
      have hp := types_congr_hom ((sliceUnder.proj X f).naturality h.2) q.2
      exact hp
    case star.of.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case star.star.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl


private noncomputable def sliceUnderTensorMap {K X : SSet.{u}} (f : K ⟶ X) :
    augDay.obj K ⊗ augDay.obj (sliceUnder X f) ⟶ augDay.obj X :=
  DayFunctor.tensorDesc (sliceUnderTensorNatTrans f)

private noncomputable def sliceUnderEvaluation {K X : SSet.{u}} (f : K ⟶ X) :
    K ⋆ sliceUnder X f ⟶ X :=
  dropDay.map (sliceUnderTensorMap f)

private lemma augDay_map_sliceUnderEvaluation {K X : SSet.{u}} (f : K ⟶ X) :
    augDay.map (sliceUnderEvaluation f) =
      (augDayJoinIso K (sliceUnder X f)).hom ≫ sliceUnderTensorMap f := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n => rfl
  | star => apply Types.isTerminalPUnit.hom_ext

private lemma η_comp_sliceUnderTensorMap {K X : SSet.{u}} (f : K ⟶ X) :
    DayFunctor.η (augDay.obj K) (augDay.obj (sliceUnder X f)) ≫
        Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
          (sliceUnderTensorMap f).natTrans =
      sliceUnderTensorNatTrans f :=
  DayFunctor.η_comp_tensorDec _


private lemma joinInlDayMap_comp_sliceUnderTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) :
    joinInlDayMap K (sliceUnder X f) ≫ sliceUnderTensorMap f =
      augDay.map f := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      apply TypeCat.homEquiv.injective
      funext z
      have hη := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (sliceUnderTensorNatTrans f)
          (op (WithInitial.of n)) (op WithInitial.star))
        (z, PUnit.unit)
      simp only [types_comp_apply] at hη
      change (sliceUnderTensorMap f).natTrans.app
          (op (WithInitial.of n))
          ((joinInlDayMap K (sliceUnder X f)).natTrans.app
            (op (WithInitial.of n)) z) =
        (augDay.map f).natTrans.app (op (WithInitial.of n)) z
      change K.obj (op n) at z
      have hj := joinInlDayMap_app_of K (sliceUnder X f) n z
      rw [hj]
      exact hη
  | star =>
      apply Types.isTerminalPUnit.hom_ext

private lemma joinInrDayMap_comp_sliceUnderTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) :
    joinInrDayMap K (sliceUnder X f) ≫ sliceUnderTensorMap f =
      augDay.map (sliceUnder.proj X f) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      apply TypeCat.homEquiv.injective
      funext z
      have hη := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (sliceUnderTensorNatTrans f)
          (op WithInitial.star) (op (WithInitial.of n)))
        (PUnit.unit, z)
      simp only [types_comp_apply] at hη
      change (sliceUnderTensorMap f).natTrans.app
          (op (WithInitial.of n))
          ((joinInrDayMap K (sliceUnder X f)).natTrans.app
            (op (WithInitial.of n)) z) =
        (augDay.map (sliceUnder.proj X f)).natTrans.app
          (op (WithInitial.of n)) z
      change (sliceUnder X f).obj (op n) at z
      have hj := joinInrDayMap_app_of K (sliceUnder X f) n z
      rw [hj]
      exact hη
  | star =>
      apply Types.isTerminalPUnit.hom_ext

private lemma joinInl_comp_sliceUnderEvaluation {K X : SSet.{u}}
    (f : K ⟶ X) :
    SSet.joinInl K (sliceUnder X f) ≫ sliceUnderEvaluation f = f := by
  have hday : augDay.map
        (SSet.joinInl K (sliceUnder X f) ≫ sliceUnderEvaluation f) =
      augDay.map f := by
    rw [Functor.map_comp, augDay_map_sliceUnderEvaluation, ← Category.assoc,
      augDay_map_joinInl_comp_augDayJoinIso_hom,
      joinInlDayMap_comp_sliceUnderTensorMap]
  exact congrArg dropDay.map hday

private lemma joinInr_comp_sliceUnderEvaluation {K X : SSet.{u}}
    (f : K ⟶ X) :
    SSet.joinInr K (sliceUnder X f) ≫ sliceUnderEvaluation f =
      sliceUnder.proj X f := by
  have hday : augDay.map
        (SSet.joinInr K (sliceUnder X f) ≫ sliceUnderEvaluation f) =
      augDay.map (sliceUnder.proj X f) := by
    rw [Functor.map_comp, augDay_map_sliceUnderEvaluation, ← Category.assoc,
      augDay_map_joinInr_comp_augDayJoinIso_hom,
      joinInrDayMap_comp_sliceUnderTensorMap]
  exact congrArg dropDay.map hday


private lemma whisker_yoneda_comp_sliceUnderTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) (n : SimplexCategory)
    (g : (sliceUnder X f).obj (op n)) :
    (augDay.obj K ◁ augDay.map (SSet.yonedaEquiv.symm g)) ≫
        sliceUnderTensorMap f =
      wholeDayMap f n g := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
  cases b' with
  | of m =>
      obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
      cases a' with
      | of k =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨z, t⟩ := q
          let α : op n ⟶ op m := (SSet.stdSimplex.objEquiv t).op
          let σ := SSet.yonedaEquiv.symm g
          have ht : (augDay.map σ).natTrans.app (op (WithInitial.of m)) t =
              (sliceUnder X f).map α g := by rfl
          have hwh := types_congr_hom
            (η_whiskerLeft_app (augDay.obj K)
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceUnder X f)) (augDay.map σ)
              (op (WithInitial.of k)) (op (WithInitial.of m))) (z, t)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
              (op (WithInitial.of k)) (op (WithInitial.of m)))
            (z, (augDay.map σ).natTrans.app (op (WithInitial.of m)) t)
          have hcomp := types_congr_hom
            (underTensorOfComponent_naturality_right f α g (op (WithInitial.of k))) z
          have hext :
              ((augDay.obj K).functor.obj (op (WithInitial.of k)) ◁
                (augDay.map σ).natTrans.app (op (WithInitial.of m))) (z, t) =
              (z, (augDay.map σ).natTrans.app (op (WithInitial.of m)) t) := rfl
          simp only [types_comp_apply] at hwh hdesc hcomp
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceUnderTensorMap]
          rw [hdesc, ht]
          change (underTensorOfComponent f m ((sliceUnder X f).map α g)
              (op (WithInitial.of k))) z = _
          rw [hcomp]
          have hident :
              (augDay.obj (SSet.stdSimplex.obj n)).functor.map
                (AugmentedSimplexCategory.inclusion.op.map α)
                (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) = t := by
            change (SSet.stdSimplex.obj n).map α
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) = t
            have hid : SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)) =
                SSet.stdSimplex.objEquiv.symm (𝟙 n) := by
              simpa using SSet.yonedaEquiv_map (𝟙 n)
            rw [hid, SSet.stdSimplex.map_objEquiv_symm]
            apply SSet.stdSimplex.objEquiv.injective
            simp [α]
          let β : op (WithInitial.of n) ⟶ op (WithInitial.of m) :=
            (WithInitial.incl.map α.unop).op
          have hηidx := types_congr_hom
            ((DayFunctor.η (augDay.obj K)
              (augDay.obj (SSet.stdSimplex.obj n))).naturality
                ((𝟙 (op (WithInitial.of k)), β) :
                  (op (WithInitial.of k), op (WithInitial.of n)) ⟶
                    (op (WithInitial.of k), op (WithInitial.of m))))
            (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))
          have hwhole := types_congr_hom
            ((wholeDayMap f n g).natTrans.naturality
              (𝟙 (op (WithInitial.of k)) ⊗ₘ β))
            ((DayFunctor.η (augDay.obj K)
              (augDay.obj (SSet.stdSimplex.obj n))).app
                (op (WithInitial.of k), op (WithInitial.of n))
                (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))))
          simp only [types_comp_apply] at hηidx hwhole
          have hextidx :
              (((augDay.obj K).functor ⊠
                (augDay.obj (SSet.stdSimplex.obj n)).functor).map
                  ((𝟙 (op (WithInitial.of k)), β) :
                    (op (WithInitial.of k), op (WithInitial.of n)) ⟶
                      (op (WithInitial.of k), op (WithInitial.of m))))
                ((z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) :
                  ((augDay.obj K).functor ⊠
                    (augDay.obj (SSet.stdSimplex.obj n)).functor).obj
                      (op (WithInitial.of k), op (WithInitial.of n))) =
              (z, t) := by
            simpa [externalProductBifunctor_obj_map] using
              (Prod.ext (by rfl) hident)
          rw [hextidx] at hηidx
          change (augDay.obj X).functor.map
              (𝟙 (op (WithInitial.of k)) ⊗ₘ β)
              (underTensorOfComponent f n g (op (WithInitial.of k)) z) =
            (wholeDayMap f n g).natTrans.app
              (op (WithInitial.of k) ⊗ op (WithInitial.of m))
              ((DayFunctor.η (augDay.obj K)
                (augDay.obj (SSet.stdSimplex.obj n))).app
                  (op (WithInitial.of k), op (WithInitial.of m)) (z, t))
          rw [hηidx]
          exact hwhole.symm
      | star =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨z, t⟩ := q
          let ptK : (augDay.obj K).functor.obj
              (op WithInitial.star) := PUnit.unit
          have hz : z = ptK := by
            change (PUnit.unit : PUnit) = PUnit.unit
            rfl
          subst z
          let α : op n ⟶ op m := (SSet.stdSimplex.objEquiv t).op
          let σ := SSet.yonedaEquiv.symm g
          have ht : (augDay.map σ).natTrans.app
              (op (WithInitial.of m)) t = (sliceUnder X f).map α g := by
            rfl
          have hwh := types_congr_hom
            (η_whiskerLeft_app (augDay.obj K)
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceUnder X f)) (augDay.map σ)
              (op WithInitial.star) (op (WithInitial.of m)))
            (ptK, t)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
              (op WithInitial.star) (op (WithInitial.of m)))
            (ptK,
              (augDay.map σ).natTrans.app (op (WithInitial.of m)) t)
          simp only [types_comp_apply] at hwh hdesc
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          have hext :
              ((augDay.obj K).functor.obj (op WithInitial.star) ◁
                (augDay.map σ).natTrans.app (op (WithInitial.of m)))
                  (ptK, t) =
                (ptK,
                  (augDay.map σ).natTrans.app (op (WithInitial.of m)) t) :=
            rfl
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceUnderTensorMap]
          rw [hdesc, ht]
          change (sliceUnder.proj X f).app (op m)
              ((sliceUnder X f).map α g) =
            (wholeDayMap f n g).natTrans.app (op (WithInitial.of m))
              ((DayFunctor.η (augDay.obj K)
                (augDay.obj (SSet.stdSimplex.obj n))).app
                  (op WithInitial.star, op (WithInitial.of m))
                  (ptK, t))
          have hj := joinInrDayMap_app_of K (SSet.stdSimplex.obj n) m t
          have hc := congrArg DayFunctor.Hom.natTrans
            (joinInrDayMap_comp_wholeDayMap f n g)
          have hcapp := types_congr_hom
            (NatTrans.congr_app hc (op (WithInitial.of m))) t
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            types_comp_apply] at hcapp
          rw [← hj]
          rw [hcapp]
          change SSet.yonedaEquiv
              (SSet.joinInr K (SSet.stdSimplex.obj m) ≫
                ((SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1)) =
            (SSet.joinInr K (SSet.stdSimplex.obj n) ≫ g.1).app (op m) t
          rw [← Category.assoc, ← SSet.map_comp_joinInr]
          rw [Category.assoc, ← SSet.yonedaEquiv_naturality]
          have ht' : t = SSet.stdSimplex.objEquiv.symm α.unop := by
            apply SSet.stdSimplex.objEquiv.injective
            simp [α]
          rw [ht']
          symm
          simpa using
            (SSet.yonedaEquiv_symm_app_objEquiv_symm
              (x := SSet.yonedaEquiv
                (SSet.joinInr K (SSet.stdSimplex.obj n) ≫ g.1))
              (f := α.unop))
  | star =>
      obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
      cases a' with
      | of m =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨z, t⟩ := q
          let ptN : (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
              (op WithInitial.star) := PUnit.unit
          have ht : t = ptN := by
            change (PUnit.unit : PUnit) = PUnit.unit
            rfl
          subst t
          let σ := SSet.yonedaEquiv.symm g
          let ptS : (augDay.obj (sliceUnder X f)).functor.obj
              (op WithInitial.star) :=
            (augDay.map σ).natTrans.app (op WithInitial.star) ptN
          have hwh := types_congr_hom
            (η_whiskerLeft_app (augDay.obj K)
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceUnder X f)) (augDay.map σ)
              (op (WithInitial.of m)) (op WithInitial.star))
            (z, ptN)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
              (op (WithInitial.of m)) (op WithInitial.star))
            (z, ptS)
          simp only [types_comp_apply] at hwh hdesc
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          have hext :
              ((augDay.obj K).functor.obj (op (WithInitial.of m)) ◁
                (augDay.map σ).natTrans.app (op WithInitial.star))
                  (z, ptN) = (z, ptS) := rfl
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceUnderTensorMap]
          rw [hdesc]
          change f.app (op m) z =
            (wholeDayMap f n g).natTrans.app (op (WithInitial.of m))
              ((DayFunctor.η (augDay.obj K)
                (augDay.obj (SSet.stdSimplex.obj n))).app
                  (op (WithInitial.of m), op WithInitial.star)
                  (z, PUnit.unit))
          have hj := joinInlDayMap_app_of K (SSet.stdSimplex.obj n) m z
          have hc := congrArg DayFunctor.Hom.natTrans
            (joinInlDayMap_comp_wholeDayMap f n g)
          have hcapp := types_congr_hom
            (NatTrans.congr_app hc (op (WithInitial.of m))) z
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            types_comp_apply] at hcapp
          rw [← hj]
          exact hcapp.symm
      | star =>
          apply TypeCat.homEquiv.injective
          funext q
          change (PUnit.unit : PUnit) = PUnit.unit
          rfl

private lemma sliceUnderEvaluation_wholeMap {K X : SSet.{u}}
    (f : K ⟶ X) (n : SimplexCategory)
    (g : (sliceUnder X f).obj (op n)) :
    (SSet.join.obj K).map (SSet.yonedaEquiv.symm g) ≫
        sliceUnderEvaluation f = g.1 := by
  have hday : augDay.map
        ((SSet.join.obj K).map (SSet.yonedaEquiv.symm g) ≫
          sliceUnderEvaluation f) = augDay.map g.1 := by
    rw [Functor.map_comp, augDay_map_sliceUnderEvaluation,
      ← Category.assoc, SSet.Join.augDayJoinIso_naturality_right,
      Category.assoc, whisker_yoneda_comp_sliceUnderTensorMap]
    simp only [wholeDayMap, Iso.hom_inv_id_assoc]
  exact congrArg dropDay.map hday

end Join

namespace sliceUnder


/-- Recover the slice map classified by a compatible whole join map. -/
def lift {K X A : SSet.{u}} (f : K ⟶ X)
    (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f }) :
    A ⟶ sliceUnder X f where
  app n := ↾fun a =>
    ⟨(SSet.join.obj K).map (SSet.yonedaEquiv.symm a) ≫ g.1, by
      rw [← Category.assoc, SSet.joinInl_comp_map, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change (SSet.join.obj K).map
          (SSet.yonedaEquiv.symm (A.map α a)) ≫ g.1 =
      (SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫
        ((SSet.join.obj K).map (SSet.yonedaEquiv.symm a) ≫ g.1)
    have hy := SSet.yonedaEquiv_symm_naturality_left α.unop a
    rw [Quiver.Hom.op_unop] at hy
    rw [← hy, Functor.map_comp, Category.assoc]

/-- Bundled whole-map universal property of a general under-slice. -/
structure UniversalProperty (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) where
  /-- The canonical evaluation map from the join with the under-slice. -/
  evaluation : K ⋆ sliceUnder X f ⟶ X
  /-- Evaluation restricts to the fixed left factor. -/
  joinInl_evaluation : SSet.joinInl K (sliceUnder X f) ≫ evaluation = f
  /-- Evaluation restricts to the slice projection on the free factor. -/
  joinInr_evaluation : SSet.joinInr K (sliceUnder X f) ≫ evaluation =
    sliceUnder.proj X f
  /-- Evaluation recovers every whole join map stored by a slice simplex. -/
  evaluation_wholeMap : ∀ (n : SimplexCategory)
    (g : (sliceUnder X f).obj (op n)),
    (SSet.join.obj K).map (SSet.yonedaEquiv.symm g) ≫ evaluation = g.1
  /-- The whole-map equivalence, natural in the free simplicial set. -/
  homEquiv : ∀ A : SSet.{u},
    (A ⟶ sliceUnder X f) ≃
      { g : K ⋆ A ⟶ X // SSet.joinInl K A ≫ g = f }
  /-- Forward evaluation under the whole-map equivalence. -/
  homEquiv_apply : ∀ (A : SSet.{u}) (φ : A ⟶ sliceUnder X f),
    homEquiv A φ =
      ⟨(SSet.join.obj K).map φ ≫ evaluation, by
        rw [← Category.assoc, SSet.joinInl_comp_map, joinInl_evaluation]⟩
  /-- The inverse whole-map equivalence is the literal slice lift. -/
  homEquiv_symm_apply : ∀ (A : SSet.{u})
    (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f }),
    (homEquiv A).symm g = lift f g

end sliceUnder

namespace Join

private lemma wholeDayMap_sliceUnder.lift {K X A : SSet.{u}} (f : K ⟶ X)
    (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f })
    (n : SimplexCategory) (a : A.obj (op n)) :
    wholeDayMap f n ((sliceUnder.lift f g).app (op n) a) =
      (augDay.obj K ◁ augDay.map (SSet.yonedaEquiv.symm a)) ≫
        (augDayJoinIso K A).inv ≫ augDay.map g.1 := by
  change (augDayJoinIso K (SSet.stdSimplex.obj n)).inv ≫
      augDay.map ((SSet.join.obj K).map (SSet.yonedaEquiv.symm a) ≫ g.1) =
    (augDay.obj K ◁ augDay.map (SSet.yonedaEquiv.symm a)) ≫
      (augDayJoinIso K A).inv ≫ augDay.map g.1
  rw [Functor.map_comp]
  apply (cancel_epi (augDayJoinIso K (SSet.stdSimplex.obj n)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  slice_rhs 1 2 => rw [← augDayJoinIso_naturality_right]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]


/-- Whole-map universal property of the under-slice. -/
private noncomputable def sliceUnderHomEquivImpl (X : SSet.{u}) {K : SSet.{u}}
    (f : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceUnder X f) ≃
      { g : K ⋆ A ⟶ X // SSet.joinInl K A ≫ g = f } where
  toFun φ :=
    ⟨(SSet.join.obj K).map φ ≫ sliceUnderEvaluation f, by
      rw [← Category.assoc, SSet.joinInl_comp_map,
        joinInl_comp_sliceUnderEvaluation]⟩
  invFun := sliceUnder.lift f
  left_inv φ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change (SSet.join.obj K).map (SSet.yonedaEquiv.symm a) ≫
        ((SSet.join.obj K).map φ ≫ sliceUnderEvaluation f) =
      (φ.app n a).1
    rw [← Category.assoc, ← Functor.map_comp,
      SSet.yonedaEquiv_symm_comp]
    exact sliceUnderEvaluation_wholeMap f n.unop (φ.app n a)
  right_inv g := by
    apply Subtype.ext
    have hday : augDay.map
          ((SSet.join.obj K).map (sliceUnder.lift f g) ≫
            sliceUnderEvaluation f) = augDay.map g.1 := by
      apply (cancel_epi (augDayJoinIso K A).inv).mp
      rw [Functor.map_comp, augDay_map_sliceUnderEvaluation]
      rw [← Category.assoc]
      have hnat := augDayJoinIso_naturality_right
        (X := K) (g := sliceUnder.lift f g)
      have hinv : (augDayJoinIso K A).inv ≫
            augDay.map ((SSet.join.obj K).map (sliceUnder.lift f g)) =
          (augDay.obj K ◁ augDay.map (sliceUnder.lift f g)) ≫
            (augDayJoinIso K (sliceUnder X f)).inv := by
        apply (cancel_mono (augDayJoinIso K (sliceUnder X f)).hom).mp
        simp [Category.assoc, hnat]
      rw [hinv, Category.assoc, Iso.inv_hom_id_assoc]
      apply DayFunctor.tensor_hom_ext
      intro a b
      obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
      cases b' with
      | of m =>
          obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
          cases a' with
          | of k =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨z, t⟩ := q
              change A.obj (op m) at t
              let φ := sliceUnder.lift f g
              let s := φ.app (op m) t
              let σ := SSet.yonedaEquiv.symm t
              have ht : (augDay.map φ).natTrans.app
                  (op (WithInitial.of m)) t = s := by rfl
              have hwh := types_congr_hom
                (η_whiskerLeft_app (augDay.obj K) (augDay.obj A)
                  (augDay.obj (sliceUnder X f)) (augDay.map φ)
                  (op (WithInitial.of k)) (op (WithInitial.of m))) (z, t)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
                  (op (WithInitial.of k)) (op (WithInitial.of m)))
                (z, (augDay.map φ).natTrans.app (op (WithInitial.of m)) t)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.obj K).functor.obj (op (WithInitial.of k)) ◁
                    (augDay.map φ).natTrans.app (op (WithInitial.of m)))
                      (z, t) =
                    (z, (augDay.map φ).natTrans.app
                      (op (WithInitial.of m)) t) := rfl
              dsimp only [φ] at hwh ht
              rw [hwh, hext]
              dsimp only [sliceUnderTensorMap]
              rw [hdesc, ht]
              change (underTensorOfComponent f m s
                    (op (WithInitial.of k))) z = _
              change (wholeDayMap f m s).natTrans.app
                  (op (WithInitial.of k) ⊗ op (WithInitial.of m))
                  ((DayFunctor.η (augDay.obj K)
                    (augDay.obj (SSet.stdSimplex.obj m))).app
                      (op (WithInitial.of k), op (WithInitial.of m))
                      (z, SSet.yonedaEquiv
                        (𝟙 (SSet.stdSimplex.obj m)))) = _
              have hm := wholeDayMap_sliceUnder.lift f g m t
              rw [show s = (sliceUnder.lift f g).app (op m) t from rfl, hm]
              have hη := types_congr_hom
                (η_whiskerLeft_app (augDay.obj K)
                  (augDay.obj (SSet.stdSimplex.obj m)) (augDay.obj A)
                  (augDay.map σ) (op (WithInitial.of k))
                  (op (WithInitial.of m)))
                (z, SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)))
              simp only [types_comp_apply] at hη
              have hid : (augDay.map σ).natTrans.app
                  (op (WithInitial.of m))
                  (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) = t := by
                change σ.app (op m)
                    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) = t
                exact SSet.yonedaEquiv_symm_app_id t
              have hext2 :
                  ((augDay.obj K).functor.obj (op (WithInitial.of k)) ◁
                    (augDay.map σ).natTrans.app (op (WithInitial.of m)))
                      (z, SSet.yonedaEquiv
                        (𝟙 (SSet.stdSimplex.obj m))) = (z, t) := by
                exact Prod.ext rfl hid
              rw [hext2] at hη
              exact congrArg
                (fun w => (((augDayJoinIso K A).inv ≫
                  augDay.map g.1).natTrans.app
                    (op (WithInitial.of k) ⊗ op (WithInitial.of m))) w) hη
          | star =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨z, t⟩ := q
              let ptK : (augDay.obj K).functor.obj
                  (op WithInitial.star) := PUnit.unit
              have hz : z = ptK := by
                change (PUnit.unit : PUnit) = PUnit.unit
                rfl
              subst z
              change A.obj (op m) at t
              let φ := sliceUnder.lift f g
              let s := φ.app (op m) t
              let σ := SSet.yonedaEquiv.symm t
              have ht : (augDay.map φ).natTrans.app
                  (op (WithInitial.of m)) t = s := by rfl
              have hwh := types_congr_hom
                (η_whiskerLeft_app (augDay.obj K) (augDay.obj A)
                  (augDay.obj (sliceUnder X f)) (augDay.map φ)
                  (op WithInitial.star) (op (WithInitial.of m))) (ptK, t)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
                  (op WithInitial.star) (op (WithInitial.of m)))
                (ptK, (augDay.map φ).natTrans.app (op (WithInitial.of m)) t)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.obj K).functor.obj (op WithInitial.star) ◁
                    (augDay.map φ).natTrans.app (op (WithInitial.of m)))
                      (ptK, t) =
                    (ptK, (augDay.map φ).natTrans.app
                      (op (WithInitial.of m)) t) := rfl
              dsimp only [φ] at hwh ht
              rw [hwh, hext]
              dsimp only [sliceUnderTensorMap]
              rw [hdesc, ht]
              change (sliceUnder.proj X f).app (op m) s = _
              let e : (augDay.obj (SSet.stdSimplex.obj m)).functor.obj
                  (op (WithInitial.of m)) :=
                SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))
              have hj := joinInrDayMap_app_of K (SSet.stdSimplex.obj m) m e
              have hc := congrArg DayFunctor.Hom.natTrans
                (joinInrDayMap_comp_wholeDayMap f m s)
              have hcapp := types_congr_hom
                (NatTrans.congr_app hc (op (WithInitial.of m))) e
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                types_comp_apply] at hcapp
              have hproj : (sliceUnder.proj X f).app (op m) s =
                  (wholeDayMap f m s).natTrans.app
                    (op (WithInitial.of m))
                    ((DayFunctor.η (augDay.obj K)
                      (augDay.obj (SSet.stdSimplex.obj m))).app
                        (op WithInitial.star, op (WithInitial.of m))
                        (ptK, e)) := by
                rw [← hj]
                rw [hcapp]
                rfl
              rw [hproj]
              have hm := wholeDayMap_sliceUnder.lift f g m t
              rw [show s = (sliceUnder.lift f g).app (op m) t from rfl, hm]
              have hη := types_congr_hom
                (η_whiskerLeft_app (augDay.obj K)
                  (augDay.obj (SSet.stdSimplex.obj m)) (augDay.obj A)
                  (augDay.map σ) (op WithInitial.star)
                  (op (WithInitial.of m))) (ptK, e)
              simp only [types_comp_apply] at hη
              have hid : (augDay.map σ).natTrans.app
                  (op (WithInitial.of m)) e = t := by
                change σ.app (op m) e = t
                exact SSet.yonedaEquiv_symm_app_id t
              have hext2 :
                  ((augDay.obj K).functor.obj (op WithInitial.star) ◁
                    (augDay.map σ).natTrans.app (op (WithInitial.of m)))
                      (ptK, e) = (ptK, t) := by
                exact Prod.ext rfl hid
              rw [hext2] at hη
              exact congrArg
                (fun w => (((augDayJoinIso K A).inv ≫ augDay.map g.1).natTrans.app
                  (op WithInitial.star ⊗ op (WithInitial.of m))) w) hη
      | star =>
          obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
          cases a' with
          | of k =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨z, t⟩ := q
              let ptA : (augDay.obj A).functor.obj
                  (op WithInitial.star) := PUnit.unit
              have ht : t = ptA := by
                change (PUnit.unit : PUnit) = PUnit.unit
                rfl
              subst t
              let φ := sliceUnder.lift f g
              let ptS : (augDay.obj (sliceUnder X f)).functor.obj
                  (op WithInitial.star) :=
                (augDay.map φ).natTrans.app (op WithInitial.star) ptA
              have hwh := types_congr_hom
                (η_whiskerLeft_app (augDay.obj K) (augDay.obj A)
                  (augDay.obj (sliceUnder X f)) (augDay.map φ)
                  (op (WithInitial.of k)) (op WithInitial.star)) (z, ptA)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceUnderTensorNatTrans f)
                  (op (WithInitial.of k)) (op WithInitial.star)) (z, ptS)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.obj K).functor.obj (op (WithInitial.of k)) ◁
                    (augDay.map φ).natTrans.app (op WithInitial.star))
                      (z, ptA) = (z, ptS) := rfl
              dsimp only [φ] at hwh
              rw [hwh, hext]
              dsimp only [sliceUnderTensorMap]
              rw [hdesc]
              change f.app (op k) z =
                ((augDayJoinIso K A).inv ≫ augDay.map g.1).natTrans.app
                  (op (WithInitial.of k))
                  ((DayFunctor.η (augDay.obj K) (augDay.obj A)).app
                    (op (WithInitial.of k), op WithInitial.star) (z, ptA))
              have hj := joinInlDayMap_app_of K A k z
              have hc : joinInlDayMap K A ≫
                    ((augDayJoinIso K A).inv ≫ augDay.map g.1) =
                  augDay.map f := by
                rw [← augDay_map_joinInl_comp_augDayJoinIso_hom]
                simp only [Category.assoc, Iso.hom_inv_id_assoc,
                  ← Functor.map_comp, g.2]
              have hcapp := types_congr_hom
                (NatTrans.congr_app (congrArg DayFunctor.Hom.natTrans hc)
                  (op (WithInitial.of k))) z
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                types_comp_apply] at hcapp
              rw [← hj]
              exact hcapp.symm
          | star =>
              apply TypeCat.homEquiv.injective
              funext q
              change (PUnit.unit : PUnit) = PUnit.unit
              rfl
    exact congrArg dropDay.map hday


private noncomputable def wholeDayMapOver {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceOver X f).obj (op n)) :
    augDay.obj (SSet.stdSimplex.obj n) ⊗ augDay.obj K ⟶ augDay.obj X :=
  (augDayJoinIso (SSet.stdSimplex.obj n) K).inv ≫ augDay.map g.1

private lemma joinInrDayMap_comp_wholeDayMapOver {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceOver X f).obj (op n)) :
    joinInrDayMap (SSet.stdSimplex.obj n) K ≫ wholeDayMapOver f n g =
      augDay.map f := by
  rw [← augDay_map_joinInr_comp_augDayJoinIso_hom]
  simp only [wholeDayMapOver, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp]
  rw [g.2]

private lemma joinInlDayMap_comp_wholeDayMapOver {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (SSet.sliceOver X f).obj (op n)) :
    joinInlDayMap (SSet.stdSimplex.obj n) K ≫ wholeDayMapOver f n g =
      augDay.map (SSet.joinInl (SSet.stdSimplex.obj n) K ≫ g.1) := by
  rw [← augDay_map_joinInl_comp_augDayJoinIso_hom]
  simp only [wholeDayMapOver, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.map_comp]

private def sliceOverTensorComponent {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (b : AugmentedSimplexCategory) :
    ((augDay.obj (sliceOver X f)).functor ⊠ (augDay.obj K).functor).obj
        (op (WithInitial.of n), op b) ⟶
      (augDay.obj X).functor.obj (op (WithInitial.of n ⊗ b)) :=
  ↾fun q =>
    ((wholeDayMapOver f n q.1).natTrans.app
      (op (WithInitial.of n) ⊗ op b)
      ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
        (augDay.obj K)).app
          (op (WithInitial.of n), op b)
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), q.2)))

private lemma wholeDayMapOver_map {K X : SSet.{u}} (f : K ⟶ X)
    {n m : SimplexCategory} (α : op n ⟶ op m)
    (g : (sliceOver X f).obj (op n)) :
    (augDay.map (SSet.stdSimplex.map α.unop) ▷ augDay.obj K) ≫
        wholeDayMapOver f n g =
      wholeDayMapOver f m ((sliceOver X f).map α g) := by
  apply (cancel_epi (augDayJoinIso (SSet.stdSimplex.obj m) K).hom).mp
  simp only [wholeDayMapOver, sliceOver.map_val, Functor.map_comp]
  slice_lhs 1 2 => rw [← augDayJoinIso_naturality_left]
  simp

private noncomputable def overTensorOfComponent {K X : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (sliceOver X f).obj (op n))
    (b : AugmentedSimplexCategoryᵒᵖ) :
    (augDay.obj K).functor.obj b ⟶
      (augDay.obj X).functor.obj (op (WithInitial.of n) ⊗ b) :=
  ↾fun z =>
    (wholeDayMapOver f n g).natTrans.app (op (WithInitial.of n) ⊗ b)
      ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
        (augDay.obj K)).app
          (op (WithInitial.of n), b)
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z))

private lemma overTensorOfComponent_naturality_left
    {K X : SSet.{u}} (f : K ⟶ X)
    {n m : SimplexCategory} (α : op n ⟶ op m)
    (g : (sliceOver X f).obj (op n))
    (b : AugmentedSimplexCategoryᵒᵖ) :
    overTensorOfComponent f m ((sliceOver X f).map α g) b =
      overTensorOfComponent f n g b ≫
        (augDay.obj X).functor.map
          (AugmentedSimplexCategory.inclusion.op.map α ⊗ₘ 𝟙 b) := by
  apply TypeCat.homEquiv.injective
  funext z
  have hmap := congrArg DayFunctor.Hom.natTrans
    (wholeDayMapOver_map f α g)
  change (wholeDayMapOver f m ((sliceOver X f).map α g)).natTrans.app
        (op (WithInitial.of m) ⊗ b)
      ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj m))
        (augDay.obj K)).app
          (op (WithInitial.of m), b)
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)), z)) =
    (augDay.obj X).functor.map
        (AugmentedSimplexCategory.inclusion.op.map α ⊗ₘ 𝟙 b)
      ((wholeDayMapOver f n g).natTrans.app (op (WithInitial.of n) ⊗ b)
        ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
          (augDay.obj K)).app
            (op (WithInitial.of n), b)
            (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z)))
  rw [← hmap]
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app, types_comp_apply]
  have hη := types_congr_hom
    (η_whiskerRight_app
      (augDay.obj (SSet.stdSimplex.obj m))
      (augDay.obj (SSet.stdSimplex.obj n))
      (augDay.obj K)
      (augDay.map (SSet.stdSimplex.map α.unop))
      (op (WithInitial.of m)) b)
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)), z)
  simp only [types_comp_apply] at hη
  rw [hη]
  have hident :
      (augDay.map (SSet.stdSimplex.map α.unop)).natTrans.app
          (op (WithInitial.of m))
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) =
        (augDay.obj (SSet.stdSimplex.obj n)).functor.map
          (AugmentedSimplexCategory.inclusion.op.map α)
          (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) := by
    rfl
  rw [CategoryTheory.whiskerRight_apply, hident]
  let τ := DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
      (augDay.obj K) ≫
    Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      (wholeDayMapOver f n g).natTrans
  have h := types_congr_hom
    (τ.naturality
      (AugmentedSimplexCategory.inclusion.op.map α ×ₘ 𝟙 b))
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z)
  simp only [types_comp_apply, Functor.comp_map, tensor_map,
    externalProductBifunctor_obj_map] at h
  rw [CategoryTheory.whiskerLeft_apply] at h
  simp [τ, NatTrans.comp_app] at h
  change
    (wholeDayMapOver f n g).natTrans.app (op (WithInitial.of m) ⊗ b)
        ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
          (augDay.obj K)).app
            (op (WithInitial.of m), b)
            ((augDay.obj (SSet.stdSimplex.obj n)).functor.map
              (AugmentedSimplexCategory.inclusion.op.map α)
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))), z)) =
      (augDay.obj X).functor.map
          (AugmentedSimplexCategory.inclusion.op.map α ⊗ₘ 𝟙 b)
        ((wholeDayMapOver f n g).natTrans.app
          (op (WithInitial.of n) ⊗ b)
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
            (augDay.obj K)).app
              (op (WithInitial.of n), b)
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z))) at h
  exact h

private lemma sliceOverTensorComponent_naturality_left {K X : SSet.{u}}
    (f : K ⟶ X) {n m : SimplexCategory}
    (β : op (WithInitial.of n) ⟶ op (WithInitial.of m))
    (b : AugmentedSimplexCategory) :
    (augDay.obj (sliceOver X f)).functor.map β ▷
        (augDay.obj K).functor.obj (op b) ≫
        sliceOverTensorComponent f m b =
      sliceOverTensorComponent f n b ≫
        (augDay.obj X).functor.map (β ⊗ₘ 𝟙 (op b)) := by
  let α : op n ⟶ op m := (WithInitial.down β.unop).op
  have hβ : AugmentedSimplexCategory.inclusion.op.map α = β := rfl
  apply TypeCat.homEquiv.injective
  funext q
  obtain ⟨g, z⟩ := q
  simp [TypeCat.homEquiv_apply, comp_apply]
  change overTensorOfComponent f m ((sliceOver X f).map α g) (op b) z =
    (augDay.obj X).functor.map (β ⊗ₘ 𝟙 (op b))
      (overTensorOfComponent f n g (op b) z)
  rw [← hβ]
  exact types_congr_hom
    (overTensorOfComponent_naturality_left f α g (op b)) z

private lemma sliceOverTensorComponent_naturality_right {K X : SSet.{u}}
    (f : K ⟶ X) (n : SimplexCategory)
    {b d : AugmentedSimplexCategory} (h : op b ⟶ op d) :
    (augDay.obj (sliceOver X f)).functor.obj (op (WithInitial.of n)) ◁
        (augDay.obj K).functor.map h ≫
        sliceOverTensorComponent f n d =
      sliceOverTensorComponent f n b ≫
        (augDay.obj X).functor.map
          (𝟙 (op (WithInitial.of n)) ⊗ₘ h) := by
  apply TypeCat.homEquiv.injective
  funext q
  change ((sliceOver X f).obj (op n) ×
    (augDay.obj K).functor.obj (op b)) at q
  obtain ⟨g, z⟩ := q
  let θ := wholeDayMapOver f n g
  let e : (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
      (op (WithInitial.of n)) :=
    SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))
  have hη := types_congr_hom
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
      (augDay.obj K)).naturality
        ((𝟙 (op (WithInitial.of n)), h) :
          (op (WithInitial.of n), op b) ⟶
            (op (WithInitial.of n), op d))) (e, z)
  have hθ := types_congr_hom
    (θ.natTrans.naturality
      (𝟙 (op (WithInitial.of n)) ⊗ₘ h))
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
      (augDay.obj K)).app
        (op (WithInitial.of n), op b) (e, z))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      (DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
        (augDay.obj K)).app
          (op (WithInitial.of n), op d)
          (((augDay.obj (SSet.stdSimplex.obj n)).functor.obj
            (op (WithInitial.of n)) ◁ (augDay.obj K).functor.map h)
            (e, z)) =
        (augDay.obj (SSet.stdSimplex.obj n) ⊗ augDay.obj K).functor.map
          (𝟙 (op (WithInitial.of n)) ⊗ₘ h)
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
            (augDay.obj K)).app
              (op (WithInitial.of n), op b) (e, z)) := hη
  change θ.natTrans.app (op (WithInitial.of n) ⊗ op d)
      ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
        (augDay.obj K)).app
          (op (WithInitial.of n), op d)
          (((augDay.obj (SSet.stdSimplex.obj n)).functor.obj
            (op (WithInitial.of n)) ◁ (augDay.obj K).functor.map h)
            (e, z))) =
    (augDay.obj X).functor.map (𝟙 (op (WithInitial.of n)) ⊗ₘ h)
      (θ.natTrans.app (op (WithInitial.of n) ⊗ op b)
        ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
          (augDay.obj K)).app
            (op (WithInitial.of n), op b) (e, z)))
  rw [hη']
  exact hθ

private lemma sliceOverTensorComponent_boundary_left
    {K X : SSet.{u}} (f : K ⟶ X)
    {a b d : SimplexCategory}
    (h1 : op (WithInitial.of a) ⟶ op WithInitial.star)
    (h2 : op (WithInitial.of b) ⟶ op (WithInitial.of d))
    (q1 : (sliceOver X f).obj (op a))
    (q2 : (augDay.obj K).functor.obj (op (WithInitial.of b))) :
    (augDay.obj X).functor.map (h1 ⊗ₘ h2)
        ((wholeDayMapOver f a q1).natTrans.app
          (op (WithInitial.of a) ⊗ op (WithInitial.of b))
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
            (augDay.obj K)).app
              (op (WithInitial.of a), op (WithInitial.of b))
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj a)), q2))) =
      (augDay.map f).natTrans.app (op (WithInitial.of d))
        ((augDay.obj K).functor.map h2 q2) := by
  let θ := wholeDayMapOver f a q1
  let e := SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj a))
  have hη := types_congr_hom
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
      (augDay.obj K)).naturality
        ((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op WithInitial.star, op (WithInitial.of d)))) (e, q2)
  have hθ := types_congr_hom
    (θ.natTrans.naturality (h1 ⊗ₘ h2))
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
      (augDay.obj K)).app
        (op (WithInitial.of a), op (WithInitial.of b)) (e, q2))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      (DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
        (augDay.obj K)).app
          (op WithInitial.star, op (WithInitial.of d))
          (((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).map (h1, h2)
            ((e, q2) :
              ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
                (augDay.obj K).functor).obj
                  (op (WithInitial.of a), op (WithInitial.of b)))) =
        (augDay.obj (SSet.stdSimplex.obj a) ⊗ augDay.obj K).functor.map
          (h1 ⊗ₘ h2)
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
            (augDay.obj K)).app
              (op (WithInitial.of a), op (WithInitial.of b)) (e, q2)) := hη
  rw [← hθ, ← hη']
  have he : (augDay.obj (SSet.stdSimplex.obj a)).functor.map h1 e =
      PUnit.unit := by
    change (PUnit.unit : PUnit) = PUnit.unit
    rfl
  have hext :
      ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
        (augDay.obj K).functor).map
        (((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op WithInitial.star, op (WithInitial.of d))))
        ((e, q2) :
          ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).obj
              (op (WithInitial.of a), op (WithInitial.of b))) =
        ((PUnit.unit, (augDay.obj K).functor.map h2 q2) :
          ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).obj
              (op WithInitial.star, op (WithInitial.of d))) := by
    simp only [externalProductBifunctor_obj_map]
    rw [CategoryTheory.comp_apply, CategoryTheory.whiskerRight_apply,
      CategoryTheory.whiskerLeft_apply]
    exact Prod.ext he rfl
  rw [hext]
  rw [← joinInrDayMap_app_of (SSet.stdSimplex.obj a) K d
    ((augDay.obj K).functor.map h2 q2)]
  have hr := congrArg DayFunctor.Hom.natTrans
    (joinInrDayMap_comp_wholeDayMapOver f a q1)
  exact types_congr_hom
    (NatTrans.congr_app hr (op (WithInitial.of d)))
    ((augDay.obj K).functor.map h2 q2)

private lemma sliceOverTensorComponent_boundary_right
    {K X : SSet.{u}} (f : K ⟶ X)
    {a c b : SimplexCategory}
    (h1 : op (WithInitial.of a) ⟶ op (WithInitial.of c))
    (h2 : op (WithInitial.of b) ⟶ op WithInitial.star)
    (q1 : (sliceOver X f).obj (op a))
    (q2 : (augDay.obj K).functor.obj (op (WithInitial.of b))) :
    (augDay.obj X).functor.map (h1 ⊗ₘ h2)
        ((wholeDayMapOver f a q1).natTrans.app
          (op (WithInitial.of a) ⊗ op (WithInitial.of b))
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
            (augDay.obj K)).app
              (op (WithInitial.of a), op (WithInitial.of b))
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj a)), q2))) =
      (sliceOver.proj X f).app (op c)
        ((sliceOver X f).map (WithInitial.down h1.unop).op q1) := by
  let θ := wholeDayMapOver f a q1
  let e := SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj a))
  let α : op a ⟶ op c := (WithInitial.down h1.unop).op
  have hη := types_congr_hom
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
      (augDay.obj K)).naturality
        ((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op (WithInitial.of c), op WithInitial.star))) (e, q2)
  have hθ := types_congr_hom
    (θ.natTrans.naturality (h1 ⊗ₘ h2))
    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
      (augDay.obj K)).app
        (op (WithInitial.of a), op (WithInitial.of b)) (e, q2))
  simp only [types_comp_apply] at hη hθ
  have hη' :
      (DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
        (augDay.obj K)).app
          (op (WithInitial.of c), op WithInitial.star)
          (((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).map (h1, h2)
            ((e, q2) :
              ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
                (augDay.obj K).functor).obj
                  (op (WithInitial.of a), op (WithInitial.of b)))) =
        (augDay.obj (SSet.stdSimplex.obj a) ⊗ augDay.obj K).functor.map
          (h1 ⊗ₘ h2)
          ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj a))
            (augDay.obj K)).app
              (op (WithInitial.of a), op (WithInitial.of b)) (e, q2)) := hη
  rw [← hθ, ← hη']
  have hk : (augDay.obj K).functor.map h2 q2 = PUnit.unit := by
    change (PUnit.unit : PUnit) = PUnit.unit
    rfl
  let e' := (augDay.obj (SSet.stdSimplex.obj a)).functor.map h1 e
  have hext :
      ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
        (augDay.obj K).functor).map
        (((h1, h2) :
          (op (WithInitial.of a), op (WithInitial.of b)) ⟶
            (op (WithInitial.of c), op WithInitial.star)))
        ((e, q2) :
          ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).obj
              (op (WithInitial.of a), op (WithInitial.of b))) =
        ((e', PUnit.unit) :
          ((augDay.obj (SSet.stdSimplex.obj a)).functor ⊠
            (augDay.obj K).functor).obj
              (op (WithInitial.of c), op WithInitial.star)) := by
    simp only [externalProductBifunctor_obj_map]
    rw [CategoryTheory.comp_apply, CategoryTheory.whiskerRight_apply,
      CategoryTheory.whiskerLeft_apply]
    exact Prod.ext rfl hk
  rw [hext]
  rw [← joinInlDayMap_app_of (SSet.stdSimplex.obj a) K c e']
  have hr := congrArg DayFunctor.Hom.natTrans
    (joinInlDayMap_comp_wholeDayMapOver f a q1)
  rw [show θ = wholeDayMapOver f a q1 from rfl]
  change (wholeDayMapOver f a q1).natTrans.app (op (WithInitial.of c))
      ((joinInlDayMap (SSet.stdSimplex.obj a) K).natTrans.app
        (op (WithInitial.of c)) e') = _
  have hrapp := types_congr_hom
    (NatTrans.congr_app hr (op (WithInitial.of c))) e'
  rw [dayCompNatTrans, NatTrans.comp_app] at hrapp
  simp only [types_comp_apply] at hrapp
  rw [hrapp]
  change (SSet.joinInl (SSet.stdSimplex.obj a) K ≫ q1.1).app (op c) e' = _
  change SSet.yonedaEquiv
      (SSet.stdSimplex.map α.unop ≫
        SSet.joinInl (SSet.stdSimplex.obj a) K ≫ q1.1) = _
  rw [← Category.assoc, SSet.map_comp_joinInl]
  rfl

private def sliceOverTensorNatTrans {K X : SSet.{u}} (f : K ⟶ X) :
    ((augDay.obj (sliceOver X f)).functor ⊠ (augDay.obj K).functor) ⟶
      tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor where
  app z := WithInitial.rec
    (motive := fun a : AugmentedSimplexCategory =>
      ((augDay.obj (sliceOver X f)).functor ⊠ (augDay.obj K).functor).obj
          (op a, z.2) ⟶
        (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj
          (op a, z.2))
    (fun m => WithInitial.rec
      (motive := fun b : AugmentedSimplexCategory =>
        ((augDay.obj (sliceOver X f)).functor ⊠ (augDay.obj K).functor).obj
            (op (WithInitial.of m), op b) ⟶
          (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj
            (op (WithInitial.of m), op b))
      (fun n => sliceOverTensorComponent f m (WithInitial.of n))
      (↾fun q => (sliceOver.proj X f).app (op m) q.1)
      z.2.unop)
    (WithInitial.rec
      (motive := fun b : AugmentedSimplexCategory =>
        ((augDay.obj (sliceOver X f)).functor ⊠ (augDay.obj K).functor).obj
            (op WithInitial.star, op b) ⟶
          (tensor AugmentedSimplexCategoryᵒᵖ ⋙ (augDay.obj X).functor).obj
            (op WithInitial.star, op b))
      (fun n => ↾fun q => f.app (op n) q.2)
      (↾fun _ => PUnit.unit)
      z.2.unop)
    z.1.unop
  naturality := by
    intro x y h
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = op c' := ⟨c.unop, rfl⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = op d' := ⟨d.unop, rfl⟩
    cases a' <;> cases b' <;> cases c' <;> cases d' <;>
      try { exact (WithInitial.false_of_to_star h.1.unop).elim } <;>
      try { exact (WithInitial.false_of_to_star h.2.unop).elim }
    case of.of.of.of =>
      rename_i a b c d
      rw [externalProductBifunctor_obj_map]
      dsimp
      rw [Category.assoc]
      slice_lhs 2 3 =>
        rw [sliceOverTensorComponent_naturality_right f c h.2]
      rw [← Category.assoc]
      rw [sliceOverTensorComponent_naturality_left f h.1 (WithInitial.of b)]
      rw [Category.assoc, ← Functor.map_comp]
      congr 2
      simp [MonoidalCategory.tensorHom_def]
    case of.of.of.star =>
      apply TypeCat.homEquiv.injective
      funext q
      obtain ⟨q1, q2⟩ := q
      dsimp [sliceOverTensorComponent]
      exact (sliceOverTensorComponent_boundary_right
        f h.1 h.2 q1 q2).symm
    case of.of.star.of =>
      apply TypeCat.homEquiv.injective
      funext q
      obtain ⟨q1, q2⟩ := q
      dsimp [sliceOverTensorComponent]
      exact (sliceOverTensorComponent_boundary_left
        f h.1 h.2 q1 q2).symm
    case of.of.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case of.star.of.star =>
      apply TypeCat.homEquiv.injective
      funext q
      dsimp
      have h2id : h.2 = 𝟙 _ := Subsingleton.elim _ _
      rw [h2id]
      have hp := types_congr_hom ((sliceOver.proj X f).naturality h.1) q.1
      exact hp
    case of.star.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case star.of.star.of =>
      apply TypeCat.homEquiv.injective
      funext q
      dsimp
      have h1id : h.1 = 𝟙 _ := Subsingleton.elim _ _
      rw [h1id]
      have hf := types_congr_hom (f.naturality h.2) q.2
      exact hf
    case star.of.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl
    case star.star.star.star =>
      apply TypeCat.homEquiv.injective
      funext q
      change (PUnit.unit : PUnit) = PUnit.unit
      rfl

private noncomputable def sliceOverTensorMap {K X : SSet.{u}} (f : K ⟶ X) :
    augDay.obj (sliceOver X f) ⊗ augDay.obj K ⟶ augDay.obj X :=
  DayFunctor.tensorDesc (sliceOverTensorNatTrans f)

private noncomputable def sliceOverEvaluation {K X : SSet.{u}} (f : K ⟶ X) :
    sliceOver X f ⋆ K ⟶ X :=
  dropDay.map (sliceOverTensorMap f)

private lemma augDay_map_sliceOverEvaluation {K X : SSet.{u}} (f : K ⟶ X) :
    augDay.map (sliceOverEvaluation f) =
      (augDayJoinIso (sliceOver X f) K).hom ≫ sliceOverTensorMap f := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n => rfl
  | star => apply Types.isTerminalPUnit.hom_ext

private lemma η_comp_sliceOverTensorMap {K X : SSet.{u}} (f : K ⟶ X) :
    DayFunctor.η (augDay.obj (sliceOver X f)) (augDay.obj K) ≫
        Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
          (sliceOverTensorMap f).natTrans =
      sliceOverTensorNatTrans f :=
  DayFunctor.η_comp_tensorDec _

private lemma joinInlDayMap_comp_sliceOverTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) :
    joinInlDayMap (sliceOver X f) K ≫ sliceOverTensorMap f =
      augDay.map (sliceOver.proj X f) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      apply TypeCat.homEquiv.injective
      funext z
      have hη := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (sliceOverTensorNatTrans f)
          (op (WithInitial.of n)) (op WithInitial.star))
        (z, PUnit.unit)
      simp only [types_comp_apply] at hη
      change (sliceOverTensorMap f).natTrans.app
          (op (WithInitial.of n))
          ((joinInlDayMap (sliceOver X f) K).natTrans.app
            (op (WithInitial.of n)) z) =
        (augDay.map (sliceOver.proj X f)).natTrans.app
          (op (WithInitial.of n)) z
      change (sliceOver X f).obj (op n) at z
      have hj := joinInlDayMap_app_of (sliceOver X f) K n z
      rw [hj]
      exact hη
  | star =>
      apply Types.isTerminalPUnit.hom_ext

private lemma joinInrDayMap_comp_sliceOverTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) :
    joinInrDayMap (sliceOver X f) K ≫ sliceOverTensorMap f =
      augDay.map f := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      apply TypeCat.homEquiv.injective
      funext z
      have hη := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (sliceOverTensorNatTrans f)
          (op WithInitial.star) (op (WithInitial.of n)))
        (PUnit.unit, z)
      simp only [types_comp_apply] at hη
      change (sliceOverTensorMap f).natTrans.app
          (op (WithInitial.of n))
          ((joinInrDayMap (sliceOver X f) K).natTrans.app
            (op (WithInitial.of n)) z) =
        (augDay.map f).natTrans.app (op (WithInitial.of n)) z
      change K.obj (op n) at z
      have hj := joinInrDayMap_app_of (sliceOver X f) K n z
      rw [hj]
      exact hη
  | star =>
      apply Types.isTerminalPUnit.hom_ext

private lemma joinInl_comp_sliceOverEvaluation {K X : SSet.{u}}
    (f : K ⟶ X) :
    SSet.joinInl (sliceOver X f) K ≫ sliceOverEvaluation f =
      sliceOver.proj X f := by
  have hday : augDay.map
        (SSet.joinInl (sliceOver X f) K ≫ sliceOverEvaluation f) =
      augDay.map (sliceOver.proj X f) := by
    rw [Functor.map_comp, augDay_map_sliceOverEvaluation, ← Category.assoc,
      augDay_map_joinInl_comp_augDayJoinIso_hom,
      joinInlDayMap_comp_sliceOverTensorMap]
  exact congrArg dropDay.map hday

private lemma joinInr_comp_sliceOverEvaluation {K X : SSet.{u}}
    (f : K ⟶ X) :
    SSet.joinInr (sliceOver X f) K ≫ sliceOverEvaluation f = f := by
  have hday : augDay.map
        (SSet.joinInr (sliceOver X f) K ≫ sliceOverEvaluation f) =
      augDay.map f := by
    rw [Functor.map_comp, augDay_map_sliceOverEvaluation, ← Category.assoc,
      augDay_map_joinInr_comp_augDayJoinIso_hom,
      joinInrDayMap_comp_sliceOverTensorMap]
  exact congrArg dropDay.map hday

private lemma whisker_yoneda_comp_sliceOverTensorMap
    {K X : SSet.{u}} (f : K ⟶ X) (n : SimplexCategory)
    (g : (sliceOver X f).obj (op n)) :
    (augDay.map (SSet.yonedaEquiv.symm g) ▷ augDay.obj K) ≫
        sliceOverTensorMap f =
      wholeDayMapOver f n g := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
  cases a' with
  | of m =>
      obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
      cases b' with
      | of k =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨t, z⟩ := q
          let α : op n ⟶ op m := (SSet.stdSimplex.objEquiv t).op
          let σ := SSet.yonedaEquiv.symm g
          have ht : (augDay.map σ).natTrans.app
              (op (WithInitial.of m)) t =
              (sliceOver X f).map α g := by rfl
          have hwh := types_congr_hom
            (η_whiskerRight_app
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceOver X f)) (augDay.obj K)
              (augDay.map σ)
              (op (WithInitial.of m)) (op (WithInitial.of k))) (t, z)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
              (op (WithInitial.of m)) (op (WithInitial.of k)))
            ((augDay.map σ).natTrans.app (op (WithInitial.of m)) t, z)
          have hcomp := types_congr_hom
            (overTensorOfComponent_naturality_left f α g
              (op (WithInitial.of k))) z
          have hext :
              ((augDay.map σ).natTrans.app (op (WithInitial.of m)) ▷
                (augDay.obj K).functor.obj (op (WithInitial.of k)))
                  (t, z) =
                ((augDay.map σ).natTrans.app
                  (op (WithInitial.of m)) t, z) := rfl
          simp only [types_comp_apply] at hwh hdesc hcomp
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceOverTensorMap]
          rw [hdesc, ht]
          change overTensorOfComponent f m
              ((sliceOver X f).map α g) (op (WithInitial.of k)) z = _
          rw [hcomp]
          have hident :
              (augDay.obj (SSet.stdSimplex.obj n)).functor.map
                (AugmentedSimplexCategory.inclusion.op.map α)
                (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) = t := by
            change (SSet.stdSimplex.obj n).map α
              (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n))) = t
            have hid : SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)) =
                SSet.stdSimplex.objEquiv.symm (𝟙 n) := by
              simpa using SSet.yonedaEquiv_map (𝟙 n)
            rw [hid, SSet.stdSimplex.map_objEquiv_symm]
            apply SSet.stdSimplex.objEquiv.injective
            simp [α]
          let β : op (WithInitial.of n) ⟶ op (WithInitial.of m) :=
            (WithInitial.incl.map α.unop).op
          have hηidx := types_congr_hom
            ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj K)).naturality
                ((β, 𝟙 (op (WithInitial.of k))) :
                  (op (WithInitial.of n), op (WithInitial.of k)) ⟶
                    (op (WithInitial.of m), op (WithInitial.of k))))
            (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z)
          have hwhole := types_congr_hom
            ((wholeDayMapOver f n g).natTrans.naturality
              (β ⊗ₘ 𝟙 (op (WithInitial.of k))))
            ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj K)).app
                (op (WithInitial.of n), op (WithInitial.of k))
                (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z))
          simp only [types_comp_apply] at hηidx hwhole
          have hextidx :
              (((augDay.obj (SSet.stdSimplex.obj n)).functor ⊠
                (augDay.obj K).functor).map
                  ((β, 𝟙 (op (WithInitial.of k))) :
                    (op (WithInitial.of n), op (WithInitial.of k)) ⟶
                      (op (WithInitial.of m), op (WithInitial.of k))))
                ((SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)), z) :
                  ((augDay.obj (SSet.stdSimplex.obj n)).functor ⊠
                    (augDay.obj K).functor).obj
                      (op (WithInitial.of n), op (WithInitial.of k))) =
              (t, z) := by
            simpa [externalProductBifunctor_obj_map] using
              (Prod.ext hident (by rfl))
          rw [hextidx] at hηidx
          change (augDay.obj X).functor.map
              (β ⊗ₘ 𝟙 (op (WithInitial.of k)))
              (overTensorOfComponent f n g
                (op (WithInitial.of k)) z) =
            (wholeDayMapOver f n g).natTrans.app
              (op (WithInitial.of m) ⊗ op (WithInitial.of k))
              ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
                (augDay.obj K)).app
                  (op (WithInitial.of m), op (WithInitial.of k)) (t, z))
          rw [hηidx]
          exact hwhole.symm
      | star =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨t, z⟩ := q
          let ptK : (augDay.obj K).functor.obj
              (op WithInitial.star) := PUnit.unit
          have hz : z = ptK := by
            change (PUnit.unit : PUnit) = PUnit.unit
            rfl
          subst z
          let α : op n ⟶ op m := (SSet.stdSimplex.objEquiv t).op
          let σ := SSet.yonedaEquiv.symm g
          have ht : (augDay.map σ).natTrans.app
              (op (WithInitial.of m)) t = (sliceOver X f).map α g := by
            rfl
          have hwh := types_congr_hom
            (η_whiskerRight_app
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceOver X f)) (augDay.obj K)
              (augDay.map σ)
              (op (WithInitial.of m)) (op WithInitial.star))
            (t, ptK)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
              (op (WithInitial.of m)) (op WithInitial.star))
            ((augDay.map σ).natTrans.app (op (WithInitial.of m)) t, ptK)
          simp only [types_comp_apply] at hwh hdesc
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          have hext :
              ((augDay.map σ).natTrans.app (op (WithInitial.of m)) ▷
                (augDay.obj K).functor.obj (op WithInitial.star))
                  (t, ptK) =
                ((augDay.map σ).natTrans.app
                  (op (WithInitial.of m)) t, ptK) := rfl
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceOverTensorMap]
          rw [hdesc, ht]
          change (sliceOver.proj X f).app (op m)
              ((sliceOver X f).map α g) =
            (wholeDayMapOver f n g).natTrans.app (op (WithInitial.of m))
              ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
                (augDay.obj K)).app
                  (op (WithInitial.of m), op WithInitial.star)
                  (t, ptK))
          have hj := joinInlDayMap_app_of
            (SSet.stdSimplex.obj n) K m t
          have hc := congrArg DayFunctor.Hom.natTrans
            (joinInlDayMap_comp_wholeDayMapOver f n g)
          have hcapp := types_congr_hom
            (NatTrans.congr_app hc (op (WithInitial.of m))) t
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            types_comp_apply] at hcapp
          rw [← hj, hcapp]
          change SSet.yonedaEquiv
              (SSet.joinInl (SSet.stdSimplex.obj m) K ≫
                ((SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1)) =
            (SSet.joinInl (SSet.stdSimplex.obj n) K ≫ g.1).app (op m) t
          rw [← Category.assoc, ← SSet.map_comp_joinInl]
          rw [Category.assoc, ← SSet.yonedaEquiv_naturality]
          have ht' : t = SSet.stdSimplex.objEquiv.symm α.unop := by
            apply SSet.stdSimplex.objEquiv.injective
            simp [α]
          rw [ht']
          symm
          simpa using
            (SSet.yonedaEquiv_symm_app_objEquiv_symm
              (x := SSet.yonedaEquiv
                (SSet.joinInl (SSet.stdSimplex.obj n) K ≫ g.1))
              (f := α.unop))
  | star =>
      obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
      cases b' with
      | of m =>
          apply TypeCat.homEquiv.injective
          funext q
          obtain ⟨t, z⟩ := q
          let ptN : (augDay.obj (SSet.stdSimplex.obj n)).functor.obj
              (op WithInitial.star) := PUnit.unit
          have ht : t = ptN := by
            change (PUnit.unit : PUnit) = PUnit.unit
            rfl
          subst t
          let σ := SSet.yonedaEquiv.symm g
          let ptS : (augDay.obj (sliceOver X f)).functor.obj
              (op WithInitial.star) :=
            (augDay.map σ).natTrans.app (op WithInitial.star) ptN
          have hwh := types_congr_hom
            (η_whiskerRight_app
              (augDay.obj (SSet.stdSimplex.obj n))
              (augDay.obj (sliceOver X f)) (augDay.obj K)
              (augDay.map σ)
              (op WithInitial.star) (op (WithInitial.of m)))
            (ptN, z)
          have hdesc := types_congr_hom
            (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
              (op WithInitial.star) (op (WithInitial.of m)))
            (ptS, z)
          simp only [types_comp_apply] at hwh hdesc
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            TypeCat.homEquiv_apply, comp_apply]
          have hext :
              ((augDay.map σ).natTrans.app (op WithInitial.star) ▷
                (augDay.obj K).functor.obj (op (WithInitial.of m)))
                  (ptN, z) = (ptS, z) := rfl
          dsimp only [σ] at hwh
          rw [hwh, hext]
          dsimp only [sliceOverTensorMap]
          rw [hdesc]
          change f.app (op m) z =
            (wholeDayMapOver f n g).natTrans.app (op (WithInitial.of m))
              ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj n))
                (augDay.obj K)).app
                  (op WithInitial.star, op (WithInitial.of m))
                  (PUnit.unit, z))
          have hj := joinInrDayMap_app_of
            (SSet.stdSimplex.obj n) K m z
          have hc := congrArg DayFunctor.Hom.natTrans
            (joinInrDayMap_comp_wholeDayMapOver f n g)
          have hcapp := types_congr_hom
            (NatTrans.congr_app hc (op (WithInitial.of m))) z
          simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
            types_comp_apply] at hcapp
          rw [← hj]
          exact hcapp.symm
      | star =>
          apply TypeCat.homEquiv.injective
          funext q
          change (PUnit.unit : PUnit) = PUnit.unit
          rfl

private lemma sliceOverEvaluation_wholeMap {K X : SSet.{u}}
    (f : K ⟶ X) (n : SimplexCategory)
    (g : (sliceOver X f).obj (op n)) :
    (SSet.join.map (SSet.yonedaEquiv.symm g)).app K ≫
        sliceOverEvaluation f = g.1 := by
  have hday : augDay.map
        ((SSet.join.map (SSet.yonedaEquiv.symm g)).app K ≫
          sliceOverEvaluation f) = augDay.map g.1 := by
    rw [Functor.map_comp, augDay_map_sliceOverEvaluation,
      ← Category.assoc, SSet.Join.augDayJoinIso_naturality_left,
      Category.assoc, whisker_yoneda_comp_sliceOverTensorMap]
    simp only [wholeDayMapOver, Iso.hom_inv_id_assoc]
  exact congrArg dropDay.map hday

end Join

namespace sliceOver

/-- Recover the over-slice map classified by a compatible whole join map. -/
def lift {K X A : SSet.{u}} (f : K ⟶ X)
    (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f }) :
    A ⟶ sliceOver X f where
  app n := ↾fun a =>
    ⟨(SSet.join.map (SSet.yonedaEquiv.symm a)).app K ≫ g.1, by
      rw [← Category.assoc, SSet.joinInr_comp_map, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change (SSet.join.map
          (SSet.yonedaEquiv.symm (A.map α a))).app K ≫ g.1 =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫
        ((SSet.join.map (SSet.yonedaEquiv.symm a)).app K ≫ g.1)
    have hy := SSet.yonedaEquiv_symm_naturality_left α.unop a
    rw [Quiver.Hom.op_unop] at hy
    rw [← hy, SSet.join.map_comp, NatTrans.comp_app, Category.assoc]

/-- Bundled whole-map universal property of a general over-slice. -/
structure UniversalProperty (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) where
  /-- The canonical evaluation map from the over-slice join. -/
  evaluation : sliceOver X f ⋆ K ⟶ X
  /-- Evaluation restricts to the slice projection on the free factor. -/
  joinInl_evaluation : SSet.joinInl (sliceOver X f) K ≫ evaluation =
    sliceOver.proj X f
  /-- Evaluation restricts to the fixed right factor. -/
  joinInr_evaluation : SSet.joinInr (sliceOver X f) K ≫ evaluation = f
  /-- Evaluation recovers every whole join map stored by a slice simplex. -/
  evaluation_wholeMap : ∀ (n : SimplexCategory)
    (g : (sliceOver X f).obj (op n)),
    (SSet.join.map (SSet.yonedaEquiv.symm g)).app K ≫ evaluation = g.1
  /-- The whole-map equivalence, natural in the free simplicial set. -/
  homEquiv : ∀ A : SSet.{u},
    (A ⟶ sliceOver X f) ≃
      { g : A ⋆ K ⟶ X // SSet.joinInr A K ≫ g = f }
  /-- Forward evaluation under the whole-map equivalence. -/
  homEquiv_apply : ∀ (A : SSet.{u}) (φ : A ⟶ sliceOver X f),
    homEquiv A φ =
      ⟨(SSet.join.map φ).app K ≫ evaluation, by
        rw [← Category.assoc, SSet.joinInr_comp_map, joinInr_evaluation]⟩
  /-- The inverse whole-map equivalence is the literal over-slice lift. -/
  homEquiv_symm_apply : ∀ (A : SSet.{u})
    (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f }),
    (homEquiv A).symm g = lift f g

end sliceOver

namespace Join

private lemma wholeDayMapOver_sliceOver_lift {K X A : SSet.{u}} (f : K ⟶ X)
    (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f })
    (n : SimplexCategory) (a : A.obj (op n)) :
    wholeDayMapOver f n ((sliceOver.lift f g).app (op n) a) =
      (augDay.map (SSet.yonedaEquiv.symm a) ▷ augDay.obj K) ≫
        (augDayJoinIso A K).inv ≫ augDay.map g.1 := by
  change (augDayJoinIso (SSet.stdSimplex.obj n) K).inv ≫
      augDay.map ((SSet.join.map (SSet.yonedaEquiv.symm a)).app K ≫ g.1) =
    (augDay.map (SSet.yonedaEquiv.symm a) ▷ augDay.obj K) ≫
      (augDayJoinIso A K).inv ≫ augDay.map g.1
  rw [Functor.map_comp]
  apply (cancel_epi (augDayJoinIso (SSet.stdSimplex.obj n) K).hom).mp
  rw [Iso.hom_inv_id_assoc]
  slice_rhs 1 2 => rw [← augDayJoinIso_naturality_left]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private noncomputable def sliceOverHomEquivImpl (X : SSet.{u})
    {K : SSet.{u}} (f : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceOver X f) ≃
      { g : A ⋆ K ⟶ X // SSet.joinInr A K ≫ g = f } where
  toFun φ :=
    ⟨(SSet.join.map φ).app K ≫ sliceOverEvaluation f, by
      rw [← Category.assoc, SSet.joinInr_comp_map,
        joinInr_comp_sliceOverEvaluation]⟩
  invFun := sliceOver.lift f
  left_inv φ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change (SSet.join.map (SSet.yonedaEquiv.symm a)).app K ≫
        ((SSet.join.map φ).app K ≫ sliceOverEvaluation f) =
      (φ.app n a).1
    rw [← Category.assoc, ← NatTrans.comp_app, ← SSet.join.map_comp,
      SSet.yonedaEquiv_symm_comp]
    exact sliceOverEvaluation_wholeMap f n.unop (φ.app n a)
  right_inv g := by
    apply Subtype.ext
    have hday : augDay.map
          ((SSet.join.map (sliceOver.lift f g)).app K ≫
            sliceOverEvaluation f) = augDay.map g.1 := by
      apply (cancel_epi (augDayJoinIso A K).inv).mp
      rw [Functor.map_comp, augDay_map_sliceOverEvaluation]
      rw [← Category.assoc]
      have hnat := augDayJoinIso_naturality_left
        (Y := K) (f := sliceOver.lift f g)
      have hinv : (augDayJoinIso A K).inv ≫
            augDay.map ((SSet.join.map (sliceOver.lift f g)).app K) =
          (augDay.map (sliceOver.lift f g) ▷ augDay.obj K) ≫
            (augDayJoinIso (sliceOver X f) K).inv := by
        apply (cancel_mono (augDayJoinIso (sliceOver X f) K).hom).mp
        simp [Category.assoc, hnat]
      rw [hinv, Category.assoc, Iso.inv_hom_id_assoc]
      apply DayFunctor.tensor_hom_ext
      intro a b
      obtain ⟨a', rfl⟩ : ∃ a', a = op a' := ⟨a.unop, rfl⟩
      cases a' with
      | of m =>
          obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
          cases b' with
          | of k =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨t, z⟩ := q
              change A.obj (op m) at t
              let φ := sliceOver.lift f g
              let s := φ.app (op m) t
              let σ := SSet.yonedaEquiv.symm t
              have ht : (augDay.map φ).natTrans.app
                  (op (WithInitial.of m)) t = s := by rfl
              have hwh := types_congr_hom
                (η_whiskerRight_app (augDay.obj A)
                  (augDay.obj (sliceOver X f)) (augDay.obj K)
                  (augDay.map φ)
                  (op (WithInitial.of m)) (op (WithInitial.of k))) (t, z)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
                  (op (WithInitial.of m)) (op (WithInitial.of k)))
                ((augDay.map φ).natTrans.app (op (WithInitial.of m)) t, z)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.map φ).natTrans.app (op (WithInitial.of m)) ▷
                    (augDay.obj K).functor.obj (op (WithInitial.of k)))
                      (t, z) =
                    ((augDay.map φ).natTrans.app
                      (op (WithInitial.of m)) t, z) := rfl
              dsimp only [φ] at hwh ht
              rw [hwh, hext]
              dsimp only [sliceOverTensorMap]
              rw [hdesc, ht]
              change overTensorOfComponent f m s
                  (op (WithInitial.of k)) z = _
              change (wholeDayMapOver f m s).natTrans.app
                  (op (WithInitial.of m) ⊗ op (WithInitial.of k))
                  ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj m))
                    (augDay.obj K)).app
                      (op (WithInitial.of m), op (WithInitial.of k))
                      (SSet.yonedaEquiv
                        (𝟙 (SSet.stdSimplex.obj m)), z)) = _
              have hm := wholeDayMapOver_sliceOver_lift f g m t
              rw [show s = (sliceOver.lift f g).app (op m) t from rfl, hm]
              have hη := types_congr_hom
                (η_whiskerRight_app
                  (augDay.obj (SSet.stdSimplex.obj m))
                  (augDay.obj A) (augDay.obj K)
                  (augDay.map σ) (op (WithInitial.of m))
                  (op (WithInitial.of k)))
                (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m)), z)
              simp only [types_comp_apply] at hη
              have hid : (augDay.map σ).natTrans.app
                  (op (WithInitial.of m))
                  (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) = t := by
                change σ.app (op m)
                    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))) = t
                exact SSet.yonedaEquiv_symm_app_id t
              have hext2 :
                  ((augDay.map σ).natTrans.app (op (WithInitial.of m)) ▷
                    (augDay.obj K).functor.obj (op (WithInitial.of k)))
                      (SSet.yonedaEquiv
                        (𝟙 (SSet.stdSimplex.obj m)), z) = (t, z) := by
                exact Prod.ext hid rfl
              rw [hext2] at hη
              exact congrArg
                (fun w => (((augDayJoinIso A K).inv ≫
                  augDay.map g.1).natTrans.app
                    (op (WithInitial.of m) ⊗ op (WithInitial.of k))) w) hη
          | star =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨t, z⟩ := q
              change A.obj (op m) at t
              let ptK : (augDay.obj K).functor.obj
                  (op WithInitial.star) := PUnit.unit
              have hz : z = ptK := by
                change (PUnit.unit : PUnit) = PUnit.unit
                rfl
              subst z
              let φ := sliceOver.lift f g
              let s := φ.app (op m) t
              let σ := SSet.yonedaEquiv.symm t
              have ht : (augDay.map φ).natTrans.app
                  (op (WithInitial.of m)) t = s := by rfl
              have hwh := types_congr_hom
                (η_whiskerRight_app (augDay.obj A)
                  (augDay.obj (sliceOver X f)) (augDay.obj K)
                  (augDay.map φ)
                  (op (WithInitial.of m)) (op WithInitial.star)) (t, ptK)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
                  (op (WithInitial.of m)) (op WithInitial.star))
                ((augDay.map φ).natTrans.app (op (WithInitial.of m)) t, ptK)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.map φ).natTrans.app (op (WithInitial.of m)) ▷
                    (augDay.obj K).functor.obj (op WithInitial.star))
                      (t, ptK) =
                    ((augDay.map φ).natTrans.app
                      (op (WithInitial.of m)) t, ptK) := rfl
              dsimp only [φ] at hwh ht
              rw [hwh, hext]
              dsimp only [sliceOverTensorMap]
              rw [hdesc, ht]
              change (sliceOver.proj X f).app (op m) s = _
              let e : (augDay.obj (SSet.stdSimplex.obj m)).functor.obj
                  (op (WithInitial.of m)) :=
                SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m))
              have hj := joinInlDayMap_app_of
                (SSet.stdSimplex.obj m) K m e
              have hc := congrArg DayFunctor.Hom.natTrans
                (joinInlDayMap_comp_wholeDayMapOver f m s)
              have hcapp := types_congr_hom
                (NatTrans.congr_app hc (op (WithInitial.of m))) e
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                types_comp_apply] at hcapp
              have hproj : (sliceOver.proj X f).app (op m) s =
                  (wholeDayMapOver f m s).natTrans.app
                    (op (WithInitial.of m))
                    ((DayFunctor.η (augDay.obj (SSet.stdSimplex.obj m))
                      (augDay.obj K)).app
                        (op (WithInitial.of m), op WithInitial.star)
                        (e, ptK)) := by
                rw [← hj]
                rw [hcapp]
                rfl
              rw [hproj]
              have hm := wholeDayMapOver_sliceOver_lift f g m t
              rw [show s = (sliceOver.lift f g).app (op m) t from rfl, hm]
              have hη := types_congr_hom
                (η_whiskerRight_app
                  (augDay.obj (SSet.stdSimplex.obj m))
                  (augDay.obj A) (augDay.obj K)
                  (augDay.map σ) (op (WithInitial.of m))
                  (op WithInitial.star)) (e, ptK)
              simp only [types_comp_apply] at hη
              have hid : (augDay.map σ).natTrans.app
                  (op (WithInitial.of m)) e = t := by
                change σ.app (op m) e = t
                exact SSet.yonedaEquiv_symm_app_id t
              have hext2 :
                  ((augDay.map σ).natTrans.app (op (WithInitial.of m)) ▷
                    (augDay.obj K).functor.obj (op WithInitial.star))
                      (e, ptK) = (t, ptK) := by
                exact Prod.ext hid rfl
              rw [hext2] at hη
              exact congrArg
                (fun w => (((augDayJoinIso A K).inv ≫
                  augDay.map g.1).natTrans.app
                    (op (WithInitial.of m))) w) hη
      | star =>
          obtain ⟨b', rfl⟩ : ∃ b', b = op b' := ⟨b.unop, rfl⟩
          cases b' with
          | of k =>
              apply TypeCat.homEquiv.injective
              funext q
              obtain ⟨t, z⟩ := q
              let ptA : (augDay.obj A).functor.obj
                  (op WithInitial.star) := PUnit.unit
              have ht : t = ptA := by
                change (PUnit.unit : PUnit) = PUnit.unit
                rfl
              subst t
              let φ := sliceOver.lift f g
              let ptS : (augDay.obj (sliceOver X f)).functor.obj
                  (op WithInitial.star) :=
                (augDay.map φ).natTrans.app (op WithInitial.star) ptA
              have hwh := types_congr_hom
                (η_whiskerRight_app (augDay.obj A)
                  (augDay.obj (sliceOver X f)) (augDay.obj K)
                  (augDay.map φ)
                  (op WithInitial.star) (op (WithInitial.of k))) (ptA, z)
              have hdesc := types_congr_hom
                (DayFunctor.η_comp_tensorDesc_app (sliceOverTensorNatTrans f)
                  (op WithInitial.star) (op (WithInitial.of k))) (ptS, z)
              simp only [types_comp_apply] at hwh hdesc
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                TypeCat.homEquiv_apply, comp_apply]
              have hext :
                  ((augDay.map φ).natTrans.app (op WithInitial.star) ▷
                    (augDay.obj K).functor.obj (op (WithInitial.of k)))
                      (ptA, z) = (ptS, z) := rfl
              dsimp only [φ] at hwh
              rw [hwh, hext]
              dsimp only [sliceOverTensorMap]
              rw [hdesc]
              change f.app (op k) z =
                ((augDayJoinIso A K).inv ≫ augDay.map g.1).natTrans.app
                  (op (WithInitial.of k))
                  ((DayFunctor.η (augDay.obj A) (augDay.obj K)).app
                    (op WithInitial.star, op (WithInitial.of k)) (ptA, z))
              have hj := joinInrDayMap_app_of A K k z
              have hc : joinInrDayMap A K ≫
                    ((augDayJoinIso A K).inv ≫ augDay.map g.1) =
                  augDay.map f := by
                rw [← augDay_map_joinInr_comp_augDayJoinIso_hom]
                simp only [Category.assoc, Iso.hom_inv_id_assoc,
                  ← Functor.map_comp, g.2]
              have hcapp := types_congr_hom
                (NatTrans.congr_app (congrArg DayFunctor.Hom.natTrans hc)
                  (op (WithInitial.of k))) z
              simp only [DayFunctor.comp_natTrans, NatTrans.comp_app,
                types_comp_apply] at hcapp
              rw [← hj]
              exact hcapp.symm
          | star =>
              apply TypeCat.homEquiv.injective
              funext q
              change (PUnit.unit : PUnit) = PUnit.unit
              rfl
    exact congrArg dropDay.map hday

/-- The canonical whole-map universal-property packet for over-slices. -/
opaque _root_.SSet.sliceOver.universalProperty (X : SSet.{u})
    {K : SSet.{u}} (f : K ⟶ X) : sliceOver.UniversalProperty X f :=
  { evaluation := sliceOverEvaluation f
    joinInl_evaluation := joinInl_comp_sliceOverEvaluation f
    joinInr_evaluation := joinInr_comp_sliceOverEvaluation f
    evaluation_wholeMap := sliceOverEvaluation_wholeMap f
    homEquiv := fun A => sliceOverHomEquivImpl X f A
    homEquiv_apply := fun _ _ => rfl
    homEquiv_symm_apply := fun _ _ => rfl }

end Join

namespace sliceOver

/-- Evaluation of a general over-slice: a compatible whole join map
`X_{/f} ⋆ K ⟶ X`. -/
noncomputable def evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    sliceOver X f ⋆ K ⟶ X :=
  (universalProperty X f).evaluation

@[reassoc]
lemma joinInl_evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    SSet.joinInl (sliceOver X f) K ≫ evaluation X f = proj X f :=
  (universalProperty X f).joinInl_evaluation

@[reassoc]
lemma joinInr_evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    SSet.joinInr (sliceOver X f) K ≫ evaluation X f = f :=
  (universalProperty X f).joinInr_evaluation

lemma evaluation_wholeMap (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (sliceOver X f).obj (op n)) :
    (SSet.join.map (SSet.yonedaEquiv.symm g)).app K ≫
      evaluation X f = g.1 :=
  (universalProperty X f).evaluation_wholeMap n g

/-- Whole-map universal property of the over-slice. -/
noncomputable def homEquiv (X : SSet.{u}) {K : SSet.{u}}
    (f : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceOver X f) ≃
      { g : A ⋆ K ⟶ X // SSet.joinInr A K ≫ g = f } :=
  (universalProperty X f).homEquiv A

@[simp]
lemma homEquiv_apply (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (A : SSet.{u}) (φ : A ⟶ sliceOver X f) :
    homEquiv X f A φ =
      ⟨(SSet.join.map φ).app K ≫ evaluation X f, by
        rw [← Category.assoc, SSet.joinInr_comp_map, joinInr_evaluation]⟩ :=
  (universalProperty X f).homEquiv_apply A φ

@[simp]
lemma homEquiv_symm_apply (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (A : SSet.{u})
    (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f }) :
    (homEquiv X f A).symm g = lift f g :=
  (universalProperty X f).homEquiv_symm_apply A g

end sliceOver

namespace Join

/-- The canonical whole-map universal-property packet. -/
opaque _root_.SSet.sliceUnder.universalProperty (X : SSet.{u})
    {K : SSet.{u}} (f : K ⟶ X) : sliceUnder.UniversalProperty X f :=
  { evaluation := sliceUnderEvaluation f
    joinInl_evaluation := joinInl_comp_sliceUnderEvaluation f
    joinInr_evaluation := joinInr_comp_sliceUnderEvaluation f
    evaluation_wholeMap := sliceUnderEvaluation_wholeMap f
    homEquiv := fun A => sliceUnderHomEquivImpl X f A
    homEquiv_apply := fun _ _ => rfl
    homEquiv_symm_apply := fun _ _ => rfl }

end Join

namespace sliceUnder

/-- Evaluation of a general under-slice: a compatible whole join map
`K ⋆ X_{f/} ⟶ X`. -/
noncomputable def evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    K ⋆ sliceUnder X f ⟶ X :=
  (universalProperty X f).evaluation

@[reassoc]
lemma joinInl_evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    SSet.joinInl K (sliceUnder X f) ≫ evaluation X f = f :=
  (universalProperty X f).joinInl_evaluation

@[reassoc]
lemma joinInr_evaluation (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) :
    SSet.joinInr K (sliceUnder X f) ≫ evaluation X f = proj X f :=
  (universalProperty X f).joinInr_evaluation

lemma evaluation_wholeMap (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (n : SimplexCategory) (g : (sliceUnder X f).obj (op n)) :
    (SSet.join.obj K).map (SSet.yonedaEquiv.symm g) ≫ evaluation X f = g.1 :=
  (universalProperty X f).evaluation_wholeMap n g

/-- Whole-map universal property of the under-slice. -/
noncomputable def homEquiv (X : SSet.{u}) {K : SSet.{u}}
    (f : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceUnder X f) ≃
      { g : K ⋆ A ⟶ X // SSet.joinInl K A ≫ g = f } :=
  (universalProperty X f).homEquiv A

@[simp]
lemma homEquiv_apply (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (A : SSet.{u}) (φ : A ⟶ sliceUnder X f) :
    homEquiv X f A φ =
      ⟨(SSet.join.obj K).map φ ≫ evaluation X f, by
        rw [← Category.assoc, SSet.joinInl_comp_map, joinInl_evaluation]⟩ :=
  (universalProperty X f).homEquiv_apply A φ

@[simp]
lemma homEquiv_symm_apply (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)
    (A : SSet.{u})
    (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f }) :
    (homEquiv X f A).symm g = lift f g :=
  (universalProperty X f).homEquiv_symm_apply A g

end sliceUnder

/-!
## The structured under-slice adjunction
-/

/-- The structured Hom equivalence for left join division. -/
noncomputable def joinUnderHomEquiv (K A : SSet.{u}) (P : Under K) :
    ((joinUnder K).obj A ⟶ P) ≃
      (A ⟶ (joinLeftDivision K).obj P) where
  toFun q := (sliceUnder.homEquiv P.right P.hom A).symm
    ⟨q.right, q.w⟩
  invFun φ := Under.homMk
    ((sliceUnder.homEquiv P.right P.hom A φ).1)
    ((sliceUnder.homEquiv P.right P.hom A φ).2)
  left_inv q := by
    apply StructuredArrow.hom_ext
    change ((sliceUnder.homEquiv P.right P.hom A)
      ((sliceUnder.homEquiv P.right P.hom A).symm ⟨q.right, q.w⟩)).1 = q.right
    exact congrArg Subtype.val
      ((sliceUnder.homEquiv P.right P.hom A).apply_symm_apply ⟨q.right, q.w⟩)
  right_inv φ :=
    (sliceUnder.homEquiv P.right P.hom A).symm_apply_apply φ


@[simp]
lemma joinUnderHomEquiv_apply (K A : SSet.{u}) (P : Under K)
    (q : (joinUnder K).obj A ⟶ P) :
    joinUnderHomEquiv K A P q =
      (sliceUnder.homEquiv P.right P.hom A).symm ⟨q.right, q.w⟩ :=
  rfl

@[simp]
lemma joinUnderHomEquiv_symm_right (K A : SSet.{u}) (P : Under K)
    (φ : A ⟶ sliceUnder P.right P.hom) :
    ((joinUnderHomEquiv K A P).symm φ).right =
      (sliceUnder.homEquiv P.right P.hom A φ).1 :=
  rfl

lemma joinUnderHomEquiv_naturality_left_symm
    (K : SSet.{u}) {A' A : SSet.{u}} {P : Under K}
    (a : A' ⟶ A) (g : A ⟶ sliceUnder P.right P.hom) :
    (joinUnderHomEquiv K A' P).symm (a ≫ g) =
      (joinUnder K).map a ≫ (joinUnderHomEquiv K A P).symm g := by
  apply StructuredArrow.hom_ext
  change ((sliceUnder.homEquiv P.right P.hom A') (a ≫ g)).1 =
    (join.obj K).map a ≫ ((sliceUnder.homEquiv P.right P.hom A) g).1
  rw [sliceUnder.homEquiv_apply, sliceUnder.homEquiv_apply]
  simp only [Functor.map_comp, Category.assoc]

lemma joinUnderHomEquiv_naturality_right
    (K : SSet.{u}) {A : SSet.{u}} {P Q : Under K}
    (f : (joinUnder K).obj A ⟶ P) (q : P ⟶ Q) :
    joinUnderHomEquiv K A Q (f ≫ q) =
      joinUnderHomEquiv K A P f ≫ (joinLeftDivision K).map q := by
  rw [joinUnderHomEquiv_apply, joinUnderHomEquiv_apply,
    sliceUnder.homEquiv_symm_apply, sliceUnder.homEquiv_symm_apply]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- Left join by `K` is left adjoint to the general under-slice functor. -/
noncomputable def joinUnderAdjunction (K : SSet.{u}) :
    joinUnder K ⊣ joinLeftDivision K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := joinUnderHomEquiv K
      homEquiv_naturality_left_symm := joinUnderHomEquiv_naturality_left_symm K
      homEquiv_naturality_right := joinUnderHomEquiv_naturality_right K }


/-!
## The structured over-slice adjunction
-/

/-- The structured Hom equivalence for right join division. -/
noncomputable def joinOverHomEquiv (K A : SSet.{u}) (P : Under K) :
    ((joinOver K).obj A ⟶ P) ≃
      (A ⟶ (joinRightDivision K).obj P) where
  toFun q := (sliceOver.homEquiv P.right P.hom A).symm
    ⟨q.right, q.w⟩
  invFun φ := Under.homMk
    ((sliceOver.homEquiv P.right P.hom A φ).1)
    ((sliceOver.homEquiv P.right P.hom A φ).2)
  left_inv q := by
    apply StructuredArrow.hom_ext
    change ((sliceOver.homEquiv P.right P.hom A)
      ((sliceOver.homEquiv P.right P.hom A).symm ⟨q.right, q.w⟩)).1 = q.right
    exact congrArg Subtype.val
      ((sliceOver.homEquiv P.right P.hom A).apply_symm_apply ⟨q.right, q.w⟩)
  right_inv φ :=
    (sliceOver.homEquiv P.right P.hom A).symm_apply_apply φ

@[simp, nolint simpNF]
lemma joinOverHomEquiv_apply (K A : SSet.{u}) (P : Under K)
    (q : (joinOver K).obj A ⟶ P) :
    joinOverHomEquiv K A P q =
      (sliceOver.homEquiv P.right P.hom A).symm ⟨q.right, q.w⟩ :=
  rfl

@[simp, nolint simpNF]
lemma joinOverHomEquiv_symm_right (K A : SSet.{u}) (P : Under K)
    (φ : A ⟶ sliceOver P.right P.hom) :
    ((joinOverHomEquiv K A P).symm φ).right =
      (sliceOver.homEquiv P.right P.hom A φ).1 :=
  rfl

lemma joinOverHomEquiv_naturality_left_symm
    (K : SSet.{u}) {A' A : SSet.{u}} {P : Under K}
    (a : A' ⟶ A) (g : A ⟶ sliceOver P.right P.hom) :
    (joinOverHomEquiv K A' P).symm (a ≫ g) =
      (joinOver K).map a ≫ (joinOverHomEquiv K A P).symm g := by
  apply StructuredArrow.hom_ext
  change ((sliceOver.homEquiv P.right P.hom A') (a ≫ g)).1 =
    (SSet.join.map a).app K ≫
      ((sliceOver.homEquiv P.right P.hom A) g).1
  rw [sliceOver.homEquiv_apply, sliceOver.homEquiv_apply]
  simp only [SSet.join.map_comp, NatTrans.comp_app, Category.assoc]

lemma joinOverHomEquiv_naturality_right
    (K : SSet.{u}) {A : SSet.{u}} {P Q : Under K}
    (f : (joinOver K).obj A ⟶ P) (q : P ⟶ Q) :
    joinOverHomEquiv K A Q (f ≫ q) =
      joinOverHomEquiv K A P f ≫ (joinRightDivision K).map q := by
  rw [joinOverHomEquiv_apply, joinOverHomEquiv_apply,
    sliceOver.homEquiv_symm_apply, sliceOver.homEquiv_symm_apply]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- Right join by `K` is left adjoint to the general over-slice functor. -/
noncomputable def joinOverAdjunction (K : SSet.{u}) :
    joinOver K ⊣ joinRightDivision K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := joinOverHomEquiv K
      homEquiv_naturality_left_symm := joinOverHomEquiv_naturality_left_symm K
      homEquiv_naturality_right := joinOverHomEquiv_naturality_right K }



/-!
## Initial-diagram slice equivalences
-/

namespace sliceUnder

/-- The unit whole map classifying the initial-diagram slice inverse. -/
def initialWholeMap (X : SSet.{u}) :
    { g : (⊥_ SSet.{u}) ⋆ X ⟶ X //
      SSet.joinInl (⊥_ SSet.{u}) X ≫ g = initial.to X } :=
  ⟨(SSet.botJoinIso X).hom, initialIsInitial.hom_ext _ _⟩

/-- The inverse of the projection from the initial-diagram slice. -/
noncomputable def initialInv (X : SSet.{u}) :
    X ⟶ SSet.sliceUnder X (initial.to X) :=
  (homEquiv X (initial.to X) X).symm (initialWholeMap X)

/-- The initial-diagram slice inverse followed by projection is the identity. -/
lemma initialInv_comp_proj (X : SSet.{u}) :
    initialInv X ≫ proj X (initial.to X) = 𝟙 X := by
  let S := SSet.sliceUnder X (initial.to X)
  have heval : evaluation X (initial.to X) =
      (SSet.botJoinIso S).hom ≫ proj X (initial.to X) := by
    apply (cancel_epi (SSet.botJoinIso S).inv).mp
    rw [← SSet.joinInr_bot, joinInr_evaluation]
    simp
  have hwhole :
      (SSet.join.obj (⊥_ SSet.{u})).map (initialInv X) ≫
          evaluation X (initial.to X) = (SSet.botJoinIso X).hom := by
    have h := congrArg Subtype.val
      ((homEquiv X (initial.to X) X).apply_symm_apply (initialWholeMap X))
    simpa only [homEquiv_apply, initialInv, initialWholeMap] using h
  apply (cancel_epi (SSet.botJoinIso X).hom).mp
  rw [← Category.assoc, ← SSet.botJoinIso_naturality, Category.assoc,
    ← heval, hwhole, Category.comp_id]

/-- Projection followed by the initial-diagram slice inverse is the identity. -/
lemma proj_comp_initialInv (X : SSet.{u}) :
    proj X (initial.to X) ≫ initialInv X =
      𝟙 (SSet.sliceUnder X (initial.to X)) := by
  let S := SSet.sliceUnder X (initial.to X)
  have heval : evaluation X (initial.to X) =
      (SSet.botJoinIso S).hom ≫ proj X (initial.to X) := by
    apply (cancel_epi (SSet.botJoinIso S).inv).mp
    rw [← SSet.joinInr_bot, joinInr_evaluation]
    simp
  have hwhole :
      (SSet.join.obj (⊥_ SSet.{u})).map (initialInv X) ≫
          evaluation X (initial.to X) = (SSet.botJoinIso X).hom := by
    have h := congrArg Subtype.val
      ((homEquiv X (initial.to X) X).apply_symm_apply (initialWholeMap X))
    simpa only [homEquiv_apply, initialInv, initialWholeMap] using h
  apply (homEquiv X (initial.to X) S).injective
  apply Subtype.ext
  rw [homEquiv_apply, homEquiv_apply]
  change (SSet.join.obj (⊥_ SSet.{u})).map
      (proj X (initial.to X) ≫ initialInv X) ≫
        evaluation X (initial.to X) =
    (SSet.join.obj (⊥_ SSet.{u})).map (𝟙 S) ≫
      evaluation X (initial.to X)
  rw [Functor.map_comp, Category.assoc, hwhole,
    SSet.botJoinIso_naturality, ← heval]
  simp

/-- The under-slice under the unique map from the initial simplicial set is
canonically isomorphic to its target. -/
noncomputable def initialIso (X : SSet.{u}) :
    SSet.sliceUnder X (initial.to X) ≅ X where
  hom := proj X (initial.to X)
  inv := initialInv X
  hom_inv_id := proj_comp_initialInv X
  inv_hom_id := initialInv_comp_proj X

@[simp]
lemma initialIso_hom (X : SSet.{u}) :
    (initialIso X).hom = proj X (initial.to X) := rfl

/-- Functoriality of the under-slice below the initial diagram. -/
noncomputable def initialMap {X Y : SSet.{u}} (p : X ⟶ Y) :
    SSet.sliceUnder X (initial.to X) ⟶
      SSet.sliceUnder Y (initial.to Y) where
  app n := ↾fun g => ⟨g.1 ≫ p, initialIsInitial.hom_ext _ _⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    exact Category.assoc _ _ _

@[simp]
lemma initialMap_app_val {X Y : SSet.{u}} (p : X ⟶ Y)
    {n : SimplexCategoryᵒᵖ}
    (g : (SSet.sliceUnder X (initial.to X)).obj n) :
    ((initialMap p).app n g).1 = g.1 ≫ p := rfl

@[reassoc]
lemma initialMap_comp_proj {X Y : SSet.{u}} (p : X ⟶ Y) :
    initialMap p ≫ proj Y (initial.to Y) =
      proj X (initial.to X) ≫ p := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, initialMap_app_val]
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

/-- The under-slice construction below the initial diagram. -/
noncomputable def initialFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := SSet.sliceUnder X (initial.to X)
  map p := initialMap p
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp only [initialMap_app_val, Category.comp_id, NatTrans.id_app,
      types_id_apply]
  map_comp p q := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp only [NatTrans.comp_app, types_comp_apply, initialMap_app_val,
      Category.assoc]

/-- The under-slice below the initial diagram is naturally isomorphic to the
identity functor. -/
noncomputable def initialNatIso : initialFunctor.{u} ≅ 𝟭 SSet.{u} where
  hom :=
    { app := fun X => (initialIso X).hom
      naturality := by
        intro X Y p
        change initialMap p ≫ proj Y (initial.to Y) =
          proj X (initial.to X) ≫ p
        exact initialMap_comp_proj p }
  inv :=
    { app := fun X => (initialIso X).inv
      naturality := by
        intro X Y p
        change p ≫ (initialIso Y).inv =
          (initialIso X).inv ≫ initialMap p
        apply (cancel_epi (initialIso X).hom).mp
        change proj X (initial.to X) ≫ p ≫ (initialIso Y).inv =
          proj X (initial.to X) ≫ (initialIso X).inv ≫ initialMap p
        calc
          _ = (proj X (initial.to X) ≫ p) ≫ (initialIso Y).inv :=
            (Category.assoc _ _ _).symm
          _ = (initialMap p ≫ proj Y (initial.to Y)) ≫
              (initialIso Y).inv := by rw [initialMap_comp_proj]
          _ = initialMap p := by
            change initialMap p ≫ proj Y (initial.to Y) ≫ initialInv Y =
              initialMap p
            rw [proj_comp_initialInv, Category.comp_id]
          _ = (proj X (initial.to X) ≫ (initialIso X).inv) ≫
              initialMap p := by
            change initialMap p =
              (proj X (initial.to X) ≫ initialInv X) ≫ initialMap p
            rw [proj_comp_initialInv, Category.id_comp]
          _ = _ := Category.assoc _ _ _ }
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    exact (initialIso X).hom_inv_id
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    exact (initialIso X).inv_hom_id

end sliceUnder

namespace sliceOver

/-- The unit whole map classifying the initial-diagram slice inverse. -/
def initialWholeMap (X : SSet.{u}) :
    { g : X ⋆ (⊥_ SSet.{u}) ⟶ X //
      SSet.joinInr X (⊥_ SSet.{u}) ≫ g = initial.to X } :=
  ⟨(SSet.joinBotIso X).hom, initialIsInitial.hom_ext _ _⟩

/-- The inverse of the projection from the initial-diagram slice. -/
noncomputable def initialInv (X : SSet.{u}) :
    X ⟶ SSet.sliceOver X (initial.to X) :=
  (homEquiv X (initial.to X) X).symm (initialWholeMap X)

/-- The initial-diagram slice inverse followed by projection is the identity. -/
lemma initialInv_comp_proj (X : SSet.{u}) :
    initialInv X ≫ proj X (initial.to X) = 𝟙 X := by
  let S := SSet.sliceOver X (initial.to X)
  have heval : evaluation X (initial.to X) =
      (SSet.joinBotIso S).hom ≫ proj X (initial.to X) := by
    apply (cancel_epi (SSet.joinBotIso S).inv).mp
    rw [← SSet.joinInl_bot, joinInl_evaluation]
    simp
  have hwhole :
      (SSet.join.map (initialInv X)).app (⊥_ SSet.{u}) ≫
          evaluation X (initial.to X) = (SSet.joinBotIso X).hom := by
    have h := congrArg Subtype.val
      ((homEquiv X (initial.to X) X).apply_symm_apply (initialWholeMap X))
    simpa only [homEquiv_apply, initialInv, initialWholeMap] using h
  apply (cancel_epi (SSet.joinBotIso X).hom).mp
  rw [← Category.assoc, ← SSet.joinBotIso_naturality, Category.assoc,
    ← heval, hwhole, Category.comp_id]

/-- Projection followed by the initial-diagram slice inverse is the identity. -/
lemma proj_comp_initialInv (X : SSet.{u}) :
    proj X (initial.to X) ≫ initialInv X =
      𝟙 (SSet.sliceOver X (initial.to X)) := by
  let S := SSet.sliceOver X (initial.to X)
  have heval : evaluation X (initial.to X) =
      (SSet.joinBotIso S).hom ≫ proj X (initial.to X) := by
    apply (cancel_epi (SSet.joinBotIso S).inv).mp
    rw [← SSet.joinInl_bot, joinInl_evaluation]
    simp
  have hwhole :
      (SSet.join.map (initialInv X)).app (⊥_ SSet.{u}) ≫
          evaluation X (initial.to X) = (SSet.joinBotIso X).hom := by
    have h := congrArg Subtype.val
      ((homEquiv X (initial.to X) X).apply_symm_apply (initialWholeMap X))
    simpa only [homEquiv_apply, initialInv, initialWholeMap] using h
  apply (homEquiv X (initial.to X) S).injective
  apply Subtype.ext
  rw [homEquiv_apply, homEquiv_apply]
  change (SSet.join.map (proj X (initial.to X) ≫ initialInv X)).app
      (⊥_ SSet.{u}) ≫ evaluation X (initial.to X) =
    (SSet.join.map (𝟙 S)).app (⊥_ SSet.{u}) ≫
      evaluation X (initial.to X)
  rw [SSet.join.map_comp, NatTrans.comp_app, Category.assoc, hwhole,
    SSet.joinBotIso_naturality, ← heval]
  simp

/-- The over-slice over the unique map from the initial simplicial set is
canonically isomorphic to its target. -/
noncomputable def initialIso (X : SSet.{u}) :
    SSet.sliceOver X (initial.to X) ≅ X where
  hom := proj X (initial.to X)
  inv := initialInv X
  hom_inv_id := proj_comp_initialInv X
  inv_hom_id := initialInv_comp_proj X

@[simp]
lemma initialIso_hom (X : SSet.{u}) :
    (initialIso X).hom = proj X (initial.to X) := rfl

/-- Functoriality of the over-slice above the initial diagram. -/
noncomputable def initialMap {X Y : SSet.{u}} (p : X ⟶ Y) :
    SSet.sliceOver X (initial.to X) ⟶
      SSet.sliceOver Y (initial.to Y) where
  app n := ↾fun g => ⟨g.1 ≫ p, initialIsInitial.hom_ext _ _⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    exact Category.assoc _ _ _

@[simp]
lemma initialMap_app_val {X Y : SSet.{u}} (p : X ⟶ Y)
    {n : SimplexCategoryᵒᵖ}
    (g : (SSet.sliceOver X (initial.to X)).obj n) :
    ((initialMap p).app n g).1 = g.1 ≫ p := rfl

@[reassoc]
lemma initialMap_comp_proj {X Y : SSet.{u}} (p : X ⟶ Y) :
    initialMap p ≫ proj Y (initial.to Y) =
      proj X (initial.to X) ≫ p := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, initialMap_app_val]
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

/-- The over-slice construction above the initial diagram. -/
noncomputable def initialFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := SSet.sliceOver X (initial.to X)
  map p := initialMap p
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp only [initialMap_app_val, Category.comp_id, NatTrans.id_app,
      types_id_apply]
  map_comp p q := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp only [NatTrans.comp_app, types_comp_apply, initialMap_app_val,
      Category.assoc]

/-- The over-slice above the initial diagram is naturally isomorphic to the
identity functor. -/
noncomputable def initialNatIso : initialFunctor.{u} ≅ 𝟭 SSet.{u} where
  hom :=
    { app := fun X => (initialIso X).hom
      naturality := by
        intro X Y p
        change initialMap p ≫ proj Y (initial.to Y) =
          proj X (initial.to X) ≫ p
        exact initialMap_comp_proj p }
  inv :=
    { app := fun X => (initialIso X).inv
      naturality := by
        intro X Y p
        change p ≫ (initialIso Y).inv =
          (initialIso X).inv ≫ initialMap p
        apply (cancel_epi (initialIso X).hom).mp
        change proj X (initial.to X) ≫ p ≫ (initialIso Y).inv =
          proj X (initial.to X) ≫ (initialIso X).inv ≫ initialMap p
        calc
          _ = (proj X (initial.to X) ≫ p) ≫ (initialIso Y).inv :=
            (Category.assoc _ _ _).symm
          _ = (initialMap p ≫ proj Y (initial.to Y)) ≫
              (initialIso Y).inv := by rw [initialMap_comp_proj]
          _ = initialMap p := by
            change initialMap p ≫ proj Y (initial.to Y) ≫ initialInv Y =
              initialMap p
            rw [proj_comp_initialInv, Category.comp_id]
          _ = (proj X (initial.to X) ≫ (initialIso X).inv) ≫
              initialMap p := by
            change initialMap p =
              (proj X (initial.to X) ≫ initialInv X) ≫ initialMap p
            rw [proj_comp_initialInv, Category.id_comp]
          _ = _ := Category.assoc _ _ _ }
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    exact (initialIso X).hom_inv_id
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    exact (initialIso X).inv_hom_id

end sliceOver

end SSet
