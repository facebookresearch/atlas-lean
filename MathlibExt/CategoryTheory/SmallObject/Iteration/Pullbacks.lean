/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Preserves.Colimits
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u uC vC uS vS uJ
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallObject.SuccStruct

/-- Proof support only: the applications derive these colimit instances from Type exactness.
The argument concerns C-colimits, not preservation by a limit stage or an output certificate. -/
private theorem iterationFunctor_obj_preservesPullbacks_core
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : C ⥤ C} (ε : 𝟭 C ⟶ G) [PreservesLimitsOfShape WalkingCospan G]
    (hcomm : ∀ (K : Type uJ) [SmallCategory K] [Small.{u} K] [IsFiltered K]
      [HasColimitsOfShape K C],
      PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C)) (j : J) :
    PreservesLimitsOfShape WalkingCospan (((ofNatTrans ε).iterationFunctor J).obj j) := by
  let Φ : SuccStruct (C ⥤ C) := ofNatTrans ε
  let M : J ⥤ C ⥤ C := Φ.iterationFunctor J
  change PreservesLimitsOfShape WalkingCospan (M.obj j)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      have hjbot : j = ⊥ := isMin_iff_eq_bot.mp hj
      subst j
      let _ : PreservesLimitsOfShape WalkingCospan Φ.X₀ := by
        change PreservesLimitsOfShape WalkingCospan (𝟭 C)
        infer_instance
      exact preservesLimitsOfShape_of_natIso (Φ.iterationFunctorObjBotIso J).symm
  | succ j hj ih =>
      let _ : PreservesLimitsOfShape WalkingCospan (M.obj j) := ih
      let _ : PreservesLimitsOfShape WalkingCospan (Φ.succ (M.obj j)) := by
        change PreservesLimitsOfShape WalkingCospan (M.obj j ⋙ G)
        infer_instance
      exact preservesLimitsOfShape_of_natIso
        (Φ.iterationFunctorObjSuccIso j hj).symm
  | isSuccLimit j hj ih =>
      let H : Set.Iio j ⥤ C ⥤ C :=
        (Set.principalSegIio j).monotone.functor ⋙ M
      let c : Cocone H := (Set.principalSegIio j).cocone M
      let _ : HasColimitsOfShape (Set.Iio j) C :=
        hasColimitsOfShape_of_isSuccLimit C j hj
      let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
      let _ : IsFiltered (Set.Iio j) := inferInstance
      let _ : Small.{u} (Set.Iio j) := inferInstance
      let _ : PreservesLimitsOfShape WalkingCospan
          (colim : (Set.Iio j ⥤ C) ⥤ C) := hcomm (Set.Iio j)
      let _ : ∀ k : Set.Iio j, PreservesLimitsOfShape WalkingCospan (H.obj k) :=
        fun k => by
          change PreservesLimitsOfShape WalkingCospan (M.obj k.1)
          exact ih k.1 k.2
      exact Functor.preservesLimitsOfShape_of_isColimit (L := WalkingCospan) H c
        (M.isColimitOfIsWellOrderContinuous j hj)

private theorem iteration_preservesPullbacks_core
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : C ⥤ C} (ε : 𝟭 C ⟶ G) [PreservesLimitsOfShape WalkingCospan G]
    (hcomm : ∀ (K : Type uJ) [SmallCategory K] [Small.{u} K] [IsFiltered K]
      [HasColimitsOfShape K C],
      PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C)) :
    PreservesLimitsOfShape WalkingCospan ((ofNatTrans ε).iteration J) := by
  let Φ : SuccStruct (C ⥤ C) := ofNatTrans ε
  let M : J ⥤ C ⥤ C := Φ.iterationFunctor J
  let _ : IsFiltered J := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (colim : (J ⥤ C) ⥤ C) := hcomm J
  let _ : ∀ j : J, PreservesLimitsOfShape WalkingCospan (M.obj j) :=
    fun j => iterationFunctor_obj_preservesPullbacks_core ε hcomm j
  exact Functor.preservesLimitsOfShape_of_isColimit (L := WalkingCospan) M
    (Φ.iterationCocone J) (Φ.isColimitIterationCocone J)

/-- The SAME original pointed iteration in a presheaf-equivalent carrier preserves pullbacks. -/
theorem iteration_preservesPullbacks_of_presheaf_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : C ⥤ C} (ε : 𝟭 C ⟶ G) [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingCospan ((ofNatTrans ε).iteration J) := by
  apply iteration_preservesPullbacks_core ε
  intro K _ _ _ _
  exact filtered_colim_preservesPullbacks_of_presheaf_equivalence F

/-- BOTH original Arrow projections derive exactness for the actual Arrow iteration. -/
theorem arrow_iteration_preservesPullbacks_of_presheaf_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : Arrow C ⥤ Arrow C} (ε : 𝟭 (Arrow C) ⟶ G)
    [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingCospan ((ofNatTrans ε).iteration J) := by
  let _ : HasLimitsOfShape WalkingCospan C :=
    Adjunction.hasLimitsOfShape_of_equivalence F
  let _ : HasIterationOfShape J (Arrow C) := inferInstance
  apply iteration_preservesPullbacks_core ε
  intro K _ _ _ _
  let _ : HasColimitsOfShape K C :=
    Adjunction.hasColimitsOfShape_of_equivalence F
  let _ : PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C) :=
    filtered_colim_preservesPullbacks_of_presheaf_equivalence F
  exact arrow_colim_preservesPullbacks

/-- Every SAME original Arrow stage preserves pullbacks, including genuine strict limits. -/
theorem arrow_iterationFunctor_obj_preservesPullbacks_of_presheaf_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : Arrow C ⥤ Arrow C} (ε : 𝟭 (Arrow C) ⟶ G)
    [PreservesLimitsOfShape WalkingCospan G] (j : J) :
    PreservesLimitsOfShape WalkingCospan (((ofNatTrans ε).iterationFunctor J).obj j) := by
  let _ : HasLimitsOfShape WalkingCospan C :=
    Adjunction.hasLimitsOfShape_of_equivalence F
  let _ : HasIterationOfShape J (Arrow C) := inferInstance
  apply iterationFunctor_obj_preservesPullbacks_core ε _ j
  intro K _ _ _ _
  let _ : HasColimitsOfShape K C :=
    Adjunction.hasColimitsOfShape_of_equivalence F
  let _ : PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C) :=
    filtered_colim_preservesPullbacks_of_presheaf_equivalence F
  exact arrow_colim_preservesPullbacks

/-- Monomorphisms follow from the actual original pullback-preservation result. -/
theorem arrow_iteration_preservesMonomorphisms_of_presheaf_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : Arrow C ⥤ Arrow C} (ε : 𝟭 (Arrow C) ⟶ G)
    [PreservesLimitsOfShape WalkingCospan G] :
    ((ofNatTrans ε).iteration J).PreservesMonomorphisms := by
  let _ : PreservesLimitsOfShape WalkingCospan ((ofNatTrans ε).iteration J) :=
    arrow_iteration_preservesPullbacks_of_presheaf_equivalence F ε
  infer_instance


end CategoryTheory.SmallObject.SuccStruct
