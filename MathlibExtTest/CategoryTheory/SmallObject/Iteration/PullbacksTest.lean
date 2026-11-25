/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.Iteration.Pullbacks

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u uC vC uS vS uJ
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject
namespace OrdinaryPointedIterationPullbacksTest

section Preservation
variable {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : C ⥤ C} (ε : 𝟭 C ⟶ G) [PreservesLimitsOfShape WalkingCospan G]

include F

/-- The SAME native final cocone and the original supplied pullback cone remain actual data. -/
example (A : WalkingCospan ⥤ C) (c : Cone A) (hc : IsLimit c) :
    let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
    let final := Φ.iterationCocone J
    (IsColimit final) × (IsLimit (final.pt.mapCone c)) := by
  let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
  let _ : PreservesLimitsOfShape WalkingCospan (Φ.iteration J) :=
    SuccStruct.iteration_preservesPullbacks_of_presheaf_equivalence F ε
  exact ⟨Φ.isColimitIterationCocone J, isLimitOfPreserves (Φ.iteration J) hc⟩

end Preservation

section OriginalGeometry
variable {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J C]
    {G : C ⥤ C} (ε : 𝟭 C ⟶ G)

/-- Zero and only the genuine nonmaximum successors use the prescribed native isomorphisms. -/
example :
    let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
    ((Φ.iterationFunctor J).obj ⊥ ≅ 𝟭 C) ×
      (∀ (j : J) (_hj : ¬ IsMax j),
        (Φ.iterationFunctor J).obj (Order.succ j) ≅
          (Φ.iterationFunctor J).obj j ⋙ G) := by
  let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
  exact ⟨Φ.iterationFunctorObjBotIso J,
    fun j _hj => Φ.iterationFunctorObjSuccIso j _hj⟩

/-- A true strict-limit prefix keeps its SAME supplied colimit cocone and actual bottom witness. -/
example (j : J) (hj : Order.IsSuccLimit j) :
    let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
    let stages := Φ.iterationFunctor J
    let prefixCocone := (Set.principalSegIio j).cocone stages
    (IsColimit prefixCocone) × { k : Set.Iio j // k.1 = ⊥ } := by
  let Φ : SuccStruct (C ⥤ C) := SuccStruct.ofNatTrans ε
  let stages := Φ.iterationFunctor J
  exact ⟨stages.isColimitOfIsWellOrderContinuous j hj, ⟨⟨⊥, hj.bot_lt⟩, rfl⟩⟩

end OriginalGeometry

end OrdinaryPointedIterationPullbacksTest

namespace OriginalIterationPullbacksTest

section Preservation
variable {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]

include F

variable {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [Small.{u} J] [HasIterationOfShape J C]
    {G : Arrow C ⥤ Arrow C} (ε : 𝟭 (Arrow C) ⟶ G)
    [PreservesLimitsOfShape WalkingCospan G]

/-- Both original Arrow projections of every prescribed cone are retained. -/
example (A : WalkingCospan ⥤ Arrow C) (c : Cone A) (hc : IsLimit c) :
    IsLimit (((SuccStruct.ofNatTrans ε).iteration J).mapCone c) := by
  let _ : PreservesLimitsOfShape WalkingCospan ((SuccStruct.ofNatTrans ε).iteration J) :=
    SuccStruct.arrow_iteration_preservesPullbacks_of_presheaf_equivalence F ε
  exact isLimitOfPreserves ((SuccStruct.ofNatTrans ε).iteration J) hc

/-- A genuine strict prefix has a real bottom element below j and its SAME supplied cocone. -/
example (j : J) (hj : Order.IsSuccLimit j) :
    let M := (SuccStruct.ofNatTrans ε).iterationFunctor J
    let c := (Set.principalSegIio j).cocone M
    PreservesLimitsOfShape WalkingCospan c.pt := by
  let _ : HasLimitsOfShape WalkingCospan C :=
    Adjunction.hasLimitsOfShape_of_equivalence F
  let _ : HasColimitsOfShape (Set.Iio j) C :=
    hasColimitsOfShape_of_isSuccLimit C j hj
  let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  let _ : Small.{u} (Set.Iio j) := inferInstance
  let _ : IsFiltered (Set.Iio j) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan
      (colim : (Set.Iio j ⥤ C) ⥤ C) :=
    filtered_colim_preservesPullbacks_of_presheaf_equivalence F
  let _ : PreservesLimitsOfShape WalkingCospan
      (colim : (Set.Iio j ⥤ Arrow C) ⥤ Arrow C) := arrow_colim_preservesPullbacks
  let M := (SuccStruct.ofNatTrans ε).iterationFunctor J
  let H := (Set.principalSegIio j).monotone.functor ⋙ M
  let c := (Set.principalSegIio j).cocone M
  let _ : ∀ k : Set.Iio j, PreservesLimitsOfShape WalkingCospan (H.obj k) := fun k =>
    SuccStruct.arrow_iterationFunctor_obj_preservesPullbacks_of_presheaf_equivalence
      F ε k.1
  exact Functor.preservesLimitsOfShape_of_isColimit (L := WalkingCospan) H c
    (M.isColimitOfIsWellOrderContinuous j hj)

/-- The actual final functor preserves an original monic Arrow map and its full square. -/
example {a b : Arrow C} (f : a ⟶ b) [Mono f] :
    let T := (SuccStruct.ofNatTrans ε).iteration J
    Mono (T.map f) ∧
      (T.map f).left ≫ (T.obj b).hom = (T.obj a).hom ≫ (T.map f).right := by
  let T := (SuccStruct.ofNatTrans ε).iteration J
  let _ : T.PreservesMonomorphisms :=
    SuccStruct.arrow_iteration_preservesMonomorphisms_of_presheaf_equivalence F ε
  exact ⟨inferInstance, (T.map f).w⟩

end Preservation

section ProjectionGeometry
variable {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J C]
    {G : Arrow C ⥤ Arrow C} (ε : 𝟭 (Arrow C) ⟶ G)

/-- Both original projections and every original cone leg are the actual mapped data. -/
example (A : WalkingCospan ⥤ Arrow C) (c : Cone A) :
    let T := (SuccStruct.ofNatTrans ε).iteration J
    let mapped := T.mapCone c
    ((Arrow.leftFunc : Arrow C ⥤ C).mapCone mapped).pt = (T.obj c.pt).left ∧
      ((Arrow.rightFunc : Arrow C ⥤ C).mapCone mapped).pt = (T.obj c.pt).right ∧
      ∀ k : WalkingCospan,
        ((Arrow.leftFunc : Arrow C ⥤ C).mapCone mapped).π.app k =
            (T.map (c.π.app k)).left ∧
          ((Arrow.rightFunc : Arrow C ⥤ C).mapCone mapped).π.app k =
            (T.map (c.π.app k)).right := by
  exact ⟨rfl, rfl, fun k => ⟨rfl, rfl⟩⟩

end ProjectionGeometry

end OriginalIterationPullbacksTest
