/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IntervalMaximum
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatRightProper
import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Realization of simplicial path homotopy fibers

This file compares the literal endpoint-pair path homotopy fiber of a
simplicial map with the compact-open homotopy fiber of its realization.
Paths are oriented from `f(x)` at time zero to the selected point at time
one. The comparison is weak under exactly the simplicial fibration premise.
Weak base change retains explicit Kan, properness, factorization, square,
vertex, and weak-map inputs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial
  Topology HomotopicalAlgebra MorphismProperty Opposite
open scoped MonoidalCategory Simplicial SSet.modelCategoryQuillen
  TopCat.modelCategory

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/- The exact PathSpace-characteristics overlay used by reviewed v5 is
replayed locally because the primary cache currently contains the older
PathSpace olean from the independently reviewed core lineage. -/
private theorem constPath_eq_curry_snd (X : SSet.{u}) :
    constPath X = MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) := by
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_constPath, MonoidalClosed.uncurry_curry]

private structure PathSpaceEvaluationHomotopyData (Y : SSet.{u}) where
  homotopy : SSet.Homotopy (eval₀ : pathSpace Y ⟶ Y) eval₁
  h_eq : homotopy.h =
    (β_ (pathSpace Y) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (𝟙 (pathSpace Y))

private noncomputable def pathSpaceEvaluationHomotopyData (Y : SSet.{u}) :
    PathSpaceEvaluationHomotopyData Y where
  homotopy := by
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm SSet.eval₀)
      (SSet.RelativeMorphism.botEquiv.symm SSet.eval₁)
    refine
      { h := (β_ (pathSpace Y) (Δ[1] : SSet.{u})).hom ≫
          MonoidalClosed.uncurry (𝟙 (pathSpace Y))
        h₀ := by
          simpa using
            (comp_eval₀_eq_ι₀_braiding_uncurry
              (𝟙 (pathSpace Y))).symm
        h₁ := by
          simpa using
            (comp_eval₁_eq_ι₁_braiding_uncurry
              (𝟙 (pathSpace Y))).symm
        rel := by
          ext a ⟨⟨x, hx⟩, t⟩
          cases hx }
  h_eq := rfl

private noncomputable def pathSpaceEvaluationHomotopy (Y : SSet.{u}) :
    SSet.Homotopy (eval₀ : pathSpace Y ⟶ Y) eval₁ :=
  (pathSpaceEvaluationHomotopyData Y).homotopy

private theorem pathSpaceEvaluationHomotopy_h (Y : SSet.{u}) :
    (pathSpaceEvaluationHomotopy Y).h =
      (β_ (pathSpace Y) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry (𝟙 (pathSpace Y)) :=
  (pathSpaceEvaluationHomotopyData Y).h_eq

/-- A simplicial path realizes to a compact-open path. -/
noncomputable def pathSpaceRealizationComparison (Y : SSet.{u}) :
    SSet.toTop.obj (pathSpace Y) ⟶
      TopCat.pathObject (SSet.toTop.obj Y) :=
  TopCat.ofHom <| ContinuousMap.curry <|
    (SSet.realizeHomotopyMap
      (pathSpace Y) Y eval₀ eval₁
      (pathSpaceEvaluationHomotopy Y)).hom.comp
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))).inv.hom.comp
            ⟨fun z => (z.2, z.1), by fun_prop⟩)

/-- A realized simplicial path starts at its realized zero endpoint. -/
@[reassoc]
theorem pathSpaceRealizationComparison_evalZero (Y : SSet.{u}) :
    pathSpaceRealizationComparison Y ≫
        TopCat.pathEvalZero (SSet.toTop.obj Y) =
      SSet.toTop.map (eval₀ : pathSpace Y ⟶ Y) := by
  apply TopCat.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_zero
      (pathSpace Y) Y eval₀ eval₁
      (pathSpaceEvaluationHomotopy Y)) x
  change (SSet.realizeHomotopyMap
      (pathSpace Y) Y eval₀ eval₁
      (pathSpaceEvaluationHomotopy Y))
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))).inv (0, x)) = _
  have hpoint :
      (TopCat.prodIsoProd TopCat.I.{u}
        (SSet.toTop.obj (pathSpace Y))).inv (0, x) =
        Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y))) x := by
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · have hL := ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_fst TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))) (0, x)
      have hR := ConcreteCategory.congr_hom
        (Limits.prod.lift_fst (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y)))) x
      exact hL.trans hR.symm
    · have hL := ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_snd TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))) (0, x)
      have hR := ConcreteCategory.congr_hom
        (Limits.prod.lift_snd (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y)))) x
      exact hL.trans hR.symm
  rw [hpoint]
  exact h

/-- A realized simplicial path ends at its realized one endpoint. -/
@[reassoc]
theorem pathSpaceRealizationComparison_evalOne (Y : SSet.{u}) :
    pathSpaceRealizationComparison Y ≫
        TopCat.pathEvalOne (SSet.toTop.obj Y) =
      SSet.toTop.map (eval₁ : pathSpace Y ⟶ Y) := by
  apply TopCat.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_one
      (pathSpace Y) Y eval₀ eval₁
      (pathSpaceEvaluationHomotopy Y)) x
  change (SSet.realizeHomotopyMap
      (pathSpace Y) Y eval₀ eval₁
      (pathSpaceEvaluationHomotopy Y))
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))).inv (1, x)) = _
  have hpoint :
      (TopCat.prodIsoProd TopCat.I.{u}
        (SSet.toTop.obj (pathSpace Y))).inv (1, x) =
        Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y))) x := by
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · have hL := ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_fst TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))) (1, x)
      have hR := ConcreteCategory.congr_hom
        (Limits.prod.lift_fst (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y)))) x
      exact hL.trans hR.symm
    · have hL := ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_snd TopCat.I.{u}
          (SSet.toTop.obj (pathSpace Y))) (1, x)
      have hR := ConcreteCategory.congr_hom
        (Limits.prod.lift_snd (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj (pathSpace Y)))) x
      exact hL.trans hR.symm
  rw [hpoint]
  exact h

private theorem constPath_whisker_evaluation (Y : SSet.{u}) :
    (constPath Y ▷ (Δ[1] : SSet.{u})) ≫
        (pathSpaceEvaluationHomotopy Y).h =
      CartesianMonoidalCategory.fst Y (Δ[1] : SSet.{u}) := by
  rw [pathSpaceEvaluationHomotopy_h,
    BraidedCategory.braiding_naturality_left_assoc]
  rw [MonoidalClosed.uncurry_id_eq_ev, constPath_eq_curry_snd,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_inv_fst (X K : SSet.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫
        SemiCartesianMonoidalCategory.fst X K =
      Limits.prod.fst := by
  rw [← cancel_epi
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K)]
  rw [Iso.hom_inv_id_app_assoc]
  exact (tensorLeftIsoProd_hom_fst X K).symm

private theorem intervalSwap_natural {Z X : TopCat.{u}} (q : Z ⟶ X) :
    Limits.prod.map (𝟙 TopCat.I.{u}) q ≫
        Limits.prod.lift Limits.prod.snd
          (Limits.prod.fst ≫ SSet.stdSimplex.toTopObjIsoI.inv) =
      Limits.prod.lift Limits.prod.snd
          (Limits.prod.fst ≫ SSet.stdSimplex.toTopObjIsoI.inv) ≫
        Limits.prod.map q
          (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) := by
  apply Limits.prod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_hom_natural_left
    {Z X K : SSet.{u}} (q : Z ⟶ X) :
    (q ▷ K) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K =
      (CartesianMonoidalCategory.tensorLeftIsoProd Z).hom.app K ≫
        (Limits.prod.functor.map q).app K := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, tensorLeftIsoProd_hom_fst]
    change _ = _ ≫ (Limits.prod.map q (𝟙 K) ≫ Limits.prod.fst)
    rw [Limits.prod.map_fst]
    rw [← Category.assoc, tensorLeftIsoProd_hom_fst]
    exact CartesianMonoidalCategory.whiskerRight_fst q K
  · rw [Category.assoc, tensorLeftIsoProd_hom_snd]
    change _ = _ ≫ (Limits.prod.map q (𝟙 K) ≫ Limits.prod.snd)
    rw [Limits.prod.map_snd]
    rw [← Category.assoc, tensorLeftIsoProd_hom_snd]
    exact CartesianMonoidalCategory.whiskerRight_snd q K

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_inv_natural_left
    {Z X K : SSet.{u}} (q : Z ⟶ X) :
    (Limits.prod.functor.map q).app K ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K =
      (CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K ≫
        (q ▷ K) := by
  rw [← cancel_mono
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K)]
  calc
    ((Limits.prod.functor.map q).app K ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K =
      (Limits.prod.functor.map q).app K ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K) :=
      Category.assoc _ _ _
    _ = (Limits.prod.functor.map q).app K := by
      rw [Iso.inv_hom_id_app, Category.comp_id]
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd Z).hom.app K ≫
          (Limits.prod.functor.map q).app K) := by
      rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K ≫
        ((q ▷ K) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K) := by
      exact congrArg
        ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K ≫ ·)
        (tensorLeftIsoProd_hom_natural_left q).symm
    _ = ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K ≫
        (q ▷ K)) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app K :=
      (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem toTop_tensorLeftIsoProd_inv_natural_left
    {Z X K : SSet.{u}} (q : Z ⟶ X) :
    SSet.toTop.map ((Limits.prod.functor.map q).app K) ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K) =
      SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K) ≫
        SSet.toTop.map (q ▷ K) := by
  rw [← Functor.map_comp, tensorLeftIsoProd_inv_natural_left,
    Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem toTop_bridge_tensorLeftIsoProd_inv_natural_left
    {Z X K : SSet.{u}} (q : Z ⟶ X)
    (eZ : ((Limits.prod.functor.obj Z).obj K) ≅ (Z ⨯ K))
    (eX : ((Limits.prod.functor.obj X).obj K) ≅ (X ⨯ K))
    (hBridge : Limits.prod.map q (𝟙 K) ≫ eX.inv =
      eZ.inv ≫ (Limits.prod.functor.map q).app K) :
    SSet.toTop.map (Limits.prod.map q (𝟙 K)) ≫
        SSet.toTop.map eX.inv ≫
          SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K) =
      SSet.toTop.map eZ.inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K) ≫
            SSet.toTop.map (q ▷ K) := by
  rw [← Functor.map_comp_assoc, hBridge, Functor.map_comp_assoc]
  rw [toTop_tensorLeftIsoProd_inv_natural_left]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem toTop_reflBridge_tensorLeftIsoProd_inv_natural_left
    {Z X K : SSet.{u}} (q : Z ⟶ X) :
    SSet.toTop.map (Limits.prod.map q (𝟙 K)) ≫
        SSet.toTop.map (Iso.refl (X ⨯ K)).inv ≫
          SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K) =
      SSet.toTop.map (Iso.refl (Z ⨯ K)).inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K) ≫
            SSet.toTop.map (q ▷ K) := by
  let eZ : ((Limits.prod.functor.obj Z).obj K) ≅ (Z ⨯ K) := Iso.refl _
  let eX : ((Limits.prod.functor.obj X).obj K) ≅ (X ⨯ K) := Iso.refl _
  change SSet.toTop.map (Limits.prod.map q (𝟙 K)) ≫
      SSet.toTop.map eX.inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K) =
    SSet.toTop.map eZ.inv ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app K) ≫
          SSet.toTop.map (q ▷ K)
  exact toTop_bridge_tensorLeftIsoProd_inv_natural_left q eZ eX rfl

@[reassoc]
private theorem prodComparison_inv_natural_id
    {Z X : SSet.{u}} (q : Z ⟶ X)
    (hZ : IsIso (Limits.prodComparison SSet.toTop
      Z (Δ[1] : SSet.{u})))
    (hX : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u}))) :
    Limits.prod.map (SSet.toTop.map q)
        (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) ≫
        CategoryTheory.inv (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) =
      CategoryTheory.inv (Limits.prodComparison SSet.toTop
          Z (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map (Limits.prod.map q (𝟙 (Δ[1] : SSet.{u}))) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
    Z (Δ[1] : SSet.{u})) := hZ
  let _ : IsIso (Limits.prodComparison SSet.toTop
    X (Δ[1] : SSet.{u})) := hX
  calc
    _ = Limits.prod.map (SSet.toTop.map q)
          (SSet.toTop.map (𝟙 (Δ[1] : SSet.{u}))) ≫
          CategoryTheory.inv (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) := by
      exact congrArg
        (fun r => Limits.prod.map (SSet.toTop.map q) r ≫
          CategoryTheory.inv (Limits.prodComparison SSet.toTop
            X (Δ[1] : SSet.{u})))
        (SSet.toTop.map_id (Δ[1] : SSet.{u})).symm
    _ = _ := (Limits.prodComparison_inv_natural (F := SSet.toTop)
      q (𝟙 (Δ[1] : SSet.{u}))).symm

private def homotopyPrecomp {Z X Y : SSet.{u}} {f g : X ⟶ Y}
    (q : Z ⟶ X) (H : SSet.Homotopy f g) :
    SSet.Homotopy (q ≫ f) (q ≫ g) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (q ≫ f))
    (SSet.RelativeMorphism.botEquiv.symm (q ≫ g))
  refine
    { h := (q ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := ?_
      h₁ := ?_
      rel := by
        ext a ⟨⟨x, hx⟩, t⟩
        cases hx }
  · change SSet.ι₀ ≫ ((q ▷ (Δ[1] : SSet.{u})) ≫ H.h) = q ≫ f
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
  · change SSet.ι₁ ≫ ((q ▷ (Δ[1] : SSet.{u})) ≫ H.h) = q ≫ g
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]

set_option backward.isDefEq.respectTransparency false in
private theorem realizeHomotopyMap_precomp
    {Z X Y : SSet.{u}} {f g : X ⟶ Y}
    (q : Z ⟶ X) (H : SSet.Homotopy f g) :
    Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map q) ≫
        SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap Z Y (q ≫ f) (q ≫ g)
        (homotopyPrecomp q H) := by
  have hFiniteZ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) Z) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  have hZ : IsIso (Limits.prodComparison SSet.toTop
      Z (Δ[1] : SSet.{u})) :=
    @SSet.isIso_prodComparison_swap _ _ hFiniteZ
  have hFiniteX : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  have hX : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u})) :=
    @SSet.isIso_prodComparison_swap _ _ hFiniteX
  simp only [SSet.realizeHomotopyMap, Limits.prod.braiding_hom,
    asIso_inv, curriedTensor_obj_obj, Limits.prod.lift_map_assoc,
    Category.comp_id, homotopyPrecomp, id_eq, Functor.map_comp]
  rw [← Category.assoc, intervalSwap_natural, Category.assoc]
  rw [prodComparison_inv_natural_id_assoc q hZ hX]
  rw [toTop_reflBridge_tensorLeftIsoProd_inv_natural_left_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem realizeHomotopyMap_eq_snd_of_h (Y : SSet.{u})
    {f g : Y ⟶ Y} (H : SSet.Homotopy f g)
    (hH : H.h = CartesianMonoidalCategory.fst Y (Δ[1] : SSet.{u})) :
    SSet.realizeHomotopyMap Y Y f g H = Limits.prod.snd := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) Y) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      Y (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  simp only [SSet.realizeHomotopyMap, hH, asIso_inv,
    curriedTensor_obj_obj, Iso.refl_inv]
  rw [SSet.toTop.map_id, Category.id_comp]
  rw [← Functor.map_comp, tensorLeftIsoProd_inv_fst]
  rw [← Limits.prodComparison_fst]
  simp only [IsIso.inv_hom_id_assoc, Limits.prod.map_fst,
    Category.comp_id, Limits.prod.braiding_hom]
  rw [Limits.prod.lift_fst]

/-- Realization sends a simplicial constant path to the corresponding
compact-open constant path. -/
@[reassoc]
theorem constPath_pathSpaceRealizationComparison (Y : SSet.{u}) :
    SSet.toTop.map (SSet.constPath Y) ≫
        pathSpaceRealizationComparison Y =
      TopCat.pathConstant (SSet.toTop.obj Y) := by
  apply TopCat.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change (SSet.realizeHomotopyMap
      (SSet.pathSpace Y) Y SSet.eval₀ SSet.eval₁
      (SSet.pathSpaceEvaluationHomotopy Y))
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (SSet.pathSpace Y))).inv
            (t, SSet.toTop.map (SSet.constPath Y) x)) = x
  let HC := homotopyPrecomp (SSet.constPath Y)
    (SSet.pathSpaceEvaluationHomotopy Y)
  have hHC : HC.h =
      CartesianMonoidalCategory.fst Y (Δ[1] : SSet.{u}) := by
    change (SSet.constPath Y ▷ (Δ[1] : SSet.{u})) ≫
      (SSet.pathSpaceEvaluationHomotopy Y).h = _
    exact constPath_whisker_evaluation Y
  have hPre := realizeHomotopyMap_precomp
    (SSet.constPath Y) (SSet.pathSpaceEvaluationHomotopy Y)
  have hSnd := realizeHomotopyMap_eq_snd_of_h Y HC hHC
  let z := (TopCat.prodIsoProd TopCat.I.{u}
    (SSet.toTop.obj Y)).inv (t, x)
  have hPrePoint := ConcreteCategory.congr_hom hPre z
  have hMapPoint := TopCat.prodMap_prodIso_inv_apply
    (SSet.toTop.map (SSet.constPath Y)) t x
  have hSndPoint := ConcreteCategory.congr_hom hSnd z
  have hz := ConcreteCategory.congr_hom
    (TopCat.prodIsoProd_inv_snd TopCat.I.{u} (SSet.toTop.obj Y)) (t, x)
  calc
    _ = SSet.realizeHomotopyMap Y Y
          (SSet.constPath Y ≫ SSet.eval₀)
          (SSet.constPath Y ≫ SSet.eval₁) HC z := by
      rw [← hMapPoint]
      exact hPrePoint
    _ = (Limits.prod.snd : TopCat.I.{u} ⨯ SSet.toTop.obj Y ⟶
          SSet.toTop.obj Y) z := hSndPoint
    _ = x := hz

private noncomputable abbrev pathEndpointPair (Y : SSet.{u}) :
    SSet.pathSpace Y ⟶ Y ⨯ Y :=
  SSet.evalPair (X := Y) ≫
    (CartesianMonoidalCategory.tensorLeftIsoProd Y).hom.app Y

@[reassoc (attr := simp), nolint simpNF]
private theorem pathEndpointPair_fst (Y : SSet.{u}) :
    pathEndpointPair Y ≫ Limits.prod.fst = SSet.eval₀ := by
  calc
    _ = SSet.evalPair ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd Y).hom.app Y ≫
          Limits.prod.fst) := Category.assoc _ _ _
    _ = SSet.evalPair ≫ SemiCartesianMonoidalCategory.fst Y Y :=
      congrArg (SSet.evalPair ≫ ·) (tensorLeftIsoProd_hom_fst Y Y)
    _ = _ := SSet.evalPair_fst

@[reassoc (attr := simp), nolint simpNF]
private theorem pathEndpointPair_snd (Y : SSet.{u}) :
    pathEndpointPair Y ≫ Limits.prod.snd = SSet.eval₁ := by
  calc
    _ = SSet.evalPair ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd Y).hom.app Y ≫
          Limits.prod.snd) := Category.assoc _ _ _
    _ = SSet.evalPair ≫ SemiCartesianMonoidalCategory.snd Y Y :=
      congrArg (SSet.evalPair ≫ ·) (tensorLeftIsoProd_hom_snd Y Y)
    _ = _ := SSet.evalPair_snd

private theorem toTop_map_const
    {A Y : SSet.{u}} (y : Y _⦋0⦌) :
    SSet.toTop.map (SSet.const (X := A) y) =
      TopCat.const (SSet.realizedVertex y) := by
  have hfac : SSet.const (X := A) y =
      SSet.stdSimplex.isTerminalObj₀.from A ≫
        SSet.const (X := (Δ[0] : SSet.{u})) y := by
    simp
  rw [hfac, Functor.map_comp]
  apply TopCat.hom_ext
  ext a
  change SSet.toTop.map
      (SSet.const (X := (Δ[0] : SSet.{u})) y)
      (SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from A) a) =
    SSet.realizedVertex y
  rw [SSet.realizedVertex_eq_const]
  congr 1
  apply (SimplexCategory.toTopHomeo ⦋0⦌).injective
  subsingleton

/-- Canonical comparison from the realization of the simplicial path
homotopy fiber to the compact-open TopCat homotopy fiber. -/
noncomputable def pathHomotopyFiberRealizationComparison
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    SSet.toTop.obj (pathHomotopyFiber f y) ⟶
      TopCat.homotopyFiber
        (SSet.toTop.map f) (SSet.realizedVertex y) :=
  pullback.lift
    (Limits.prod.lift
      (SSet.toTop.map (pathHomotopyFiberToTotal f y))
      (TopCat.isTerminalPUnit.from _))
    (SSet.toTop.map (pathHomotopyFiberPath f y) ≫
      pathSpaceRealizationComparison Y)
    (by
      apply Limits.prod.hom_ext
      · calc
          (Limits.prod.lift
                (SSet.toTop.map (pathHomotopyFiberToTotal f y))
                (TopCat.isTerminalPUnit.from _) ≫
              Limits.prod.map (SSet.toTop.map f)
                (TopCat.const (SSet.realizedVertex y))) ≫
              Limits.prod.fst =
            SSet.toTop.map (pathHomotopyFiberToTotal f y) ≫
              SSet.toTop.map f := by simp
          _ = SSet.toTop.map
              (pathHomotopyFiberToTotal f y ≫ f) :=
            (SSet.toTop.map_comp _ _).symm
          _ = SSet.toTop.map
              (pathHomotopyFiberPath f y ≫ SSet.eval₀) := by
            rw [pathHomotopyFiberPath_evalZero]
          _ = SSet.toTop.map (pathHomotopyFiberPath f y) ≫
              SSet.toTop.map (SSet.eval₀ : SSet.pathSpace Y ⟶ Y) :=
            SSet.toTop.map_comp _ _
          _ = (SSet.toTop.map (pathHomotopyFiberPath f y) ≫
                pathSpaceRealizationComparison Y) ≫
              TopCat.pathEvalZero (SSet.toTop.obj Y) := by
            rw [Category.assoc, pathSpaceRealizationComparison_evalZero]
          _ = ((SSet.toTop.map (pathHomotopyFiberPath f y) ≫
                pathSpaceRealizationComparison Y) ≫
              TopCat.pathEndpoints (SSet.toTop.obj Y)) ≫
                Limits.prod.fst := by
            simp [TopCat.pathEndpoints, Category.assoc]
      · calc
          (Limits.prod.lift
                (SSet.toTop.map (pathHomotopyFiberToTotal f y))
                (TopCat.isTerminalPUnit.from _) ≫
              Limits.prod.map (SSet.toTop.map f)
                (TopCat.const (SSet.realizedVertex y))) ≫
              Limits.prod.snd =
            TopCat.isTerminalPUnit.from _ ≫
              TopCat.const (SSet.realizedVertex y) := by simp
          _ = TopCat.const (SSet.realizedVertex y) := by
            ext z
            rfl
          _ = SSet.toTop.map
              (SSet.const (X := pathHomotopyFiber f y) y) :=
            (toTop_map_const y).symm
          _ = SSet.toTop.map
              (pathHomotopyFiberPath f y ≫ SSet.eval₁) := by
            rw [pathHomotopyFiberPath_evalOne]
          _ = SSet.toTop.map (pathHomotopyFiberPath f y) ≫
              SSet.toTop.map (SSet.eval₁ : SSet.pathSpace Y ⟶ Y) :=
            SSet.toTop.map_comp _ _
          _ = (SSet.toTop.map (pathHomotopyFiberPath f y) ≫
                pathSpaceRealizationComparison Y) ≫
              TopCat.pathEvalOne (SSet.toTop.obj Y) := by
            rw [Category.assoc, pathSpaceRealizationComparison_evalOne]
          _ = ((SSet.toTop.map (pathHomotopyFiberPath f y) ≫
                pathSpaceRealizationComparison Y) ≫
              TopCat.pathEndpoints (SSet.toTop.obj Y)) ≫
                Limits.prod.snd := by
            simp [TopCat.pathEndpoints, Category.assoc])

/-- The realization comparison retains the total-space point. -/
@[reassoc]
theorem pathHomotopyFiberRealizationComparison_toTotal
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map f) (SSet.realizedVertex y) =
      SSet.toTop.map (pathHomotopyFiberToTotal f y) := by
  rw [pathHomotopyFiberRealizationComparison,
    ← Category.assoc, pullback.lift_fst]
  simp

/-- The realization comparison retains the entire realized path. -/
@[reassoc]
theorem pathHomotopyFiberRealizationComparison_path
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberPath
        (SSet.toTop.map f) (SSet.realizedVertex y) =
      SSet.toTop.map (pathHomotopyFiberPath f y) ≫
        pathSpaceRealizationComparison Y := by
  rw [pathHomotopyFiberRealizationComparison, pullback.lift_snd]

/-! ## Ending paths and their contraction -/

private abbrev endingPath (Y : SSet.{u}) (y : Y _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber (eval₁ : pathSpace Y ⟶ Y) y

private abbrev endingPathIncl (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPath Y y ⟶ pathSpace Y :=
  (Subcomplex.fiber (eval₁ : pathSpace Y ⟶ Y) y).ι

private abbrev endingPathEvalZero (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPath Y y ⟶ Y :=
  endingPathIncl Y y ≫ eval₀

private noncomputable def endingPathPoint (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPath Y y _⦋0⦌ :=
  Subcomplex.fiber.basePoint ((constPath Y).app _ y) (by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (eval₁_constPath Y) (op ⦋0⦌)) y)

private noncomputable def endingPathConstant
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ endingPath Y y :=
  SSet.const (endingPathPoint Y y)

private theorem endingPathConstant_incl (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPathConstant Y y ≫ endingPathIncl Y y =
      SSet.const y ≫ constPath Y := by
  dsimp [endingPathConstant, endingPathPoint, endingPath, endingPathIncl]
  rw [const_comp, const_comp]
  rfl

@[reassoc (attr := simp)]
private theorem endingPathConstant_evalZero
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPathConstant Y y ≫ endingPathEvalZero Y y = SSet.const y := by
  rw [endingPathEvalZero, ← Category.assoc, endingPathConstant_incl]
  rw [Category.assoc, eval₀_constPath, Category.comp_id]

private theorem intervalMaxMap_timeZero :
    (Δ[1] : SSet.{u}) ◁
        (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫
      intervalMaxMap =
        (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom :=
  intervalMaxMap_zero_right

private theorem intervalMaxMap_timeOne :
    (Δ[1] : SSet.{u}) ◁
        (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫
      intervalMaxMap =
        SSet.const (stdSimplex.obj₀Equiv.{u}.symm 1) :=
  intervalMaxMap_one_right

private theorem intervalMaxMap_firstOne (Z : SSet.{u}) :
    (SSet.const (X := Z)
        (stdSimplex.obj₀Equiv.{u}.symm 1) ▷
      (Δ[1] : SSet.{u})) ≫ intervalMaxMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm 1) := by
  ext ⟨⟨n⟩⟩ z i
  change ((intervalMaxMap.app (op ⦋n⦌)
      ((SSet.const (X := Z) (stdSimplex.obj₀Equiv.{u}.symm 1)).app (op ⦋n⦌) z.1,
        z.2) : (Δ[1] : SSet.{u}) _⦋n⦌) i).val =
    (((SSet.const (stdSimplex.obj₀Equiv.{u}.symm 1)).app (op ⦋n⦌) z :
      (Δ[1] : SSet.{u}) _⦋n⦌) i).val
  rw [intervalMaxMap_apply]
  change (max (1 : Fin 2) (z.2 i)).val = 1
  exact congrArg Fin.val (max_eq_left (Fin.le_last _))

private theorem eval₁_constPath_eq_pre_constOne (Y : SSet.{u}) :
    (eval₁ : pathSpace Y ⟶ Y) ≫ constPath Y =
      (MonoidalClosed.pre
        (SSet.const (X := (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y := by
  rw [← (pathSpaceEvaluationHomotopy Y).h₁,
    pathSpaceEvaluationHomotopy_h, constPath_eq_curry_snd]
  rw [← MonoidalClosed.curry_natural_left]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  change _ = MonoidalClosed.uncurry
    ((𝟙 (pathSpace Y)) ≫
      (MonoidalClosed.pre
        (SSet.const (X := (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y)
  rw [MonoidalClosed.uncurry_pre_app]
  simp only [MonoidalClosed.uncurry_id_eq_ev]
  ext n z
  rfl

private noncomputable def pathTailContractionCurried (Y : SSet.{u}) :
    pathSpace Y ⟶ (ihom (Δ[1] : SSet.{u})).obj (pathSpace Y) :=
  (MonoidalClosed.pre intervalMaxMap).app Y ≫
    MonoidalClosed.ihomCurry (Δ[1] : SSet.{u}) Δ[1] Y

private noncomputable def pathTailContractionMap (Y : SSet.{u}) :
    pathSpace Y ⊗ Δ[1] ⟶ pathSpace Y :=
  (β_ (pathSpace Y) (Δ[1] : SSet.{u})).hom ≫
    MonoidalClosed.uncurry (pathTailContractionCurried Y)

private theorem pathTailContractionMap_eq (Y : SSet.{u}) :
    pathTailContractionMap Y =
      (β_ (pathSpace Y) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.curry ((α_ (Δ[1] : SSet.{u}) Δ[1]
          (pathSpace Y)).inv ≫
            MonoidalClosed.uncurry
              ((MonoidalClosed.pre intervalMaxMap).app Y)) := by
  dsimp [pathTailContractionMap, pathTailContractionCurried]
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_ihomCurry,
    ← MonoidalClosed.curry_natural_left]
  congr 1

private theorem pathTailContractionMap_timeZero (Y : SSet.{u}) :
    ι₀ ≫ pathTailContractionMap Y = 𝟙 (pathSpace Y) := by
  rw [pathTailContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₀_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    Category.comp_id, ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMaxMap_timeZero]
  apply MonoidalClosed.uncurry_injective
  rfl

private theorem pathTailContractionMap_timeOne (Y : SSet.{u}) :
    ι₁ ≫ pathTailContractionMap Y = eval₁ ≫ constPath Y := by
  rw [pathTailContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₁_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMaxMap_timeOne,
    ← MonoidalClosed.curry_natural_left,
    eval₁_constPath_eq_pre_constOne]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre]
  rfl

private theorem pathTailContractionMap_preOne (Y : SSet.{u}) :
    pathTailContractionMap Y ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y =
      CartesianMonoidalCategory.fst (pathSpace Y) (Δ[1] : SSet.{u}) ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y := by
  rw [pathTailContractionMap_eq, Category.assoc,
    MonoidalClosed.curry_pre_app]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_pre]
  rw [associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMaxMap_firstOne]
  rfl

private theorem endingPathCylinder_evalOne
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    ((endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
        pathTailContractionMap Y) ≫ eval₁ = SSet.const y := by
  let _ : IsSplitMono (constPath Y) :=
    IsSplitMono.mk'
      { retraction := eval₁
        id := eval₁_constPath Y }
  apply (cancel_mono (constPath Y)).mp
  calc
    (((endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
          pathTailContractionMap Y ≫ eval₁) ≫ constPath Y) =
        (endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
          (pathTailContractionMap Y ≫ (eval₁ ≫ constPath Y)) := by
      simp only [Category.assoc]
    _ = (endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
          (pathTailContractionMap Y ≫
            (MonoidalClosed.pre
              (SSet.const (X := (Δ[1] : SSet.{u}))
                (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y) := by
      rw [eval₁_constPath_eq_pre_constOne]
    _ = (endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
          (CartesianMonoidalCategory.fst (pathSpace Y)
            (Δ[1] : SSet.{u}) ≫
            (MonoidalClosed.pre
              (SSet.const (X := (Δ[1] : SSet.{u}))
                (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y) := by
      rw [pathTailContractionMap_preOne]
    _ = CartesianMonoidalCategory.fst (endingPath Y y)
          (Δ[1] : SSet.{u}) ≫ endingPathIncl Y y ≫
            (MonoidalClosed.pre
              (SSet.const (X := (Δ[1] : SSet.{u}))
                (stdSimplex.obj₀Equiv.{u}.symm 1))).app Y := by
      rw [← Category.assoc,
        CartesianMonoidalCategory.whiskerRight_fst, Category.assoc]
    _ = CartesianMonoidalCategory.fst (endingPath Y y)
          (Δ[1] : SSet.{u}) ≫ endingPathIncl Y y ≫
            eval₁ ≫ constPath Y := by
      rw [← eval₁_constPath_eq_pre_constOne]
    _ = SSet.const y ≫ constPath Y := by
      simp

private noncomputable def endingPathContractionMap
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    endingPath Y y ⊗ Δ[1] ⟶ endingPath Y y :=
  Subcomplex.lift
    ((endingPathIncl Y y ▷ (Δ[1] : SSet.{u})) ≫
      pathTailContractionMap Y)
    (by
      rw [Subcomplex.range_le_fiber_iff]
      exact endingPathCylinder_evalOne Y y)

private theorem endingPathContractionMap_timeZero
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    ι₀ ≫ endingPathContractionMap Y y = 𝟙 (endingPath Y y) := by
  apply (cancel_mono (endingPathIncl Y y)).mp
  simp only [endingPathContractionMap, Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₀_comp, Category.assoc,
    pathTailContractionMap_timeZero]
  simp

private theorem endingPathContractionMap_timeOne
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    ι₁ ≫ endingPathContractionMap Y y =
      SSet.stdSimplex.isTerminalObj₀.from (endingPath Y y) ≫
        endingPathConstant Y y := by
  apply (cancel_mono (endingPathIncl Y y)).mp
  simp only [endingPathContractionMap, Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₁_comp, Category.assoc,
    pathTailContractionMap_timeOne, ← Category.assoc,
    Subcomplex.fiber_ι_comp]
  rw [endingPathConstant_incl]
  simp

private noncomputable def endingPathContraction
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    SSet.Homotopy (𝟙 (endingPath Y y))
      (SSet.stdSimplex.isTerminalObj₀.from (endingPath Y y) ≫
        endingPathConstant Y y) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  refine
    { h := endingPathContractionMap Y y
      h₀ := endingPathContractionMap_timeZero Y y
      h₁ := endingPathContractionMap_timeOne Y y
      rel := ?_ }
  ext m ⟨⟨z, hz⟩, t⟩
  cases hz

private theorem realizedPointInclusion_mem
    {P : SSet.{u}}
    (k : (Δ[0] : SSet.{u}) ⟶ P)
    (q : P ⟶ (Δ[0] : SSet.{u}))
    (hkq : k ≫ q = 𝟙 _)
    (H : SSet.Homotopy (𝟙 P) (q ≫ k)) :
    TopCat.weakHomotopyEquivalences (SSet.toTop.map k) := by
  let e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (Δ[0] : SSet.{u})) (SSet.toTop.obj P) :=
    { toFun := (SSet.toTop.map k).hom
      invFun := (SSet.toTop.map q).hom
      left_inv := by
        have hcomp : SSet.toTop.map k ≫ SSet.toTop.map q = 𝟙 _ := by
          calc
            SSet.toTop.map k ≫ SSet.toTop.map q =
                SSet.toTop.map (k ≫ q) :=
              (SSet.toTop.map_comp k q).symm
            _ = SSet.toTop.map (𝟙 _) := by rw [hkq]
            _ = 𝟙 _ := SSet.toTop.map_id _
        rw [show (SSet.toTop.map q).hom.comp (SSet.toTop.map k).hom =
            (SSet.toTop.map k ≫ SSet.toTop.map q).hom by rfl, hcomp]
        exact ⟨ContinuousMap.Homotopy.refl _⟩
      right_inv := by
        have hR := SSet.realizeHomotopy P P (𝟙 P) (q ≫ k) H
        have hR' : ContinuousMap.Homotopy
            ((SSet.toTop.map k).hom.comp (SSet.toTop.map q).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id] using hR.symm
        exact ⟨hR'⟩ }
  exact TopCat.homotopyEquiv_toFun_mem e

private theorem endingPathConstant_mem_weakHomotopyEquivalences
    (Y : SSet.{u}) (y : Y _⦋0⦌) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (endingPathConstant Y y)) := by
  let q : endingPath Y y ⟶ (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.from _
  apply realizedPointInclusion_mem (endingPathConstant Y y) q
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · simpa [q] using endingPathContraction Y y

/-! ## Pullback presentations -/

private noncomputable def pathHomotopyFiberToEndingPath
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiber f y ⟶ endingPath Y y :=
  Subcomplex.lift (pathHomotopyFiberPath f y) (by
    rw [Subcomplex.range_le_fiber_iff]
    exact pathHomotopyFiberPath_evalOne f y)

@[reassoc (attr := simp)]
private theorem pathHomotopyFiberToEndingPath_incl
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiberToEndingPath f y ≫ endingPathIncl Y y =
      pathHomotopyFiberPath f y := by
  rw [pathHomotopyFiberToEndingPath, Subcomplex.lift_ι]

@[reassoc]
private theorem pathHomotopyFiberToEndingPath_evalZero
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiberToEndingPath f y ≫ endingPathEvalZero Y y =
      pathHomotopyFiberToTotal f y ≫ f := by
  simp [endingPathEvalZero, Category.assoc,
    pathHomotopyFiberPath_evalZero]

set_option backward.isDefEq.respectTransparency false in
private theorem pathHomotopyFiber_isPullback_endingPath
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    IsPullback (pathHomotopyFiberToTotal f y)
      (pathHomotopyFiberToEndingPath f y) f (endingPathEvalZero Y y) := by
  have hw := (pathHomotopyFiberToEndingPath_evalZero f y).symm
  have hcompat (s : PullbackCone f (endingPathEvalZero Y y)) :
      Limits.prod.lift s.fst
            (SSet.stdSimplex.isTerminalObj₀.from _) ≫
          Limits.prod.map f
            (SSet.const (X := (Δ[0] : SSet.{u})) y) =
        (s.snd ≫ endingPathIncl Y y) ≫ pathEndpointPair Y := by
    apply Limits.prod.hom_ext
    · calc
        (Limits.prod.lift s.fst
              (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            Limits.prod.map f (SSet.const y)) ≫ Limits.prod.fst =
          s.fst ≫ f := by simp
        _ = s.snd ≫ endingPathEvalZero Y y := s.condition
        _ = ((s.snd ≫ endingPathIncl Y y) ≫
              pathEndpointPair Y) ≫ Limits.prod.fst := by
          dsimp only [endingPathEvalZero]
          calc
            s.snd ≫ endingPathIncl Y y ≫ eval₀ =
                (s.snd ≫ endingPathIncl Y y) ≫
                  (pathEndpointPair Y ≫ Limits.prod.fst) := by
              rw [pathEndpointPair_fst]
              exact (Category.assoc _ _ _).symm
            _ = ((s.snd ≫ endingPathIncl Y y) ≫
                pathEndpointPair Y) ≫ Limits.prod.fst :=
              (Category.assoc _ _ _).symm
    · calc
        (Limits.prod.lift s.fst
              (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            Limits.prod.map f (SSet.const y)) ≫ Limits.prod.snd =
          SSet.const y := by simp
        _ = ((s.snd ≫ endingPathIncl Y y) ≫
              pathEndpointPair Y) ≫ Limits.prod.snd := by
          calc
            SSet.const y =
                (s.snd ≫ endingPathIncl Y y) ≫ eval₁ := by
              rw [Category.assoc, endingPathIncl,
                Subcomplex.fiber_ι_comp]
              simp
            _ = (s.snd ≫ endingPathIncl Y y) ≫
                (pathEndpointPair Y ≫ Limits.prod.snd) := by
              rw [pathEndpointPair_snd]
            _ = ((s.snd ≫ endingPathIncl Y y) ≫
                pathEndpointPair Y) ≫ Limits.prod.snd :=
              (Category.assoc _ _ _).symm
  refine { w := hw, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk
    (pathHomotopyFiberToEndingPath_evalZero f y).symm
    (fun s => pullback.lift
      (Limits.prod.lift s.fst
        (SSet.stdSimplex.isTerminalObj₀.from _))
      (s.snd ≫ endingPathIncl Y y) (hcompat s))
    (fun s => by
      rw [pathHomotopyFiberToTotal, ← Category.assoc, pullback.lift_fst]
      simp)
    (fun s => by
      apply (cancel_mono (endingPathIncl Y y)).mp
      rw [Category.assoc, pathHomotopyFiberToEndingPath_incl,
        pullback.lift_snd])
    (fun s m h₁ h₂ => by
      apply pullback.hom_ext
      · apply Limits.prod.hom_ext
        · calc
            (m ≫ pullback.fst
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{u})) y))
                (pathEndpointPair Y)) ≫ Limits.prod.fst =
                m ≫ pathHomotopyFiberToTotal f y := by rfl
            _ = s.fst := h₁
            _ = (pullback.lift
                  (Limits.prod.lift s.fst
                    (SSet.stdSimplex.isTerminalObj₀.from _))
                  (s.snd ≫ endingPathIncl Y y) (hcompat s) ≫
                pullback.fst
                  (Limits.prod.map f
                    (SSet.const (X := (Δ[0] : SSet.{u})) y))
                  (pathEndpointPair Y)) ≫ Limits.prod.fst := by
              rw [pullback.lift_fst, Limits.prod.lift_fst]
        · apply SSet.stdSimplex.isTerminalObj₀.hom_ext
      · have h := congrArg (fun k => k ≫ endingPathIncl Y y) h₂
        calc
          m ≫ pullback.snd
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{u})) y))
                (pathEndpointPair Y) =
              m ≫ pathHomotopyFiberPath f y := by rfl
          _ = s.snd ≫ endingPathIncl Y y := by
            simpa [Category.assoc] using h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (SSet.stdSimplex.isTerminalObj₀.from _))
                (s.snd ≫ endingPathIncl Y y) (hcompat s) ≫
              pullback.snd
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{u})) y))
                (pathEndpointPair Y) := by rw [pullback.lift_snd])⟩

private theorem mono_from_zero {Z : SSet.{u}}
    (z : (Δ[0] : SSet.{u}) ⟶ Z) : Mono z := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _
  apply SSet.stdSimplex.objEquiv.injective
  subsingleton

private abbrev strictFiber {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber f y

private theorem strictFiberToPathHomotopyFiber_total
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    strictFiberToPathHomotopyFiber f y ≫ pathHomotopyFiberToTotal f y =
      (Subcomplex.fiber f y).ι :=
  strictFiberToPathHomotopyFiber_toTotal f y

private theorem strictFiberToPathHomotopyFiber_isPullback
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    IsPullback (strictFiberToPathHomotopyFiber f y)
      (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y))
      (pathHomotopyFiberToEndingPath f y) (endingPathConstant Y y) := by
  have hright := pathHomotopyFiber_isPullback_endingPath f y
  have houter : IsPullback
      (strictFiberToPathHomotopyFiber f y ≫
        pathHomotopyFiberToTotal f y)
      (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y)) f
      (endingPathConstant Y y ≫ endingPathEvalZero Y y) := by
    simpa using Subcomplex.fiber_isPullback f y
  apply houter.of_right
  · apply (cancel_mono (endingPathIncl Y y)).mp
    rw [Category.assoc, pathHomotopyFiberToEndingPath_incl,
      strictFiberToPathHomotopyFiber_path]
    rw [Category.assoc, endingPathConstant_incl]
    rw [← Category.assoc]
    congr 1
  · exact hright

private theorem strictFiberToPathHomotopyFiber_realization_mem
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) [Fibration f] :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (strictFiberToPathHomotopyFiber f y)) := by
  let q := pathHomotopyFiberToEndingPath f y
  let k := endingPathConstant Y y
  let a := strictFiberToPathHomotopyFiber f y
  let hq : IsPullback (pathHomotopyFiberToTotal f y) q f
      (endingPathEvalZero Y y) :=
    pathHomotopyFiber_isPullback_endingPath f y
  let hk : IsPullback a
      (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y)) q k :=
    strictFiberToPathHomotopyFiber_isPullback f y
  let _ : Fibration q := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    exact MorphismProperty.of_isPullback hq (by
      rw [← SSet.modelCategoryQuillen.fibration_iff]
      infer_instance)
  let _ : Mono k := mono_from_zero k
  let hTop := hk.flip.map_toTop_of_mono
  let _ : WeakEquivalence (SSet.toTop.map k) :=
    (weakEquivalence_iff _).2
      (endingPathConstant_mem_weakHomotopyEquivalences Y y)
  let _ : IsRightProper TopCat.{u} := TopCat.modelCategory.rightProper
  have ha : WeakEquivalence (SSet.toTop.map a) :=
    IsRightProper.weakEquivalence_of_isPullback hTop
  exact (weakEquivalence_iff _).1 ha

private noncomputable def realizedZeroIsTerminal :
    IsTerminal (SSet.toTop.obj (Δ[0] : SSet.{u})) := by
  let _ : ∀ Z : TopCat.{u}, Unique
      (Z ⟶ SSet.toTop.obj (Δ[0] : SSet.{u})) := fun Z =>
    { default := TopCat.ofHom ⟨fun _ => default, continuous_const⟩
      uniq := by
        intro g
        apply TopCat.hom_ext
        ext z
        exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

private noncomputable def realizedZeroIso :
    SSet.toTop.obj (Δ[0] : SSet.{u}) ≅ TopCat.of PUnit :=
  realizedZeroIsTerminal.uniqueUpToIso TopCat.isTerminalPUnit

private theorem realizedStrictFiber_isPullback
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    IsPullback
      (SSet.toTop.map (Subcomplex.fiber f y).ι)
      (SSet.toTop.map
        (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y)) ≫
          realizedZeroIso.hom)
      (SSet.toTop.map f) (TopCat.const (SSet.realizedVertex y)) := by
  let k := SSet.const (X := (Δ[0] : SSet.{u})) y
  let _ : Mono k := mono_from_zero k
  have hMapped : IsPullback
      (SSet.toTop.map (Subcomplex.fiber f y).ι)
      (SSet.toTop.map
        (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y)))
      (SSet.toTop.map f) (SSet.toTop.map k) := by
    exact ((Subcomplex.fiber_isPullback f y).flip.map_toTop_of_mono).flip
  apply hMapped.of_iso (Iso.refl _) (Iso.refl _) realizedZeroIso (Iso.refl _)
  · simp
  · rfl
  · simp
  · change SSet.toTop.map k =
      realizedZeroIso.hom ≫ TopCat.const (SSet.realizedVertex y)
    rw [toTop_map_const]
    ext z
    rfl

private noncomputable def realizedStrictFiberIso
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    SSet.toTop.obj (strictFiber f y) ≅
      pullback (SSet.toTop.map f)
        (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)) :=
  (realizedStrictFiber_isPullback f y).isoIsPullback
    (SSet.toTop.obj X) (TopCat.of PUnit)
      (IsPullback.of_hasPullback (SSet.toTop.map f)
        (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)))

@[reassoc (attr := simp)]
private theorem realizedStrictFiberIso_hom_fst
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    (realizedStrictFiberIso f y).hom ≫
        pullback.fst (SSet.toTop.map f)
          (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)) =
      SSet.toTop.map (Subcomplex.fiber f y).ι :=
  (realizedStrictFiber_isPullback f y).isoIsPullback_hom_fst
    (SSet.toTop.obj X) (TopCat.of PUnit)
      (IsPullback.of_hasPullback (SSet.toTop.map f)
        (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)))

@[reassoc (attr := simp)]
private theorem realizedStrictFiberIso_hom_snd
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    (realizedStrictFiberIso f y).hom ≫
        pullback.snd (SSet.toTop.map f)
          (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)) =
      SSet.toTop.map
          (SSet.stdSimplex.isTerminalObj₀.from (strictFiber f y)) ≫
        realizedZeroIso.hom :=
  (realizedStrictFiber_isPullback f y).isoIsPullback_hom_snd
    (SSet.toTop.obj X) (TopCat.of PUnit)
      (IsPullback.of_hasPullback (SSet.toTop.map f)
        (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex y)))

private theorem strictFiberComparison_square
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    SSet.toTop.map (strictFiberToPathHomotopyFiber f y) ≫
        pathHomotopyFiberRealizationComparison f y =
      (realizedStrictFiberIso f y).hom ≫
        TopCat.strictFiberToHomotopyFiber
          (SSet.toTop.map f) (SSet.realizedVertex y) := by
  apply TopCat.homotopyPullback_hom_ext
  · rw [Category.assoc,
      pathHomotopyFiberRealizationComparison_toTotal]
    rw [← Functor.map_comp, strictFiberToPathHomotopyFiber_total]
    rw [Category.assoc, TopCat.strictFiberToHomotopyFiber_toTotal,
      realizedStrictFiberIso_hom_fst]
  · apply TopCat.isTerminalPUnit.hom_ext
  · calc
      (SSet.toTop.map (strictFiberToPathHomotopyFiber f y) ≫
          pathHomotopyFiberRealizationComparison f y) ≫
          TopCat.homotopyFiberPath
            (SSet.toTop.map f) (SSet.realizedVertex y) =
        TopCat.const (X := SSet.toTop.obj (strictFiber f y))
            (SSet.realizedVertex y) ≫
          TopCat.pathConstant (SSet.toTop.obj Y) := by
            rw [Category.assoc,
              pathHomotopyFiberRealizationComparison_path]
            rw [← Category.assoc, ← Functor.map_comp,
              strictFiberToPathHomotopyFiber_path]
            rw [Functor.map_comp, Category.assoc,
              constPath_pathSpaceRealizationComparison, toTop_map_const]
      _ = ((realizedStrictFiberIso f y).hom ≫
          TopCat.strictFiberToHomotopyFiber
            (SSet.toTop.map f) (SSet.realizedVertex y)) ≫
          TopCat.homotopyFiberPath
            (SSet.toTop.map f) (SSet.realizedVertex y) := by
            rw [Category.assoc,
              TopCat.strictFiberToHomotopyFiber_path]
            rw [← Category.assoc, realizedStrictFiberIso_hom_snd]
            ext z t
            rfl

/-- Realization of a simplicial path homotopy fiber compares weakly to the
compact-open homotopy fiber of the realized fibration. -/
theorem pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (y : Y.obj (Opposite.op (SimplexCategory.mk 0))) [Fibration f] :
    TopCat.weakHomotopyEquivalences
      (pathHomotopyFiberRealizationComparison f y) := by
  have ha : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (strictFiberToPathHomotopyFiber f y)) :=
    strictFiberToPathHomotopyFiber_realization_mem f y
  have he : TopCat.weakHomotopyEquivalences
      (realizedStrictFiberIso f y).hom :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hj : TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber
        (SSet.toTop.map f) (SSet.realizedVertex y)) :=
    TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
      (SSet.toTop.map f) (SSet.realizedVertex y)
  have hac : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (strictFiberToPathHomotopyFiber f y) ≫
        pathHomotopyFiberRealizationComparison f y) := by
    rw [strictFiberComparison_square]
    exact TopCat.weakHomotopyEquivalences.comp_mem _ _ he hj
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _ ha hac


/-! ## Weak base change -/

private noncomputable def pathTailContraction (Y : SSet.{u}) :
    SSet.Homotopy (𝟙 (pathSpace Y)) (eval₁ ≫ constPath Y) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  refine
    { h := pathTailContractionMap Y
      h₀ := pathTailContractionMap_timeZero Y
      h₁ := pathTailContractionMap_timeOne Y
      rel := ?_ }
  ext m ⟨⟨z, hz⟩, t⟩
  cases hz

private theorem evalOne_mem_realizationWeakEquivalences (Y : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (eval₁ : pathSpace Y ⟶ Y) := by
  let p : pathSpace Y ⟶ Y := eval₁
  let s : Y ⟶ pathSpace Y := constPath Y
  let e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (pathSpace Y)) (SSet.toTop.obj Y) :=
    { toFun := (SSet.toTop.map p).hom
      invFun := (SSet.toTop.map s).hom
      left_inv := by
        have hR := SSet.realizeHomotopy _ _ (𝟙 _) (p ≫ s)
          (pathTailContraction Y)
        have hR' : ContinuousMap.Homotopy
            ((SSet.toTop.map s).hom.comp (SSet.toTop.map p).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id, p, s] using hR.symm
        exact ⟨hR'⟩
      right_inv := by
        have hcomp : SSet.toTop.map s ≫ SSet.toTop.map p = 𝟙 _ := by
          calc
            SSet.toTop.map s ≫ SSet.toTop.map p =
                SSet.toTop.map (s ≫ p) :=
              (SSet.toTop.map_comp s p).symm
            _ = SSet.toTop.map (𝟙 _) := by simp [p, s]
            _ = 𝟙 _ := SSet.toTop.map_id _
        rw [show (SSet.toTop.map p).hom.comp (SSet.toTop.map s).hom =
            (SSet.toTop.map s ≫ SSet.toTop.map p).hom by rfl, hcomp]
        exact ⟨ContinuousMap.Homotopy.refl _⟩ }
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
  exact TopCat.homotopyEquiv_toFun_mem e

private theorem pathSpaceMap_mem_realizationWeakEquivalences
    {Y Y' : SSet.{u}} (h : Y ⟶ Y')
    (hh : SSet.realizationWeakEquivalences h) :
    SSet.realizationWeakEquivalences
      ((ihom (Δ[1] : SSet.{u})).map h) := by
  have hp := evalOne_mem_realizationWeakEquivalences Y
  have hp' := evalOne_mem_realizationWeakEquivalences Y'
  have hc : SSet.realizationWeakEquivalences
      (((ihom (Δ[1] : SSet.{u})).map h) ≫ eval₁) := by
    rw [pathSpace_map_eval₁]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hp hh
  exact SSet.realizationWeakEquivalences.of_postcomp _ _ hp' hc


private noncomputable abbrev baseChangeEndpointPair (C : SSet.{u}) :
    pathSpace C ⟶ C ⨯ C :=
  pathEndpointPair C

@[reassoc (attr := simp), nolint simpNF]
private theorem baseChangeEndpointPair_fst (C : SSet.{u}) :
    baseChangeEndpointPair C ≫ Limits.prod.fst = eval₀ :=
  pathEndpointPair_fst C

@[reassoc (attr := simp), nolint simpNF]
private theorem baseChangeEndpointPair_snd (C : SSet.{u}) :
    baseChangeEndpointPair C ≫ Limits.prod.snd = eval₁ :=
  pathEndpointPair_snd C

attribute [nolint simpNF] baseChangeEndpointPair_fst_assoc baseChangeEndpointPair_snd_assoc

private theorem baseChangeEndpointPair_naturality
    {C C' : SSet.{u}} (h : C ⟶ C') :
    (ihom (Δ[1] : SSet.{u})).map h ≫ baseChangeEndpointPair C' =
      baseChangeEndpointPair C ≫ Limits.prod.map h h := by
  apply Limits.prod.hom_ext
  · calc
      _ = (ihom (Δ[1] : SSet.{u})).map h ≫ eval₀ := by
        simpa only [Category.assoc] using
          congrArg ((ihom (Δ[1] : SSet.{u})).map h ≫ ·)
            (baseChangeEndpointPair_fst C')
      _ = eval₀ ≫ h := pathSpace_map_eval₀ h
      _ = _ := by
        simpa only [Category.assoc, Limits.prod.map_fst] using
          (congrArg (· ≫ h) (baseChangeEndpointPair_fst C)).symm
  · calc
      _ = (ihom (Δ[1] : SSet.{u})).map h ≫ eval₁ := by
        simpa only [Category.assoc] using
          congrArg ((ihom (Δ[1] : SSet.{u})).map h ≫ ·)
            (baseChangeEndpointPair_snd C')
      _ = eval₁ ≫ h := pathSpace_map_eval₁ h
      _ = _ := by
        simpa only [Category.assoc, Limits.prod.map_snd] using
          (congrArg (· ≫ h) (baseChangeEndpointPair_snd C)).symm

private noncomputable abbrev pathFiberCospan
    {A C : SSet.{u}} (q : A ⟶ C) (c : C _⦋0⦌) :
    WalkingCospan ⥤ SSet.{u} :=
  cospan
    (Limits.prod.map q (SSet.const (X := (Δ[0] : SSet.{u})) c))
    (baseChangeEndpointPair C)

private noncomputable def pathFiberCospanMap
    {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
    (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
    {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c') :
    pathFiberCospan q c ⟶ pathFiberCospan q' c' :=
  cospanHomMk
    (Limits.prod.map h h)
    (Limits.prod.map l (𝟙 (Δ[0] : SSet.{u})))
    ((ihom (Δ[1] : SSet.{u})).map h)
    (by
      change
        Limits.prod.map q (SSet.const c) ≫ Limits.prod.map h h =
          Limits.prod.map l (𝟙 (Δ[0] : SSet.{u})) ≫
            Limits.prod.map q' (SSet.const c')
      apply Limits.prod.hom_ext
      · simpa [Category.assoc] using
          congrArg (fun k => Limits.prod.fst ≫ k) hq
      · have hconst : SSet.const c ≫ h =
            (𝟙 (Δ[0] : SSet.{u})) ≫ SSet.const c' := by
          simp [SSet.const_comp, hc]
        simpa [Category.assoc] using
          congrArg (fun k => Limits.prod.snd ≫ k) hconst)
    (baseChangeEndpointPair_naturality h).symm

open scoped SSet.modelCategoryQuillen in
private theorem baseChangeEndpointPair_fibration (C : SSet.{u}) [KanComplex C] :
    Fibration (baseChangeEndpointPair C) := by
  let e := (CartesianMonoidalCategory.tensorLeftIsoProd C).app C
  change Fibration ((evalPair : pathSpace C ⟶ C ⊗ C) ≫ e.hom)
  rw [fibration_iff]
  apply (fibrations SSet.{u}).comp_mem
  · rw [← fibration_iff]
    infer_instance
  · exact (fibrations SSet.{u}).of_isIso e.hom

set_option backward.isDefEq.respectTransparency false in
private theorem limitMap_pathFiberCospanMap
    {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
    (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
    {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c') :
    lim.map (pathFiberCospanMap l h hq hc) =
      pathHomotopyFiberMap l h hq hc := by
  apply pathHomotopyFiber_hom_ext
  · rw [pathHomotopyFiberMap_toTotal]
    change
      lim.map (pathFiberCospanMap l h hq hc) ≫
          limit.π (pathFiberCospan q' c') WalkingCospan.left ≫
            Limits.prod.fst =
        (limit.π (pathFiberCospan q c) WalkingCospan.left ≫
          Limits.prod.fst) ≫ l
    rw [← Category.assoc, limit.map_π]
    change
      (limit.π (pathFiberCospan q c) WalkingCospan.left ≫
          Limits.prod.map l (𝟙 (Δ[0] : SSet.{u}))) ≫
        Limits.prod.fst = _
    simp
  · rw [pathHomotopyFiberMap_path]
    change
      lim.map (pathFiberCospanMap l h hq hc) ≫
          limit.π (pathFiberCospan q' c') WalkingCospan.right =
        limit.π (pathFiberCospan q c) WalkingCospan.right ≫
          (ihom (Δ[1] : SSet.{u})).map h
    rw [limit.map_π]
    rfl

open scoped SSet.modelCategoryQuillen in
theorem pathHomotopyFiberMap_mem_realizationWeakEquivalences
    {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
    (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
    {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
    [KanComplex C] [KanComplex C'] [IsRightProper SSet.{u}]
    [HasFunctorialFactorization
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
    (hl : realizationWeakEquivalences l)
    (hh : realizationWeakEquivalences h) :
    realizationWeakEquivalences (pathHomotopyFiberMap l h hq hc) := by
  let F := pathFiberCospan q c
  let G := pathFiberCospan q' c'
  let eta : F ⟶ G := pathFiberCospanMap l h hq hc
  let _ : Fibration (F.map WalkingCospan.Hom.inr) := by
    change Fibration (baseChangeEndpointPair C)
    exact baseChangeEndpointPair_fibration C
  let _ : Fibration (G.map WalkingCospan.Hom.inr) := by
    change Fibration (baseChangeEndpointPair C')
    exact baseChangeEndpointPair_fibration C'
  have hleft : WeakEquivalence
      (Limits.prod.map l (𝟙 (Δ[0] : SSet.{u}))) := by
    rw [weakEquivalence_iff]
    exact realizationWeakEquivalences.prodMap_id_of_finite_right l hl
  have hright : WeakEquivalence
      ((ihom (Δ[1] : SSet.{u})).map h) := by
    rw [weakEquivalence_iff]
    exact pathSpaceMap_mem_realizationWeakEquivalences h hh
  have hW : KanComplex.W h :=
    (KanComplex.W_iff_realizationWeakEquivalence h).2 hh
  have hone : WeakEquivalence (Limits.prod.map h h) := by
    let hProdW := KanComplex.W.prodMap hW hW
    let _ : KanComplex (C ⨯ C) := hProdW.kanComplex_source
    let _ : KanComplex (C' ⨯ C') := hProdW.kanComplex_target
    rw [weakEquivalence_iff]
    exact (KanComplex.W_iff_realizationWeakEquivalence _).1
      hProdW
  have heta : ∀ j, WeakEquivalence (eta.app j) := by
    intro j
    rcases j with (_ | _ | _)
    · change WeakEquivalence (Limits.prod.map h h)
      exact hone
    · change WeakEquivalence
        (Limits.prod.map l (𝟙 (Δ[0] : SSet.{u})))
      exact hleft
    · change WeakEquivalence ((ihom (Δ[1] : SSet.{u})).map h)
      exact hright
  have hF : WeakEquivalence
      ((homotopyPullbackComparison (C := SSet.{u})).app F) :=
    weakEquivalence_homotopyPullbackComparison_of_rightProper_inr F
  have hG : WeakEquivalence
      ((homotopyPullbackComparison (C := SSet.{u})).app G) :=
    weakEquivalence_homotopyPullbackComparison_of_rightProper_inr G
  have hDerived : WeakEquivalence
      ((homotopyPullback (C := SSet.{u})).map eta) :=
    homotopyPullback_map_weakEquivalence eta heta
  have hComposite : WeakEquivalence
      (lim.map eta ≫
        (homotopyPullbackComparison (C := SSet.{u})).app G) := by
    rw [(homotopyPullbackComparison (C := SSet.{u})).naturality eta]
    rw [weakEquivalence_iff] at hF hDerived ⊢
    exact (weakEquivalences SSet.{u}).comp_mem _ _ hF hDerived
  have hLimit : WeakEquivalence (lim.map eta) := by
    rw [weakEquivalence_iff] at hG hComposite ⊢
    exact (weakEquivalences SSet.{u}).of_postcomp _ _ hG hComposite
  rw [← limitMap_pathFiberCospanMap]
  exact (weakEquivalence_iff _).1 hLimit

end SSet

end


public section

namespace SSet

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

/-- The actual strict-to-ending-path comparison of a simplicial fibration is
weak for the canonical realization property. This exposes its existing proof. -/
theorem strictFiberToPathHomotopyFiber_mem_realizationWeakEquivalences
    {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) [Fibration f] :
    SSet.realizationWeakEquivalences (strictFiberToPathHomotopyFiber f y) :=
  strictFiberToPathHomotopyFiber_realization_mem f y

end SSet
