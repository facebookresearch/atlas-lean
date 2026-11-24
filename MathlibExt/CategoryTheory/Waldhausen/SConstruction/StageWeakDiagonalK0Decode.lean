/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalFundamentalGeneration
public import MathlibExt.KTheory.Waldhausen.K0.Basic
public import Mathlib.CategoryTheory.SingleObj

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.LowDegree
import Mathlib.CategoryTheory.Endomorphism

/-!
# Combinatorial K-zero decode for the weak-stage diagonal

An edge in the weak-stage diagonal is valued by the Waldhausen K-zero class
of the `(0, 1)` evaluation of its recovered left Stage-one object.  For an
arbitrary diagonal `2`-simplex, its three faces read the source, quotient,
and middle terms of a cofiber sequence, with the quotient transported across
the first pointwise weak Stage map.  This proves the relation required by the
simplicial fundamental-groupoid eliminator and hence defines a functor to the
single-object groupoid of multiplicative Waldhausen K-zero.

The resulting functor restricts to a monoid homomorphism on the based
fundamental group.  This file makes no commutativity, encode, inverse,
realization, additivity, spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- K-zero value of a diagonal edge, read from the `(0, 1)` evaluation of
its recovered left Stage-one object. -/
noncomputable def stageWeakDiagonalK0EdgeValue
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    CategoryTheory.End
      (SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C))) :=
  SingleObj.toEnd _
    (Multiplicative.ofAdd
      (WaldhausenKTheory.K0.mk
        ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)))

set_option backward.isDefEq.respectTransparency false in
private theorem stageWeakDiagonalK0_d2_eval
    {A₀ A₁ A₂ : StageWeakCategory C 2} (w₀₁ : A₀ ⟶ A₁)
    (w₁₂ : A₁ ⟶ A₂) :
    (stageOneEval C).obj
        (ComposableArrows.left
          ((stageWeakDiagonal C).δ 2
            (ComposableArrows.mk₂ w₀₁ w₁₂))).obj =
      A₀.obj.obj.obj
        (interval (0 : Fin 3) 1 (show (0 : Fin 3) ≤ 1 by decide)) := by
  change (stageOneEval C).obj
    (ComposableArrows.left
      ((stageWeakDiagonal C).map (SimplexCategory.δ 2).op
        (ComposableArrows.mk₂ w₀₁ w₁₂))).obj = _
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
          (ComposableArrows.mk₂ w₀₁ w₁₂) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 2).op)
            (ComposableArrows.mk₂ w₀₁ w₁₂)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂ w₀₁ w₁₂) =
      ComposableArrows.mk₁ w₀₁ :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  change A₀.obj.obj.obj
    ((indexFunctor (SimplexCategory.δ 2)).obj
      (interval (0 : Fin 2) 1 (show (0 : Fin 2) ≤ 1 by decide))) = _
  rw [indexFunctor_obj_interval]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem stageWeakDiagonalK0_d0_eval
    {A₀ A₁ A₂ : StageWeakCategory C 2} (w₀₁ : A₀ ⟶ A₁)
    (w₁₂ : A₁ ⟶ A₂) :
    (stageOneEval C).obj
        (ComposableArrows.left
          ((stageWeakDiagonal C).δ 0
            (ComposableArrows.mk₂ w₀₁ w₁₂))).obj =
      A₁.obj.obj.obj
        (interval (1 : Fin 3) 2 (show (1 : Fin 3) ≤ 2 by decide)) := by
  change (stageOneEval C).obj
    (ComposableArrows.left
      ((stageWeakDiagonal C).map (SimplexCategory.δ 0).op
        (ComposableArrows.mk₂ w₀₁ w₁₂))).obj = _
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
          (ComposableArrows.mk₂ w₀₁ w₁₂) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 0).op)
            (ComposableArrows.mk₂ w₀₁ w₁₂)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂ w₀₁ w₁₂) =
      ComposableArrows.mk₁ w₁₂ :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  change A₁.obj.obj.obj
    ((indexFunctor (SimplexCategory.δ 0)).obj
      (interval (0 : Fin 2) 1 (show (0 : Fin 2) ≤ 1 by decide))) = _
  rw [indexFunctor_obj_interval]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem stageWeakDiagonalK0_d1_eval
    {A₀ A₁ A₂ : StageWeakCategory C 2} (w₀₁ : A₀ ⟶ A₁)
    (w₁₂ : A₁ ⟶ A₂) :
    (stageOneEval C).obj
        (ComposableArrows.left
          ((stageWeakDiagonal C).δ 1
            (ComposableArrows.mk₂ w₀₁ w₁₂))).obj =
      A₀.obj.obj.obj
        (interval (0 : Fin 3) 2 (show (0 : Fin 3) ≤ 2 by decide)) := by
  change (stageOneEval C).obj
    (ComposableArrows.left
      ((stageWeakDiagonal C).map (SimplexCategory.δ 1).op
        (ComposableArrows.mk₂ w₀₁ w₁₂))).obj = _
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
          (ComposableArrows.mk₂ w₀₁ w₁₂) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 1).op)
            (ComposableArrows.mk₂ w₀₁ w₁₂)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂ w₀₁ w₁₂) =
      ComposableArrows.mk₁ (w₀₁ ≫ w₁₂) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  change A₀.obj.obj.obj
    ((indexFunctor (SimplexCategory.δ 1)).obj
      (interval (0 : Fin 2) 1 (show (0 : Fin 2) ≤ 1 by decide))) = _
  rw [indexFunctor_obj_interval]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The edge valuation respects every diagonal `2`-simplex.  Because
`SingleObj` reverses categorical composition, the proof explicitly commutes
the quotient and source K-zero summands before applying the cofiber relation. -/
theorem stageWeakDiagonalK0EdgeValue_comp
    {x₀ x₁ x₂ : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    {e₀₁ : (stageWeakDiagonal C).Edge x₀ x₁}
    {e₁₂ : (stageWeakDiagonal C).Edge x₁ x₂}
    {e₀₂ : (stageWeakDiagonal C).Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((stageWeakDiagonalK0EdgeValue C e₀₁).asHom :
        SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C)) ⟶
          SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C))) ≫
      ((stageWeakDiagonalK0EdgeValue C e₁₂).asHom :
        SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C)) ⟶
          SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C))) =
        ((stageWeakDiagonalK0EdgeValue C e₀₂).asHom :
          SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C)) ⟶
            SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C))) := by
  obtain ⟨A₀, A₁, A₂, w₀₁, w₁₂, hs⟩ :=
    ComposableArrows.mk₂_surjective h.simplex
  have hd₂ : (stageWeakDiagonalK0EdgeValue C e₀₁).asHom =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk
        (A₀.obj.obj.obj
          (interval (0 : Fin 3) 1 (show (0 : Fin 3) ≤ 1 by decide)))) := by
    unfold stageWeakDiagonalK0EdgeValue
    rw [← h.d₂, hs, stageWeakDiagonalK0_d2_eval]
    rfl
  have hd₀ : (stageWeakDiagonalK0EdgeValue C e₁₂).asHom =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk
        (A₁.obj.obj.obj
          (interval (1 : Fin 3) 2 (show (1 : Fin 3) ≤ 2 by decide)))) := by
    unfold stageWeakDiagonalK0EdgeValue
    rw [← h.d₀, hs, stageWeakDiagonalK0_d0_eval]
    rfl
  have hd₁ : (stageWeakDiagonalK0EdgeValue C e₀₂).asHom =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk
        (A₀.obj.obj.obj
          (interval (0 : Fin 3) 2 (show (0 : Fin 3) ≤ 2 by decide)))) := by
    unfold stageWeakDiagonalK0EdgeValue
    rw [← h.d₁, hs, stageWeakDiagonalK0_d1_eval]
    rfl
  have hw : IsWeakEquivalence
      (w₀₁.hom.hom.app
        (interval (1 : Fin 3) 2 (show (1 : Fin 3) ≤ 2 by decide))) := by
    change IsWeakEquivalence
      ((eval C 2
        (interval (1 : Fin 3) 2
          (show (1 : Fin 3) ≤ 2 by decide))).map w₀₁.hom)
    exact w₀₁.property _
  have hweak :
      (WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (1 : Fin 3) 2
              (show (1 : Fin 3) ≤ 2 by decide))) :
        WaldhausenKTheory.K0 C) =
      WaldhausenKTheory.K0.mk
        (A₁.obj.obj.obj
          (interval (1 : Fin 3) 2
            (show (1 : Fin 3) ≤ 2 by decide))) :=
    WaldhausenKTheory.K0.mk_eq_of_weakEquivalence _ hw
  have hcofiber :
      (WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (0 : Fin 3) 2
              (show (0 : Fin 3) ≤ 2 by decide))) :
        WaldhausenKTheory.K0 C) =
      WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (0 : Fin 3) 1
              (show (0 : Fin 3) ≤ 1 by decide))) +
        WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (1 : Fin 3) 2
              (show (1 : Fin 3) ≤ 2 by decide))) :=
    WaldhausenKTheory.K0.mk_eq_of_cofibrationSequence
      (Stage.cofiber_zero_one_two C A₀.obj)
  rw [SingleObj.comp_as_mul, hd₀, hd₂, hd₁,
    ← ofAdd_add]
  apply Multiplicative.ofAdd.injective
  calc
    WaldhausenKTheory.K0.mk
          (A₁.obj.obj.obj
            (interval (1 : Fin 3) 2
              (show (1 : Fin 3) ≤ 2 by decide))) +
        WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (0 : Fin 3) 1
              (show (0 : Fin 3) ≤ 1 by decide))) =
      WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (1 : Fin 3) 2
              (show (1 : Fin 3) ≤ 2 by decide))) +
        WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (0 : Fin 3) 1
              (show (0 : Fin 3) ≤ 1 by decide))) := by rw [hweak]
    _ = WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (0 : Fin 3) 1
              (show (0 : Fin 3) ≤ 1 by decide))) +
        WaldhausenKTheory.K0.mk
          (A₀.obj.obj.obj
            (interval (1 : Fin 3) 2
              (show (1 : Fin 3) ≤ 2 by decide))) := add_comm _ _
    _ = WaldhausenKTheory.K0.mk
        (A₀.obj.obj.obj
          (interval (0 : Fin 3) 2
            (show (0 : Fin 3) ≤ 2 by decide))) := hcofiber.symm

/-- Functor from the weak-diagonal fundamental groupoid to the single-object
groupoid of multiplicative Waldhausen K-zero. -/
noncomputable def stageWeakDiagonalK0Functor :
    SSet.FundamentalGroupoid (stageWeakDiagonal C) ⥤
      SingleObj (Multiplicative (WaldhausenKTheory.K0 C)) :=
  SSet.FundamentalGroupoid.desc
    (fun _ => SingleObj.star _)
    (fun e => (stageWeakDiagonalK0EdgeValue C e).asHom)
    (stageWeakDiagonalK0EdgeValue_comp C)

@[simp]
theorem stageWeakDiagonalK0Functor_obj_mk
    (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonalK0Functor C).obj
        (SSet.FundamentalGroupoid.mk x) =
      SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C)) :=
  rfl

/-- Computation of the decode functor on an arbitrary edge generator. -/
@[simp]
theorem stageWeakDiagonalK0Functor_map_homMk
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    (stageWeakDiagonalK0Functor C).map
        (SSet.FundamentalGroupoid.homMk e) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.mk
          ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)) :=
  SSet.FundamentalGroupoid.desc_map_homMk _ _ _ e

/-- The decode functor sends a canonical object generator to its K-zero
class. -/
@[simp]
theorem stageWeakDiagonalK0Functor_map_objectGenerator (A : C) :
    (stageWeakDiagonalK0Functor C).map
        (stageWeakDiagonalObjectGenerator C A).asHom =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A) := by
  rw [stageWeakDiagonalObjectGenerator,
    stageWeakDiagonalK0Functor_map_homMk]
  change Multiplicative.ofAdd
      (WaldhausenKTheory.K0.mk ((stageOneEval C).obj ((stageOne C).obj A))) =
    Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A)
  apply Multiplicative.ofAdd.injective
  exact congrArg WaldhausenKTheory.K0.mk (stageOneEval_obj C A)

/-- Decode homomorphism on the based combinatorial fundamental group. -/
noncomputable def stageWeakDiagonalFundamentalToK0 :
    stageWeakDiagonalFundamentalGroup C →*
      Multiplicative (WaldhausenKTheory.K0 C) :=
  (SingleObj.toEnd
      (Multiplicative (WaldhausenKTheory.K0 C))).symm.toMonoidHom.comp
    ((stageWeakDiagonalK0Functor C).mapEnd
      (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)))

/-- The based decode homomorphism sends each canonical object generator to
its K-zero class. -/
@[simp]
theorem stageWeakDiagonalFundamentalToK0_objectGenerator (A : C) :
    stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalObjectGenerator C A) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A) := by
  exact stageWeakDiagonalK0Functor_map_objectGenerator C A

end CategoryTheory.Waldhausen.SConstruction

end


public section

noncomputable section

open CategoryTheory Limits

universe uK vK

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type uK) [Category.{vK} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original fundamental-group decode is the map of its K-zero functor. -/
theorem stageWeakDiagonalFundamentalToK0_apply (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalToK0 C g = (stageWeakDiagonalK0Functor C).map g.asHom := rfl

end CategoryTheory.Waldhausen.SConstruction

end
