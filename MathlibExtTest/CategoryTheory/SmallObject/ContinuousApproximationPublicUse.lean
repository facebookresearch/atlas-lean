/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.SmallObject.ContinuousApproximation
import Mathlib.CategoryTheory.Limits.Types.Colimits

set_option autoImplicit false
noncomputable section
universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.OriginalContinuousApproximation

namespace ContinuousApproximationNeutralPublicUse

variable {C : Type uC} [Category.{vC} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasColimitsOfSize.{w, w} C]
  (F : J ⥤ C) (q0 : Arrow C) {P R : MorphismProperty C}
  (factor : MorphismProperty.FunctorialFactorizationData P R)
  (hq0 : q0.right = F.obj ⊥)

/-- The neutral API supplies a continuous source on the original caller ordinal. -/
example : (sourceDiagram F q0 factor hq0).IsWellOrderContinuous :=
  sourceDiagram_continuous F q0 factor hq0

/-- An arbitrary original successor uses the same factory's left and right classes. -/
example (j : J) (hj : ¬IsMax j) :
    P ((sourceDiagram F q0 factor hq0).map (homOfLE (Order.le_succ j))) ∧
      R ((sourceCounit F q0 factor hq0).app (Order.succ j)) :=
  ⟨sourceDiagram_successor_mem F q0 factor hq0 j hj,
    sourceCounit_successor_mem F q0 factor hq0 j hj⟩

/-- The full natural counit retains the original input map on every ordinal arrow. -/
example {i j : J} (f : i ⟶ j) :
    (sourceDiagram F q0 factor hq0).map f ≫ (sourceCounit F q0 factor hq0).app j =
      (sourceCounit F q0 factor hq0).app i ≫ F.map f :=
  (sourceCounit F q0 factor hq0).naturality f

/-- The neutral construction uses the caller's actual source-limit cocone. -/
example (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone (sourceDiagram F q0 factor hq0)) :=
  sourceDiagramLimit F q0 factor hq0 m hm

end ContinuousApproximationNeutralPublicUse

namespace ContinuousApproximationFiniteTypes

/-- A changing diagram of finite types, independent of any spectrum or model structure. -/
def input : ℕ ⥤ Type where
  obj n := Fin (n + 1)
  map f := ↾(Fin.castLE (Nat.add_le_add_right (leOfHom f) 1))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Factor each ordinary type map through its actual target. -/
def factor : MorphismProperty.FunctorialFactorizationData
    (⊤ : MorphismProperty (Type)) ⊤ where
  Z := Arrow.rightFunc
  i := Arrow.leftToRight
  p := 𝟙 Arrow.rightFunc
  fac := Category.comp_id _
  hi _ := trivial
  hp _ := trivial

def bottom : Arrow (Type) := Arrow.mk (𝟙 (input.obj 0))

/-- The generic construction retains every actual target type and inclusion. -/
example : fullDiagram input bottom factor rfl ⋙ Arrow.rightFunc = input :=
  fullDiagram_target input bottom factor rfl

/-- Its complete original bottom arrow is retained on this concrete neutral diagram. -/
example : (fullDiagram input bottom factor rfl).obj 0 = bottom :=
  fullDiagram_bottom input bottom factor rfl

end ContinuousApproximationFiniteTypes
