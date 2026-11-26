/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ColimitLimit
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits

namespace SSet.SharpSaturation

private theorem filteredColim_preservesFiniteLimits
    (J : Type v) [Category.{w} J] [Small.{u} J] [IsFiltered J] :
    PreservesFiniteLimits (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
    (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) K
  intro a
  let E : SSet.{u} ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
  let _ : PreservesLimitsOfShape K
      ((CategoryTheory.Functor.whiskeringRight J SSet.{u} (Type u)).obj E ⋙ colim) :=
    inferInstance
  exact preservesLimitsOfShape_of_natIso (preservesColimitNatIso E).symm

private theorem constant_preservesConnectedColimits
    (J : Type v) [Category.{w} J] [IsConnected J]
    (D : Type*) [Category* D] (X : SSet.{u}) :
    PreservesColimitsOfShape J ((CategoryTheory.Functor.const D).obj X) := by
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨?_⟩
  change IsColimit (constCocone J X)
  exact isColimitConstCocone J X

private def cospanFunctor {X Y : SSet.{u}} (p : X ⟶ Y) :
    Over Y ⥤ (WalkingCospan ⥤ SSet.{u}) where
  obj a := cospan a.hom p
  map {a b} f := cospanHomMk (𝟙 Y) f.left (𝟙 X)
    (by
      change a.hom ≫ 𝟙 Y = f.left ≫ b.hom
      simpa only [Category.comp_id] using (Over.w f).symm)
    (by simp)
  map_id a := by
    ext j
    rcases j with (_ | _ | _) <;> simp [cospanHomMk]
  map_comp f g := by
    ext j
    rcases j with (_ | _ | _) <;> simp [cospanHomMk]

private theorem cospanFunctor_preservesConnectedColimits
    (J : Type v) [Category.{w} J] [IsConnected J]
    {X Y : SSet.{u}} (p : X ⟶ Y) :
    PreservesColimitsOfShape J (cospanFunctor p) := by
  apply preservesColimitsOfShape_of_evaluation (cospanFunctor p) J
  rintro (_ | _ | _)
  · change PreservesColimitsOfShape J ((CategoryTheory.Functor.const (Over Y)).obj Y)
    exact constant_preservesConnectedColimits J (Over Y) Y
  · change PreservesColimitsOfShape J (Over.forget Y)
    infer_instance
  · change PreservesColimitsOfShape J ((CategoryTheory.Functor.const (Over Y)).obj X)
    exact constant_preservesConnectedColimits J (Over Y) X

private def cospanLimitIso {X Y : SSet.{u}} (p : X ⟶ Y) :
    cospanFunctor p ⋙ lim ≅ Over.pullback p ⋙ Over.forget X :=
  NatIso.ofComponents (fun a => Iso.refl _)
    (by
      intro a b f
      apply pullback.hom_ext
      · simp [cospanFunctor, cospanHomMk, Over.pullback]
      · simp [cospanFunctor, cospanHomMk, Over.pullback])

/-- Pullback along an arbitrary original simplicial map preserves working-small
filtered colimits in the original slice categories. -/
theorem overPullback_preservesColimitsOfShape_of_isFiltered
    (J : Type v) [Category.{w} J] [Small.{u} J] [IsFiltered J]
    {X Y : SSet.{u}} (p : X ⟶ Y) :
    PreservesColimitsOfShape J (Over.pullback p) := by
  let _ : IsConnected J := CategoryTheory.IsFiltered.isConnected J
  let _ : PreservesFiniteLimits (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) :=
    filteredColim_preservesFiniteLimits J
  let _ : PreservesColimitsOfShape J
      (lim : (WalkingCospan ⥤ SSet.{u}) ⥤ SSet.{u}) :=
    (preservesColimitsOfShape_lim_iff_preservesLimitsOfShape_colim
      WalkingCospan J SSet.{u}).2 inferInstance
  let _ : PreservesColimitsOfShape J (cospanFunctor p) :=
    cospanFunctor_preservesConnectedColimits J p
  let _ : PreservesColimitsOfShape J (Over.pullback p ⋙ Over.forget X) :=
    preservesColimitsOfShape_of_natIso (cospanLimitIso p)
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (Over.pullback p) (Over.forget X)

end SSet.SharpSaturation
