/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Uniform relative smallness of the original generating sources

The source hypothesis quantifies over every sufficiently large regular
cardinal and every continuous sequence with relative-cell successor maps.
Each actual generator retains its own bound. It is distinct from
eligibility at one fixed cardinal.

The relative-cell class is the existing transfinite composition of
pushouts of working-size coproducts. The same original sequence,
endpoint inclusion and source Hom comparison are kept when the hypothesis
is applied. No model category or presentability assumption is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v t
open CategoryTheory Limits MorphismProperty Opposite

namespace CategoryTheory.SmallObject

variable {C : Type u} [Category.{v} C]

/-- Relative P-cell maps have the actual arbitrary working-size cellular presentation. -/
def relativeCellMaps (P : MorphismProperty C) : MorphismProperty C :=
  transfiniteCompositions.{w} (coproducts.{w} P).pushouts

/-- Every genuine single attachment belongs to the same relative-cell class. -/
theorem attachCells_mem_relativeCellMaps (P : MorphismProperty C)
    {X Y : C} {f : X ⟶ Y} (c : HomotopicalAlgebra.AttachCells.{w} P.homFamily f) :
    relativeCellMaps.{w} P f := by
  apply (le_transfiniteCompositions (coproducts.{w} P).pushouts) f
  simpa only [ofHoms_homFamily] using c.pushouts_coproducts

/-- A supplied full relative complex lies in this original relative-cell class. -/
theorem relativeCellComplex_mem_relativeCellMaps (P : MorphismProperty C)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {X Y : C} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.RelativeCellComplex.{w} (fun _ : J => P.homFamily) f) :
    relativeCellMaps.{w} P f := by
  apply (transfiniteCompositionsOfShape_le_transfiniteCompositions
    (coproducts.{w} P).pushouts J) f
  simpa only [ofHoms_homFamily] using c.transfiniteCompositionOfShape P.homFamily |>.mem

/-- The actual generating sources preserve all sufficiently long regular relative-cell chains. -/
def UniformRelativeSourceSmallness (P : MorphismProperty C) : Prop :=
  ∀ p : P.toSet, ∃ β : Cardinal.{w},
    ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType], β < κ →
      ∀ (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
        (∀ j : κ.ord.ToType, ¬ IsMax j →
          relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) →
        PreservesColimit F (coyoneda.obj (op p.1.left))

namespace UniformRelativeSourceSmallness

variable {P : MorphismProperty C} (h : UniformRelativeSourceSmallness.{w} P)

/-- The chosen bound belongs to the original actual generator arrow. -/
def sourceBound (p : P.toSet) : Cardinal.{w} := (h p).choose

/-- The selected bound retains the complete regular-cardinal and same-chain contract. -/
theorem sourceBound_spec (p : P.toSet)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : sourceBound h p < κ) (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op p.1.left)) :=
  (h p).choose_spec κ hκ F hF

/-- Any later bound remains valid for this same source, without enlarging fixed eligibility. -/
theorem sourceBound_mono (p : P.toSet) {β : Cardinal.{w}} (hβ : sourceBound h p ≤ β)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : β < κ) (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op p.1.left)) :=
  sourceBound_spec h p κ (hβ.trans_lt hκ) F hF

/-- The original canonical cocone remains colimiting after source Hom. -/
def mappedCanonicalCocone (p : P.toSet)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : sourceBound h p < κ) (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] :
    IsColimit ((coyoneda.obj (op p.1.left)).mapCocone (colimit.cocone F)) := by
  letI : PreservesColimit F (coyoneda.obj (op p.1.left)) := sourceBound_spec h p κ hκ F hF
  exact isColimitOfPreserves (coyoneda.obj (op p.1.left)) (colimit.isColimit F)

/-- Every arrow from the original source to this actual colimit factors through a stage. -/
theorem exists_stage_factor (p : P.toSet)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : sourceBound h p < κ) (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] (f : p.1.left ⟶ colimit F) :
    ∃ (j : κ.ord.ToType) (g : p.1.left ⟶ F.obj j), g ≫ colimit.ι F j = f := by
  let _ : PreservesColimit F (coyoneda.obj (op p.1.left)) := sourceBound_spec h p κ hκ F hF
  exact exists_hom_of_preservesColimit_coyoneda (colimit.isColimit F) f

/-- Equality at the original colimit is detected at an actual common later stage. -/
theorem exists_stage_equality (p : P.toSet)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : sourceBound h p < κ) (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] {i j : κ.ord.ToType}
    (f : p.1.left ⟶ F.obj i) (g : p.1.left ⟶ F.obj j)
    (hfg : f ≫ colimit.ι F i = g ≫ colimit.ι F j) :
    ∃ (k : κ.ord.ToType) (a : i ⟶ k) (b : j ⟶ k), f ≫ F.map a = g ≫ F.map b := by
  let _ : PreservesColimit F (coyoneda.obj (op p.1.left)) := sourceBound_spec h p κ hκ F hF
  exact exists_eq_of_preservesColimit_coyoneda (colimit.isColimit F) f g hfg

/-- Source Hom preserves the unchanged chain of each actual sufficiently long P-complex. -/
theorem preservesColimit_relativeCellComplex
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {A B X Y : C} (i : A ⟶ B) (hi : P i)
    (hκ : sourceBound h ⟨Arrow.mk i, hi⟩ < κ) (f : X ⟶ Y)
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) := by
  let _ : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact sourceBound_spec h ⟨Arrow.mk i, hi⟩ κ hκ c.F
    (fun j hj => attachCells_mem_relativeCellMaps P (c.attachCells j hj))

/-- The same actual endpoint cocone remains colimiting for the original generator source. -/
def relativeCellComplexMappedCocone
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {A B X Y : C} (i : A ⟶ B) (hi : P i)
    (hκ : sourceBound h ⟨Arrow.mk i, hi⟩ < κ) (f : X ⟶ Y)
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    IsColimit ((coyoneda.obj (op A)).mapCocone (Cocone.mk Y c.incl)) := by
  letI : PreservesColimit c.F (coyoneda.obj (op A)) :=
    preservesColimit_relativeCellComplex h κ i hi hκ f c
  exact isColimitOfPreserves (coyoneda.obj (op A)) c.isColimit

end UniformRelativeSourceSmallness

end CategoryTheory.SmallObject
