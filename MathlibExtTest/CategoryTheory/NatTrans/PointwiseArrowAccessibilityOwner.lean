/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
public import Mathlib.CategoryTheory.Presentable.Comma

/-!
# Arrow-valued accessibility contracts

These clients retain arbitrary original arrows, both endpoint functors,
and an independently chosen accessibility universe and cardinal.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uB vB uC vC

open CategoryTheory

namespace CategoryTheory.Functor.ArrowAccessibilityOwner

variable {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]

/-- The entire original Arrow-valued functor is accessible from both endpoint projections. -/
theorem originalFunctor (T : B ⥤ Arrow C) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [(T ⋙ Arrow.leftFunc).IsCardinalAccessible μ]
    [(T ⋙ Arrow.rightFunc).IsCardinalAccessible μ] : T.IsCardinalAccessible μ :=
  T.isCardinalAccessible_toArrow μ

/-- A natural transformation retains the original two endpoint functors. -/
theorem originalTransformation {F G : B ⥤ C} (α : F ⟶ G)
    (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [F.IsCardinalAccessible μ] [G.IsCardinalAccessible μ] :
    (NatTrans.arrow α).IsCardinalAccessible μ := by
  let _ : (NatTrans.arrow α ⋙ Arrow.leftFunc).IsCardinalAccessible μ := by
    change F.IsCardinalAccessible μ
    infer_instance
  let _ : (NatTrans.arrow α ⋙ Arrow.rightFunc).IsCardinalAccessible μ := by
    change G.IsCardinalAccessible μ
    infer_instance
  exact (NatTrans.arrow α).isCardinalAccessible_toArrow μ

/-- Every original mapped Arrow retains the same accessible coefficient functor. -/
theorem originalMappedArrows (F : B ⥤ C) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [HasCardinalFilteredColimits B μ] [F.IsCardinalAccessible μ] :
    F.mapArrow.IsCardinalAccessible μ := by
  let _ : (Arrow.leftFunc : Arrow B ⥤ B).IsCardinalAccessible μ :=
    inferInstanceAs ((Comma.fst (𝟭 B) (𝟭 B)).IsCardinalAccessible μ)
  let _ : (Arrow.rightFunc : Arrow B ⥤ B).IsCardinalAccessible μ :=
    inferInstanceAs ((Comma.snd (𝟭 B) (𝟭 B)).IsCardinalAccessible μ)
  let _ : (F.mapArrow ⋙ Arrow.leftFunc).IsCardinalAccessible μ := by
    change (Arrow.leftFunc ⋙ F).IsCardinalAccessible μ
    infer_instance
  let _ : (F.mapArrow ⋙ Arrow.rightFunc).IsCardinalAccessible μ := by
    change (Arrow.rightFunc ⋙ F).IsCardinalAccessible μ
    infer_instance
  exact F.mapArrow.isCardinalAccessible_toArrow μ

end CategoryTheory.Functor.ArrowAccessibilityOwner

