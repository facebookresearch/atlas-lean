/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Source colimits preserving the actual selected filtered diagram

Hom from a source colimit preserves the given cardinal-filtered diagram when
Hom from every actual constituent does. The proof reuses Mathlib's precise
pointwise limit/colimit witness. It assumes no global source presentability,
accessibility or locally presentable model category.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v w uK vK

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- Hom from this actual small source colimit preserves this one original
cardinal-filtered diagram, without a global presentability assumption. -/
theorem preservesColimit_coyoneda_of_isColimit
    {C : Type u} [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ C)
    {K : Type uK} [Category.{vK} K] [HasLimitsOfShape Kᵒᵖ (Type v)]
    {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c)
    (hK : HasCardinalLT (Arrow K) κ)
    (hSources : ∀ k : K, PreservesColimit F (coyoneda.obj (Opposite.op (D.obj k)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op c.pt)) := by
  let cH : Cone (D.op ⋙ coyoneda) := coyoneda.mapCone c.op
  have hLimit : IsLimit cH := isLimitOfPreserves coyoneda hc.op
  refine { preserves := ?_ }
  intro cF hcF
  refine ⟨Functor.Accessible.Limits.isColimitMapCocone cH
    (fun Y => isLimitOfPreserves ((evaluation C (Type v)).obj Y) hLimit)
    κ (by simpa using hK) cF ?_⟩
  intro k
  let _ : PreservesColimit F ((D.op ⋙ coyoneda).obj k) := by
    change PreservesColimit F (coyoneda.obj (Opposite.op (D.obj k.unop)))
    exact hSources k.unop
  exact isColimitOfPreserves ((D.op ⋙ coyoneda).obj k) hcF

/-- A finite actual source diagram has the required original-cardinal bound.
Its colimit source preserves the same selected diagram as its constituents. -/
theorem preservesColimit_coyoneda_of_finiteColimit
    {C : Type u} [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ C)
    {K : Type} [SmallCategory K] [FinCategory K]
    {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c)
    (hSources : ∀ k : K, PreservesColimit F (coyoneda.obj (Opposite.op (D.obj k)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op c.pt)) :=
  preservesColimit_coyoneda_of_isColimit κ F c hc
    (hasCardinalLT_of_finite (Arrow K) κ (Fact.out : κ.IsRegular).aleph0_le) hSources

end CategoryTheory.Limits
