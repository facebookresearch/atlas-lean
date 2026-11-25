/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ColimitCriterion
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The original maximal marking preserves native small colimits

Every simplex of a presheaf colimit comes from an actual stage. In degree
one every stage edge is marked under maximal marking, so the same native
colimit point has precisely its full maximal marking. This proves
colimit preservation on the original carrier without a model structure.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Maximal marking sends each original native small colimit cocone to a genuine marked colimit cocone. -/
def maximalMapCoconeIsColimit {J : Type u} [SmallCategory J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c) : IsColimit (maximal.mapCocone c) := by
  apply isColimitOfUnderlyingMarking
  · exact hc
  · intro e _
    let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋1⦌)
    have hce := isColimitOfPreserves ev hc
    obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hce e
    exact ⟨j, b, Set.mem_univ _, hb⟩

/-- The actual maximal-marking functor preserves all original-value-universe small colimits. -/
theorem maximal_preservesColimits : PreservesColimitsOfSize.{u, u} maximal.{u} where
  preservesColimitsOfShape := by
    intro J hJ
    exact
      { preservesColimit :=
          { preserves hc := ⟨maximalMapCoconeIsColimit hc⟩ } }

end SSet.Marked
