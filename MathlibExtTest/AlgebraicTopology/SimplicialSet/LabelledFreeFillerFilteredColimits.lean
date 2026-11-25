/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerFilteredColimits

/-!
# Canonical filtered-colimit comparison and its labelled restrictions
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.LabelledFreeFillerFilteredColimits

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)
variable {J : Type u} [SmallCategory J] (F : J ⥤ SSet.{u})

/-- The actual canonical comparison is invertible and has its original stage equations. -/
theorem comparison [∀ s, Mono (j s)] [∀ s, IsFinitelyPresentable.{u} (K s)]
    [IsFiltered J] :
    IsIso (colimit.post F (SSet.labelledFreeFiller j)) ∧
      ∀ k, colimit.ι (F ⋙ SSet.labelledFreeFiller j) k ≫
        colimit.post F (SSet.labelledFreeFiller j) =
          (SSet.labelledFreeFiller j).map (colimit.ι F k) := by
  exact ⟨inferInstance, fun k => colimit.ι_post F (SSet.labelledFreeFiller j) k⟩

/-- Old simplices pass through the original natural unit and colimit inclusion. -/
theorem unit_restriction (k : J) :
    (SSet.labelledFreeFiller.unit j).app (F.obj k) ≫
      colimit.ι (F ⋙ SSet.labelledFreeFiller j) k ≫
        colimit.post F (SSet.labelledFreeFiller j) =
          colimit.ι F k ≫ (SSet.labelledFreeFiller.unit j).app (colimit F) := by
  rw [colimit.ι_post]
  exact ((SSet.labelledFreeFiller.unit j).naturality (colimit.ι F k)).symm

/-- Every labelled cell retains its full attaching map under the actual comparison. -/
theorem cell_restriction (k : J) (s : I) (a : K s ⟶ F.obj k) :
    SSet.labelledFreeFiller.cell j s a ≫
      colimit.ι (F ⋙ SSet.labelledFreeFiller j) k ≫
        colimit.post F (SSet.labelledFreeFiller j) =
          SSet.labelledFreeFiller.cell j s (a ≫ colimit.ι F k) := by
  rw [colimit.ι_post]
  exact SSet.labelledFreeFiller.cell_naturality j (colimit.ι F k) s a

/-- The same restriction is literal on every simplex of every target cell. -/
theorem cell_simplex_restriction (k : J) (s : I) (a : K s ⟶ F.obj k)
    (n : ℕ) (d : D s _⦋n⦌) :
    (colimit.post F (SSet.labelledFreeFiller j)).app (op ⦋n⦌)
      ((colimit.ι (F ⋙ SSet.labelledFreeFiller j) k).app (op ⦋n⦌)
        ((SSet.labelledFreeFiller.cell j s a).app (op ⦋n⦌) d)) =
          (SSet.labelledFreeFiller.cell j s (a ≫ colimit.ι F k)).app (op ⦋n⦌) d := by
  have h := congrArg
    (fun m : D s ⟶ (SSet.labelledFreeFiller j).obj (colimit F) => m.app (op ⦋n⦌))
    (cell_restriction j F k s a)
  exact ConcreteCategory.congr_hom h d

end MathlibExtTest.AlgebraicTopology.SimplicialSet.LabelledFreeFillerFilteredColimits
