/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageInnermostInsertion

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace MathlibExtTest.IteratedStageInnermostInsertion
open CategoryTheory.Waldhausen.SConstruction
variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every finite original prior iteration has the actual innermost interval insertion. -/
def originalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    IteratedStage C ns ⥤ IteratedStage C (ns ++ [a.unop.len]) :=
  iteratedStageInnermostIntervalInsertion C ns t

/-- Every original prior reindex operator commutes with the actual unflattened original action. -/
theorem originalPriorReindex {r : ℕ} {b d : StageSimplexTuple r} (α : b ⟶ d)
    {a : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj a) :
    reindexIteratedStage C α ⋙ unflattenedInnermostIntervalInsertion C (stageTupleDegrees d) t =
      unflattenedInnermostIntervalInsertion C (stageTupleDegrees b) t ⋙
        reindexIteratedStage (IteratedStage C [a.unop.len]) α :=
  unflattenedInnermostIntervalInsertion_reindex C α t

end MathlibExtTest.IteratedStageInnermostInsertion
