/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneIntervalInsertion

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.StageOneIntervalInsertion

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original interval simplex acts on the original weak S-stage category. -/
def originalIntervalInsertion {a : SimplexCategoryᵒᵖ}
    (t :
        (Δ[1] : SSet.{max u v}).obj a) : CategoryTheory.Waldhausen.WeakCategory C ⥤ StageWeakCategory C a.unop.len :=
  stageOneWeakIntervalInsertion C t

/-- Original simplex operators commute with the complete interval insertion map. -/
theorem originalIntervalInsertionReindex {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b)
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    stageOneWeakIntervalInsertion C ((Δ[1] : SSet.{max u v}).map α t) =
      stageOneWeakIntervalInsertion C t ⋙ reindexStageWeak C α.unop :=
  stageOneWeakIntervalInsertion_reindex C α t

end MathlibExtTest.StageOneIntervalInsertion
