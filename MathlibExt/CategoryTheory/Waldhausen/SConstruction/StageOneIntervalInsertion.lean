/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWeakEquivalence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Original interval simplices insert the actual S1 stage

An original degree-n interval simplex is a monotone map [n]→[1]. Pulling
back the original S1 insertion along that same map gives an actual S_n
stage. Every simplex operator is literal interval precomposition and
original stage reindexing. This is the concrete simplicial input to the
original suspension construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original interval simplex supplies its literal S1 pullback stage functor. -/
def stageOneIntervalInsertion {a : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj a) :
    C ⥤ Stage C a.unop.len :=
  stageOne C ⋙ reindexStage (C := C) (SSet.stdSimplex.objEquiv t)

/-- The actual original interval simplex acts on the same weak stage objects and morphisms. -/
def stageOneWeakIntervalInsertion {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) : WeakCategory C ⥤ StageWeakCategory C a.unop.len :=
  stageOneGeneralWeak C ⋙ reindexStageWeak C (SSet.stdSimplex.objEquiv t)

set_option linter.checkUnivs false in
/-- Every original interval simplex operator is the original ordinal composition. -/
theorem intervalSimplexOperator {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b)
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    SSet.stdSimplex.objEquiv ((Δ[1] : SSet.{max u v}).map α t) =
      α.unop ≫ SSet.stdSimplex.objEquiv t := rfl

/-- Original interval pullback and stage pullback commute with every original simplex operator. -/
theorem stageOneIntervalInsertion_reindex {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b)
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    stageOneIntervalInsertion C ((Δ[1] : SSet.{max u v}).map α t) =
      stageOneIntervalInsertion C t ⋙ reindexStage (C := C) α.unop := by
  unfold stageOneIntervalInsertion
  rw [intervalSimplexOperator.{u,v} α t, reindexStage_comp]
  rfl

/-- The same whole simplex-operator equality retains the original weak-category map. -/
theorem stageOneWeakIntervalInsertion_reindex {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b)
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    stageOneWeakIntervalInsertion C ((Δ[1] : SSet.{max u v}).map α t) =
      stageOneWeakIntervalInsertion C t ⋙ reindexStageWeak C α.unop := by
  unfold stageOneWeakIntervalInsertion
  rw [intervalSimplexOperator.{u,v} α t, reindexStageWeak_comp]
  rfl

end CategoryTheory.Waldhausen.SConstruction
