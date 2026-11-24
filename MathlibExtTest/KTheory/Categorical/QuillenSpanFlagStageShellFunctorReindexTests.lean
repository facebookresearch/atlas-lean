/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import
  MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorReindex

/-!
# Strict outer-reindexing tests for Stage-shell Quillen simplices

These tests pin the two reindex functors, their strict coherence with the
Stage-shell simplex functor, identity and composition, and the collapsing
degree-one degeneracy.  They make no lift-category, contractibility, nerve,
realization, or Q/S comparison claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenSpanFlagStageShellFunctorReindexTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSpanFlagStageShellFunctorReindexTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example {a b : SimplexCategory} (α : a ⟶ b) :
    StageWeakCategory C (edgewiseQ.obj b).len ⥤
      StageWeakCategory C (edgewiseQ.obj a).len :=
  edgewiseStageWeakReindex α

example {a b : SimplexCategory} (α : a ⟶ b) :
    ComposableArrows (QuillenQ C) b.len ⥤
      ComposableArrows (QuillenQ C) a.len :=
  edgewiseQuillenSimplexReindex α

example {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
        edgewiseStageQuillenSimplexFunctor C a =
      edgewiseStageQuillenSimplexFunctor C b ⋙
        edgewiseQuillenSimplexReindex (C := C) α :=
  edgewiseStageQuillenSimplexFunctor_reindex α

example (a : SimplexCategory) :
    edgewiseQuillenSimplexReindex (C := C) (𝟙 a) = 𝟭 _ :=
  edgewiseQuillenSimplexReindex_id a

example {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    edgewiseQuillenSimplexReindex (C := C) (α ≫ β) =
      edgewiseQuillenSimplexReindex (C := C) β ⋙
        edgewiseQuillenSimplexReindex (C := C) α :=
  edgewiseQuillenSimplexReindex_comp α β

/-- The collapsing degeneracy sends the only degree-one arrow to the
normalized repeated shell, hence to the identity. -/
example (A : StageWeakCategory C (edgewiseQ.obj ⦋0⦌).len) :
    ((edgewiseQuillenSimplexReindex (C := C) (σ (0 : Fin 1))).obj
      ((edgewiseStageQuillenSimplexFunctor C ⦋0⦌).obj A)).map
        (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) = 𝟙 _ := by
  change (edgewiseStageQuillenSimplex A.obj).map
      (homOfLE (show (0 : Fin 1) ≤ 0 by decide)) = 𝟙 _
  rw [edgewiseStageQuillenSimplex_map_homOfLE,
    edgewiseStageShellClassNormalized_refl]
  change 𝟙 (⟨edgewiseStageVertex A.obj 0⟩ : QuillenQ C) = 𝟙 _
  rfl

end QuillenSpanFlagStageShellFunctorReindexTests
end MathlibExtTest.KTheory.Categorical

end
