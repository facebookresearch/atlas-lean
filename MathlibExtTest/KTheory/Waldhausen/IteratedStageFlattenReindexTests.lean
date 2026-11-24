/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageFlattenReindex

/-!
# Clients for the original prefix-reindexing flatten square

Every prior tuple map, the appended identity direction and the full
original object/morphism maps are retained. The interval insertion client
uses the same complete appended functor for all prefix lengths.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.IteratedStageFlattenReindexTests

open CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The same full tuple map has the original head and appended tail in the actual Cons chart. -/
theorem originalAppendedOperator {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (z : SimplexCategoryᵒᵖ) :
    eqToHom (stageTupleSnoc_cons x a z).symm ≫
        stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z) ≫
          eqToHom (stageTupleSnoc_cons y b z) =
      stageTupleConsMap (stageTupleSnocMap α (𝟙 z)) f :=
  stageTupleSnocMap_cons α f z

/-- Every original prefix operator commutes with the original appended flattening. -/
theorem originalPrefixSquare (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b)
    (z : SimplexCategoryᵒᵖ) :
    reindexIteratedStage (IteratedStage C [z.unop.len]) α ⋙
        (iteratedStageTupleSnocFlattenEquivalence C b z).functor =
      (iteratedStageTupleSnocFlattenEquivalence C a z).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap α (𝟙 z)) :=
  iteratedStageTupleSnocFlattenEquivalence_reindex C r α z

/-- The whole original morphism maps are the same maps in the two actual chart directions. -/
theorem originalPrefixMap (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b)
    (z : SimplexCategoryᵒᵖ) {X Y : StageAtTuple (IteratedStage C [z.unop.len]) a}
    (f : X ⟶ Y) :
    HEq ((iteratedStageTupleSnocFlattenEquivalence C b z).functor.map
        ((reindexIteratedStage (IteratedStage C [z.unop.len]) α).map f))
      ((reindexIteratedStage C (stageTupleSnocMap α (𝟙 z))).map
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.map f)) :=
  iteratedStageTupleSnocFlattenEquivalence_reindex_map C r α z f

/-- The same original innermost insertion commutes with all prior tuple directions. -/
theorem originalInnermostPrefixSquare (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b)
    {z : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj z) :
    reindexIteratedStage C α ⋙ iteratedStageTupleInnermostIntervalInsertion C b t =
      iteratedStageTupleInnermostIntervalInsertion C a t ⋙
        reindexIteratedStage C (stageTupleSnocMap α (𝟙 z)) :=
  iteratedStageTupleInnermostIntervalInsertion_reindex C r α t

/-- The complete original interval insertion earns exactness through its actual two factors. -/
theorem originalInnermostExact {r : ℕ} (a : StageSimplexTuple r)
    {z : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj z) :
    (iteratedStageTupleInnermostIntervalInsertion C a t).IsWaldhausenExact :=
  iteratedStageTupleInnermostIntervalInsertion_isWaldhausenExact C a t

end MathlibExtTest.KTheory.Waldhausen.IteratedStageFlattenReindexTests

end
