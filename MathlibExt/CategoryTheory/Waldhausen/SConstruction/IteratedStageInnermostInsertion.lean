/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageIntervalInsertion

/-!
# The original interval action in the innermost iterated S-direction

The original S₁ interval insertion acts on the input category. Applying
the existing exact iterated S-functor retains strict naturality in every
prior S-direction. The original recursive stage-record equality flattens
the result into the original concatenated degree list. No tuple operator
is required to send its chosen zero to another chosen zero literally.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original interval insertion, starting from the actual input category rather than its nil
carrier. -/
def baseIteratedStageIntervalInsertion {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) : C ⥤ IteratedStage C [a.unop.len] :=
  (iteratedStageNilEquivalence C).inverse ⋙ iteratedStageIntervalInsertion C [] t

/-- Every preservation field of the actual base interval insertion is earned from its original
factors. -/
theorem baseIteratedStageIntervalInsertion_isWaldhausenExact {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    (baseIteratedStageIntervalInsertion C t).IsWaldhausenExact :=
  (iteratedStageNilEquivalence_exact C).2.comp
    (iteratedStageIntervalInsertion_isWaldhausenExact C [] t)

/-- The original interval insertion acts under every finite prior S-iteration. -/
def unflattenedInnermostIntervalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    IteratedStage C ns ⥤ IteratedStage (IteratedStage C [a.unop.len]) ns :=
  mapIteratedStage (baseIteratedStageIntervalInsertion_isWaldhausenExact C t) ns

/-- The complete original innermost insertion lands in the original appended degree list. -/
def iteratedStageInnermostIntervalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    IteratedStage C ns ⥤ IteratedStage C (ns ++ [a.unop.len]) :=
  unflattenedInnermostIntervalInsertion C ns t ⋙
    (iteratedStageFlattenEquivalence C ns [a.unop.len]).functor

/-- Innermost insertion is exact for the same original recursive stage structures. -/
theorem iteratedStageInnermostIntervalInsertion_isWaldhausenExact (ns : List ℕ)
    {a : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj a) :
    (iteratedStageInnermostIntervalInsertion C ns t).IsWaldhausenExact :=
  (mapIteratedStage_isWaldhausenExact
    (baseIteratedStageIntervalInsertion_isWaldhausenExact C t) ns).comp
      (iteratedStageFlattenEquivalence_exact C ns [a.unop.len]).1

/-- Before flattening, every prior original simplex direction commutes strictly with interval
insertion. -/
theorem unflattenedInnermostIntervalInsertion_reindex {r : ℕ}
    {b d : StageSimplexTuple r} (α : b ⟶ d) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    reindexIteratedStage C α ⋙ unflattenedInnermostIntervalInsertion C (stageTupleDegrees d) t =
      unflattenedInnermostIntervalInsertion C (stageTupleDegrees b) t ⋙
        reindexIteratedStage (IteratedStage C [a.unop.len]) α :=
  mapIteratedStage_reindex (baseIteratedStageIntervalInsertion_isWaldhausenExact C t) r α

/-- The same earned innermost insertion retains the original weak-category restriction. -/
def iteratedStageWeakInnermostIntervalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    CategoryTheory.Waldhausen.WeakCategory (IteratedStage C ns) ⥤
      CategoryTheory.Waldhausen.WeakCategory (IteratedStage C (ns ++ [a.unop.len])) :=
  (iteratedStageInnermostIntervalInsertion_isWaldhausenExact C ns t).mapWeakCategory

/-- The original complete innermost action keeps the actual source-functor map followed by literal
flattening. -/
theorem iteratedStageInnermostIntervalInsertion_obj (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) (X : IteratedStage C ns) :
    (iteratedStageInnermostIntervalInsertion C ns t).obj X =
      (iteratedStageFlattenEquivalence C ns [a.unop.len]).functor.obj
        ((mapIteratedStage (baseIteratedStageIntervalInsertion_isWaldhausenExact C t) ns).obj X) :=
          rfl

end CategoryTheory.Waldhausen.SConstruction
