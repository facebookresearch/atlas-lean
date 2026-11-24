/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageWeakDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneIntervalInsertion

/-!
# Original interval insertion into every iterated S-stage

The actual prior iterated category receives its original S₁ insertion and
literal interval pullback. The canonical degree-list successor equivalence
returns that same stage to the original iterated carrier. Exactness and
weak-map preservation are derived from the existing one-stage suppliers.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Insert the original interval S₁ stage after an actual finite prior degree list. -/
def iteratedStageIntervalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    IteratedStage C ns ⥤ IteratedStage C (a.unop.len :: ns) :=
  stageOneIntervalInsertion (IteratedStage C ns) t ⋙
    (iteratedStageConsEquivalence C a.unop.len ns).inverse

/-- This actual insertion is exact for the same original successor stage structure. -/
theorem iteratedStageIntervalInsertion_isWaldhausenExact (ns : List ℕ)
    {a : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj a) :
    (iteratedStageIntervalInsertion C ns t).IsWaldhausenExact := by
  let D := IteratedStage C ns
  let : HasZeroObject (Stage D 1) := generalStageHasZeroObject D 1
  let : WaldhausenCategoryWithoutGluing (Stage D 1) := generalStageWaldhausenCategory D 1
  let : HasZeroObject (Stage D a.unop.len) := generalStageHasZeroObject D a.unop.len
  let : WaldhausenCategoryWithoutGluing (Stage D a.unop.len) :=
    generalStageWaldhausenCategory D a.unop.len
  exact ((stageOne_general_isWaldhausenExact D).comp
    (reindexStage_general_isWaldhausenExact D (SSet.stdSimplex.objEquiv t))).comp
      (iteratedStageConsEquivalence_exact C a.unop.len ns).2

/-- The same original insertion restricts to the actual prior and successor weak categories. -/
def iteratedStageWeakIntervalInsertion (ns : List ℕ) {a : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj a) :
    WeakCategory (IteratedStage C ns) ⥤ WeakCategory (IteratedStage C (a.unop.len :: ns)) :=
  (iteratedStageIntervalInsertion_isWaldhausenExact C ns t).mapWeakCategory

end CategoryTheory.Waldhausen.SConstruction
