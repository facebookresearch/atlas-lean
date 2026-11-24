/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWeakEquivalence

/-!
# The original S1 comparison at every finite iteration

The actual canonical successor carrier and original S1 insertion and
evaluation compare the same original finite iteration with its next
S1-stage. Both directions retain their original earned exactness. This
is the categorical input of the original spectrum structure map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Original S1 insertion after any actual finite iteration. -/
def iteratedStageOne : (ns : List ℕ) → IteratedStage C ns ⥤ IteratedStage C (1 :: ns)
  | ns => stageOne (IteratedStage C ns) ⋙ (iteratedStageConsEquivalence C 1 ns).inverse

/-- Original S1 evaluation after any actual finite iteration. -/
def iteratedStageOneEval : (ns : List ℕ) → IteratedStage C (1 :: ns) ⥤ IteratedStage C ns
  | ns => (iteratedStageConsEquivalence C 1 ns).functor ⋙ stageOneEval (IteratedStage C ns)

/-- The actual original categorical S1 equivalence on every finite iteration. -/
def iteratedStageOneEquivalence (ns : List ℕ) :
    IteratedStage C ns ≌ IteratedStage C (1 :: ns) :=
  (stageOneEquivalence (IteratedStage C ns)).trans (iteratedStageConsEquivalence C 1 ns).symm

/-- The original inserted stage map preserves all original Waldhausen fields. -/
theorem iteratedStageOne_isWaldhausenExact (ns : List ℕ) :
    (iteratedStageOne C ns).IsWaldhausenExact := by
  let : HasZeroObject (Stage (IteratedStage C ns) 1) :=
    generalStageHasZeroObject (IteratedStage C ns) 1
  let : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) 1) :=
    generalStageWaldhausenCategory (IteratedStage C ns) 1
  exact (stageOne_general_isWaldhausenExact (IteratedStage C ns)).comp
    (iteratedStageConsEquivalence_exact C 1 ns).2

/-- The original evaluated stage map preserves the same original Waldhausen fields. -/
theorem iteratedStageOneEval_isWaldhausenExact (ns : List ℕ) :
    (iteratedStageOneEval C ns).IsWaldhausenExact := by
  let : HasZeroObject (Stage (IteratedStage C ns) 1) :=
    generalStageHasZeroObject (IteratedStage C ns) 1
  let : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) 1) :=
    generalStageWaldhausenCategory (IteratedStage C ns) 1
  exact (iteratedStageConsEquivalence_exact C 1 ns).1.comp
    (stageOneEval_general_isWaldhausenExact (IteratedStage C ns))

end CategoryTheory.Waldhausen.SConstruction
