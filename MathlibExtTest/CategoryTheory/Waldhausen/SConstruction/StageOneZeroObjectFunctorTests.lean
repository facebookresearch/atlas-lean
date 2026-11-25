/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneZeroObjectFunctor

/-!
# Original S1 interval functor clients

Every client takes an arbitrary original exact functor, with four independent
object and morphism universes, and retains the complete original stage and
weak-chain carriers.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject

universe uC vC uD vD

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneZeroObjectFunctorTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The whole original S1 functor square is earned for an arbitrary exact functor. -/
theorem originalStageOneSquare :
    stageOne C ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapStage 1 =
      hF.zeroObjectReplacement ⋙ stageOne D :=
  stageOneZeroObjectReplacement_naturality hF

/-- The entire original interval square keeps its original ordinal parameter. -/
theorem originalIntervalSquare {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOne C ⋙ reindexStage (C := C) t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStage a.len =
      hF.zeroObjectReplacement ⋙ stageOne D ⋙ reindexStage (C := D) t :=
  stageOneIntervalZeroObjectReplacement_naturality hF t

/-- The same stage square acts on every original weak map. -/
theorem originalWeakStageOneSquare :
    stageOneGeneralWeak C ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak 1 =
      hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory ⋙ stageOneGeneralWeak D :=
  stageOneWeakZeroObjectReplacement_naturality hF

/-- The same original weak interval square retains its entire weak map family. -/
theorem originalWeakIntervalSquare {a : SimplexCategory} (t : a ⟶ ⦋1⦌) :
    stageOneGeneralWeak C ⋙ reindexStageWeak C t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak a.len =
      hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory ⋙
        stageOneGeneralWeak D ⋙ reindexStageWeak D t :=
  stageOneWeakIntervalZeroObjectReplacement_naturality hF t

/-- Every whole original weak chain, in every length, has the same source-first square. -/
theorem originalWholeChain {a : SimplexCategory} (t : a ⟶ ⦋1⦌)
    {n : ℕ} (q : ComposableArrows (CategoryTheory.Waldhausen.WeakCategory C) n) :
    q ⋙ stageOneGeneralWeak C ⋙ reindexStageWeak C t ⋙
        hF.zeroObjectReplacement_isWaldhausenExact.mapStageWeak a.len =
      (q ⋙ hF.zeroObjectReplacement_isWaldhausenExact.mapWeakCategory) ⋙
        stageOneGeneralWeak D ⋙ reindexStageWeak D t :=
  stageOneWeakIntervalZeroObjectReplacement_chain hF t q

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneZeroObjectFunctorTests

end
