/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageOneEquivalence

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.IteratedStageOneEquivalence

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original finite iteration retains its actual S1 categorical comparison. -/
def originalIteratedDegreeOne (ns : List ℕ) :
    IteratedStage C ns ≌ IteratedStage C (1 :: ns) := iteratedStageOneEquivalence C ns

/-- Original S1 insertion remains exact after arbitrary finite iteration. -/
theorem originalIteratedDegreeOneExact (ns : List ℕ) :
    (iteratedStageOne C ns).IsWaldhausenExact := iteratedStageOne_isWaldhausenExact C ns

end MathlibExtTest.IteratedStageOneEquivalence
