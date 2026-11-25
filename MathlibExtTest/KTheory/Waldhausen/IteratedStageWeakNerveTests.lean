/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageWeakNerve

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.IteratedStageWeakNerve

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every finite number of original simplex directions forms the actual weak category. -/
def originalMultisimplicialCategory (r : ℕ) : StageSimplexTuple r ⥤ Cat.{v, max u v} :=
  iteratedStageWeakMultisimplicial C r

/-- Every original componentwise tuple map acts on its original nerve. -/
theorem originalMultisimplicialNerveMap {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    (iteratedStageWeakNerve C r).map α =
      CategoryTheory.nerveMap (reindexIteratedStageWeak C α) :=
  iteratedStageWeakNerve_map C α

end MathlibExtTest.IteratedStageWeakNerve
