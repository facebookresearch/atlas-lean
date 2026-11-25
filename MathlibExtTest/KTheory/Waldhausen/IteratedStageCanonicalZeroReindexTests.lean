/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageCanonicalZeroReindex

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace MathlibExtTest.IteratedStageCanonicalZeroReindex
open CategoryTheory.Waldhausen.SConstruction
variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The complete original tuple functor preserves the explicit constructed zero. -/
theorem originalTupleZero {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    (reindexIteratedStage C α).obj (iteratedStageCanonicalZero C (stageTupleDegrees a)) =
      iteratedStageCanonicalZero C (stageTupleDegrees b) :=
  reindexIteratedStage_canonicalZero C α

end MathlibExtTest.IteratedStageCanonicalZeroReindex
