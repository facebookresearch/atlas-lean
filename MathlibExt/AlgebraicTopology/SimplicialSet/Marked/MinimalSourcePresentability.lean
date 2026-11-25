/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Colimits
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# Original minimal sources preserve presentability

The actual minimal-marking adjunction and preservation of the original
colimits by forgetting markings transfer κ-presentability of the same
underlying simplicial source. No marked-category accessibility or model
hypothesis is needed.
-/

universe u
open CategoryTheory Limits

namespace SSet.Marked

/-- The original minimally marked source is κ-presentable whenever its same simplicial carrier is. -/
theorem min_isCardinalPresentable (X : SSet.{u}) (κ : Cardinal.{u})
    [Fact κ.IsRegular] [IsCardinalPresentable X κ] : IsCardinalPresentable (min X) κ := by
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let _ : forget.{u}.IsCardinalAccessible κ :=
    { preservesColimitOfShape J _ _ := inferInstance }
  exact minimalAdjunction.isCardinalPresentable_leftAdjoint_obj κ X

end SSet.Marked
