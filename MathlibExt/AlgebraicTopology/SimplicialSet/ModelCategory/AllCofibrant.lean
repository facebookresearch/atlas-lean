/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Cofibrancy of simplicial sets

Every simplicial set is cofibrant in the selected Kan–Quillen model
structure. The instance is opt-in through the existing
`SSet.modelCategoryQuillen` scope.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra

namespace SSet.modelCategoryQuillen

/-- Every simplicial set is cofibrant in the selected model structure. -/
noncomputable scoped instance instIsCofibrant (X : SSet.{u}) :
    IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  exact MorphismProperty.monomorphisms.infer_property _

end SSet.modelCategoryQuillen
