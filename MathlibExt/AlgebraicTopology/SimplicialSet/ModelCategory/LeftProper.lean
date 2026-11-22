/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCobaseChange

/-!
# Left properness of the selected model structure on simplicial sets

The selected Kan--Quillen model structure is left proper in every universe.
The instance is opt-in through the existing `SSet.modelCategoryQuillen`
scope and directly wraps cobase stability of realization weak equivalences
against simplicial monomorphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace SSet.modelCategoryQuillen

open scoped SSet.modelCategoryQuillen in
/-- The selected Kan--Quillen model structure on simplicial sets is left
proper in every universe. -/
noncomputable scoped instance instIsLeftProper :
    IsLeftProper SSet.{u} where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    change SSet.realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u})
    infer_instance

end SSet.modelCategoryQuillen
