/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import MathlibExt.AlgebraicTopology.SimplicialSet.Presentable
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# The combinatorial Kan--Quillen model structure

The selected Kan--Quillen model structure on simplicial sets is
combinatorial in every universe, using the existing boundary and horn
families as generators.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

/-- The selected Kan--Quillen model structure is combinatorial in every
universe. -/
noncomputable scoped instance instIsCombinatorialModelCategory :
    IsCombinatorialModelCategory.{u} SSet.{u} := by
  let _ : IsLocallyPresentable.{u} SSet.{u} :=
    SSet.isLocallyPresentable
  exact isCombinatorialModelCategory_of_generators I J
    (by
      rw [← cofibrations_rlp, cofibrations_eq,
        ← llp_rlp_I, rlp_llp_rlp])
    fibrations_eq.symm

end SSet.modelCategoryQuillen
