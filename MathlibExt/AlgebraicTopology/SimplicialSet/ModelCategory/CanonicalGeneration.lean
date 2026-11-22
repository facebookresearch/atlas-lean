/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# The original Kan--Quillen generating families

The existing Kan--Quillen model has its actual boundary and horn
generators at the original countable cardinal. This data supplies the
existing projective diagram constructor without any diagram-model input.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe v
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- The actual boundary and horn families generate the existing Kan--Quillen model. -/
def canonicalGenerationData : CofibrantGenerationData SSet.{v} Cardinal.aleph0.{v} where
  I := I
  J := J
  I_smallObject := inferInstance
  J_smallObject := inferInstance
  I_rlp := by
    rw [← SSet.rlp_monomorphisms, ← cofibrations_eq, cofibrations_rlp]
  J_rlp := fibrations_eq.symm

/-- The entire generating cofibration family is the original boundary family. -/
theorem canonicalGenerationData_I : canonicalGenerationData.{v}.I = I.{v} := rfl

/-- The entire generating acyclic cofibration family is the original horn family. -/
theorem canonicalGenerationData_J : canonicalGenerationData.{v}.J = J.{v} := rfl

end SSet.modelCategoryQuillen
