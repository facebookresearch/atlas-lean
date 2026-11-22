/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Selected functorial factorizations for simplicial sets

The boundary and horn small-object arguments already provide chosen
functorial data. This file exposes that same data under the two selected
Kan--Quillen model-category class pairs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

/-- The selected cofibration/trivial-fibration factorization is the existing
boundary small-object factorization. -/
noncomputable scoped instance
    instHasFunctorialFactorizationCofibrationsTrivialFibrations :
    HasFunctorialFactorization (cofibrations SSet.{u})
      (trivialFibrations SSet.{u}) := by
  refine ⟨⟨?_⟩⟩
  rw [← cofibrations_rlp]
  rw [cofibrations_eq]
  exact monoFunctorialFactorizationData

/-- The selected trivial-cofibration/fibration factorization is the existing
horn small-object factorization. -/
noncomputable scoped instance
    instHasFunctorialFactorizationTrivialCofibrationsFibrations :
    HasFunctorialFactorization (trivialCofibrations SSet.{u})
      (fibrations SSet.{u}) := by
  refine ⟨⟨?_⟩⟩
  rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
  exact anodyneFunctorialFactorizationData

end SSet.modelCategoryQuillen
