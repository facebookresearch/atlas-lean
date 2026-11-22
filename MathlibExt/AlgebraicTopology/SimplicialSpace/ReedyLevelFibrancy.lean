/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant

/-!
# Every whole original Reedy level is Kan through its actual enriched Yoneda object

The original discrete representable is cofibrant. The actual Reedy
inner mapping object is therefore Kan at a Reedy-fibrant target, and
the entire original Yoneda isomorphism transfers this to the same
original level. No pointwise-Kan-to-Reedy converse is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.ReedyModel

/-- Every actual original level of a Reedy-fibrant simplicial space is a Kan complex. -/
theorem level_kanComplex (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant W → ∀ n : ℕ, SSet.KanComplex (W.diagram.obj (op (SimplexCategory.mk n))) := by
  intro hW n
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[n] : SSet.{u}))
  have h := innerHom_kanComplex X W (isCofibrant X) hW
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[n] : SSet.{u}))) at h
  let _ : IsFibrant ((discreteSourceMapping W).obj (op (Δ[n] : SSet.{u}))) := h
  exact isFibrant_of_fibration (discreteYonedaIso W n).inv

end SimplicialSpace.ReedyModel
