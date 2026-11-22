/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientPointEquivalence
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# The actual marked coefficient model from the original point slice

The maximally marked original zero-simplex is terminal. The canonical
slice equivalence therefore transports the proved Cartesian marked
model over that point to the unchanged marked coefficient carrier.
Its forward functor keeps the whole original marked object and map;
no coefficient model or equivalence outcome is supplied as input.
This named model is activated locally only.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The original marked coefficient model is the genuine transported point-slice model, with no new global instance. -/
@[instance_reducible]
def coefficientMarkedModelCategory : ModelCategory Marked.{u} := by
  let _ := markedCofibrationStructure (max (Δ[0] : SSet.{u}))
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedWeakStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedModelCategory (Δ[0] : SSet.{u})
  let _ : CategoryWithCofibrations Marked.{u} :=
    ⟨(cofibrations (Over (max (Δ[0] : SSet.{u})))).inverseImage coefficientPointEquivalence.functor⟩
  let _ : CategoryWithFibrations Marked.{u} :=
    ⟨(fibrations (Over (max (Δ[0] : SSet.{u})))).inverseImage coefficientPointEquivalence.functor⟩
  let _ : CategoryWithWeakEquivalences Marked.{u} :=
    ⟨(weakEquivalences (Over (max (Δ[0] : SSet.{u})))).inverseImage coefficientPointEquivalence.functor⟩
  exact ModelCategory.transport coefficientPointEquivalence rfl rfl rfl

end SSet.Marked
