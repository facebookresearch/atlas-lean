/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyFibrantDegrees

/-!
# Genuine original Reedy Hom comparison at arbitrary fibrant pointed targets

Every actual original fibrant pointed target is cofibrant in its same
opposite model. The genuine original relative-matching trivial classes
then give a Kan trivial fibration of the full original target-dependent
Hom diagrams. The same generated restriction map is retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

/-- Every same actually fibrant original pointed target is cofibrant in the actual opposite model. -/
theorem pointedTarget_op_isCofibrant (X : PointedJoyal.{u}) [IsFibrant X] : IsCofibrant (op X) := by
  exact (isCofibrant_iff_of_isInitial (terminal.from X).op (initialOpOfTerminal terminalIsTerminal)).mpr inferInstance

/-- The same actual full generated Reedy restriction map is a genuine Kan trivial fibration at every original fibrant
pointed target. -/
theorem reedyHomTransformation_trivialFibration (X : PointedJoyal.{u}) [IsFibrant X] :
    trivialFibrations SSet.{u} (reedyHomTransformation.app X) := by
  let _ : IsCofibrant (op X) := pointedTarget_op_isCofibrant X
  have h := SimplicialObject.representable_reedy_trivialFibration (op X) reversedFactorization.p
    reversedFactorization_relativeMatching_trivial
  let e := Functor.isoWhiskerLeft reversedFactorization.Z (Coyoneda.objOpOp X)
  let d := Functor.isoWhiskerLeft pointedJoyalDiagram.op (Coyoneda.objOpOp X)
  exact (trivialFibrations SSet.{u}).comp_mem _ _ ((trivialFibrations SSet.{u}).of_isIso e.inv)
    ((trivialFibrations SSet.{u}).comp_mem _ _ h ((trivialFibrations SSet.{u}).of_isIso d.hom))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
