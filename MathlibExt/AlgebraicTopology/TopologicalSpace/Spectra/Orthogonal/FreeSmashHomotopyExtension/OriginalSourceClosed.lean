/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Closed structure of primitive right-module tensor

For a commutative monoid in a symmetric closed category with equalizers and coequalizers,
supplies the closed structure on the primitive right-module tensor. Retains the right-module
construction and its adjunctions.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport
universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- The closed right-module tensor whose internal Hom is the original module mapping-end functor
and adjunction. -/
@[instance_reducible]
def sourceClosed :
    letI := RightModuleFree.tensorMonoidal R
    MonoidalClosed (CommutativeModuleConversion.RightModule R) := by
  let := RightModuleFree.tensorMonoidal R
  exact { closed M := {
    rightAdj := RightModuleMappingEnd.functor R M
    adj := RightModuleMappingEnd.leftAdjunction R M } }




end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport
