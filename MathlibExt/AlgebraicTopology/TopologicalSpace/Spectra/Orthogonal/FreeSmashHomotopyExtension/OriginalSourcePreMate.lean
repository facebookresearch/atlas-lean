/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-!
# Precomposition as a mate for module internal Hom

For a commutative monoid in a symmetric monoidal closed category with equalizers and
coequalizers, the mate of tensoring with a right-module morphism is the module internal
Hom precomposition transformation. The equality uses the full tensor/internal-Hom
adjunctions and their counits.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uC vC
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.Source

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- The right-module tensor used to evaluate the original free-source adjunction and
precomposition maps. -/
local instance : MonoidalCategory (CommutativeModuleConversion.RightModule R) :=
  RightModuleFree.tensorMonoidal R

theorem originalPreMate {M M' : CommutativeModuleConversion.RightModule R} (f : M' ⟶ M) :
    conjugateEquiv (RightModuleMappingEnd.leftAdjunction R M)
        (RightModuleMappingEnd.leftAdjunction R M')
        ((tensoringLeft (CommutativeModuleConversion.RightModule R)).map f) =
      RightModuleMappingEnd.sourceNatTrans R f := by
  apply NatTrans.ext
  funext N
  apply ((RightModuleMappingEnd.leftAdjunction R M').homEquiv
    ((RightModuleMappingEnd.functor R M).obj N) N).symm.injective
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  exact (conjugateEquiv_counit (RightModuleMappingEnd.leftAdjunction R M)
    (RightModuleMappingEnd.leftAdjunction R M')
    ((tensoringLeft (CommutativeModuleConversion.RightModule R)).map f) N).trans
    (PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Ambient.sourceMapCounit
      R f N).symm



end OrthogonalIGeneratorProbe.Source
