/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation
import MathlibExt.CategoryTheory.Enriched.FreeUnitComparison
import MathlibExt.CategoryTheory.Enriched.RightModuleFreeUnit

/-!
# The original orthogonal sphere is the actual native free zero-sphere

The original zero-representable unit and the stock free-unit unitor give
an isomorphism from the actual source free unit to the regular sphere
module. The proved source/native carrier equivalence and its evaluation
comparison carry the original two-stage free adjunction to the actual
native free zero-sphere. Both full source and native maps are retained.

This is the sphere-unit case of MMSS Construction 2.1 and Theorem 2.2,
December 30, 1999 preprint, pages 9 and 63. It uses the original right
sphere modules and all native universe parameters.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit.Internal

-- Compatibility names for the canonical free-unit constructions.
export CategoryTheory.RightModuleFree
  (freeUnitRegular freeUnitRegular_hom freeUnitRegular_inv)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit.Internal

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit.Internal

-- Compatibility names for the canonical free-unit constructions.
export CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit
  (sourceFreeObjectEq sourceFreeRegularIso sourceFreeRegularIso_hom sourceFreeRegularIso_inv
    regularUnitOperatorIso regularUnitOperatorIso_hom regularUnitOperatorIso_inv)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit.Internal

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit

/-- The original continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original orthogonal index tensor structure. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indexing. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry of orthogonal indexing. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The actual Day tensor structure on the original orthogonal I-spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The representation-sphere monoid in the original Day category. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

open EnrichedFunctorCat CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open CanonicalSourceRightModuleFreeEvaluation
private abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex

/-- The original free I-space at zero with unit coefficient is the actual Day representable unit. -/
def freeUnitISpaceIso :
    Free.object (0 : OrthogonalIndex) (𝟙_ PointedCGWH.{u, v}) ≅ 𝟙_ ISpace.{u, v} :=
  Free.unitCoefficientIso (V := PointedCGWH.{u, v}) (0 : OrthogonalIndex)

/-- Every actual zero-free coefficient component is the original pointed left unitor. -/
theorem freeUnitISpaceIso_hom_component (k : OrthogonalIndex) :
    component freeUnitISpaceIso.{u, v}.hom k =
      (λ_ (OrthogonalIndex.hom.{u, v} 0 k)).hom :=
  Free.unitCoefficientIso_hom_component (0 : OrthogonalIndex) k

/-- Every inverse coefficient component uses the original inverse pointed left unitor. -/
theorem freeUnitISpaceIso_inv_component (k : OrthogonalIndex) :
    component freeUnitISpaceIso.{u, v}.inv k =
      (λ_ (OrthogonalIndex.hom.{u, v} 0 k)).inv :=
  Free.unitCoefficientIso_inv_component (0 : OrthogonalIndex) k

/-- Actual stock free maps and the original Day unitor identify the free unit with the sphere
ring. -/
abbrev freeUnitRegularIso := Internal.freeUnitRegular sphereISpace.{u, v}
  (Free.object (0 : OrthogonalIndex) (𝟙_ PointedCGWH.{u, v})) freeUnitISpaceIso

/-- The entire source free-unit forward map retains actual coefficient tensoring and Day unitor. -/
abbrev freeUnitRegularIsoHom := Internal.freeUnitRegular_hom sphereISpace.{u, v}
  (Free.object (0 : OrthogonalIndex) (𝟙_ PointedCGWH.{u, v})) freeUnitISpaceIso

/-- The entire inverse uses the original inverse Day unitor and inverse coefficient tensor map. -/
abbrev freeUnitRegularIsoInv := Internal.freeUnitRegular_inv sphereISpace.{u, v}
  (Free.object (0 : OrthogonalIndex) (𝟙_ PointedCGWH.{u, v})) freeUnitISpaceIso

/-- The actual composed source free functor sends the zero unit to the regular sphere module. -/
abbrev sourceFreeUnitRegularIso := Internal.sourceFreeRegularIso
  sphereISpace.{u, v} (0 : OrthogonalIndex) (𝟙_ PointedCGWH.{u, v}) freeUnitISpaceIso

/-- The regular sphere source reconstructs the actual native zero-free unit-coefficient diagram. -/
abbrev regularSphereNativeFreeIso :=
  Internal.regularUnitOperatorIso sphereISpace.{u, v} equivalence.{u, v}.symm
    (0 : OrthogonalIndex) (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    freeUnitISpaceIso (evaluationComparison.{u, v} 0)

/-- Every forward unit map retains its complete original source and free-comparison factors. -/
abbrev regularSphereNativeFreeIsoHom :=
  Internal.regularUnitOperatorIso_hom sphereISpace.{u, v} equivalence.{u, v}.symm
    (0 : OrthogonalIndex) (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    freeUnitISpaceIso (evaluationComparison.{u, v} 0)

/-- Every inverse unit map retains the original inverse comparison and source-unit factors. -/
abbrev regularSphereNativeFreeIsoInv :=
  Internal.regularUnitOperatorIso_inv sphereISpace.{u, v} equivalence.{u, v}.symm
    (0 : OrthogonalIndex) (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    freeUnitISpaceIso (evaluationComparison.{u, v} 0)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit
