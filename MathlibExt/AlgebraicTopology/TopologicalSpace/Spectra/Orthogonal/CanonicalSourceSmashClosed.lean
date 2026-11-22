/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Tactic.Alias
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmash
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceClosed

/-!
# Actual source Mapping_R for canonical orthogonal sphere smash

The genuine Day adjunction discharges the original tensor-preservation
families. The canonical complete sphere tensor therefore has the
same entire monoidal structure as the original relative right-module
tensor. Its right adjoint is the actual translated action equalizer.

Both original carrier-equivalence adjunctions then reconstruct that full
source functor on canonical spectra. The actual tensor, both functors,
units, counits and triangles are retained. Explicit end-projection
formulas for the source unit and counit are separate source prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

open CategoryTheory.Enriched

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed

attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory
  SphereSmashStructure.dayMonoidalCategory
  SphereSmashStructure.daySymmetricCategory
  SphereSmashStructure.sphereMonoid
  SphereSmashStructure.sphereCommutativeMonoid
  SphereSmashStructure.spaceCoequalizers
  CanonicalSourceSmash.monoidalCategory
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- The actual canonical relative-sphere tensor is closed by the complete source Mapping_R. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed CanonicalSourceSmash.Carrier.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.monoidalClosed CanonicalSourceSmash.sourceContext.{u, v}

attribute [local instance] monoidalClosed

/-- The actual whole source Mapping_R functor is restricted and reconstructed by the original E. -/
def mappingFunctor (X : CanonicalSourceSmash.Carrier.{u, v}) :
    CanonicalSourceSmash.Carrier.{u, v} ⥤ CanonicalSourceSmash.Carrier.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.mappingFunctor CanonicalSourceSmash.sourceContext.{u, v} X

/-- The actual canonical tensor adjunction keeps its complete source and both E adjunctions. -/
def adjunction : ModuleMappingR.SourceClosed.Selected.AdjunctionFamily CanonicalSourceSmash.sourceContext.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.adjunction CanonicalSourceSmash.sourceContext.{u, v}

/-- The chosen entire native internal Hom is the actual reconstructed source Mapping_R functor. -/
theorem ihom_eq (X : CanonicalSourceSmash.Carrier.{u, v}) :
    ihom X = mappingFunctor X := rfl

/-- Its entire chosen adjunction is the original source/E composite adjunction. -/
theorem ihom_adjunction_eq :
    ModuleMappingR.SourceClosed.Selected.IhomAdjunctionFormula CanonicalSourceSmash.sourceContext.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.ihomAdjunction CanonicalSourceSmash.sourceContext.{u, v}

/-- The whole original target-map equation, with complete native source/E suppliers. -/
abbrev mappingFunctorMap :=
  ModuleMappingR.SourceClosed.Primitive.mappingFunctor_map (E := CanonicalSourceSmash.sourceEquivalence.{u, v})
    (R := (SphereSmash.sourceData.{u, v}).mappingFunctor)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed
attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- Every actual source-smash left tensor preserves all used small colimits. -/
theorem tensorLeft_preservesColimits :
    ModuleMappingR.SourceClosed.Selected.TensorLeftPreservesFamily CanonicalSourceSmash.sourceContext.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.tensorLeftPreserves CanonicalSourceSmash.sourceContext.{u, v}

/-- The original source braid gives preservation by the actual tensor in the other orientation. -/
theorem tensorRight_preservesColimits :
    ModuleMappingR.SourceClosed.Selected.TensorRightPreservesFamily CanonicalSourceSmash.sourceContext.{u, v} :=
  ModuleMappingR.SourceClosed.Selected.tensorRightPreserves CanonicalSourceSmash.sourceContext.{u, v}

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed

/-!
Compatibility for the original public orthogonal source APIs.
-/

noncomputable section

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.mappingFunctor :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.mappingFunctor

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.mappingFunctor_map :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.mappingFunctor_map

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.adjunction :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.adjunction

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12"), instance_reducible]
alias Primitive.monoidalClosed :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.monoidalClosed

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.monoidalClosed_ihom :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.monoidalClosed_ihom

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.monoidalClosed_adjunction :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.monoidalClosed_adjunction

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.homEquiv_apply :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.homEquiv_apply

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.homEquiv_symm_apply :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.homEquiv_symm_apply

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.unit_app :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.unit_app

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.counit_app :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.counit_app

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.left_triangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.left_triangle

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.right_triangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.right_triangle

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.moduleMonoidal_eq :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.moduleMonoidal_eq

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.adjunctionFromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.adjunctionFromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12"), instance_reducible]
alias Internal.fromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.fromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.AdjunctionFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.AdjunctionFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.completeAdjunctionFromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.completeAdjunctionFromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.IhomAdjunctionFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.IhomAdjunctionFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.ihomAdjunctionFromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.ihomAdjunctionFromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.TensorLeftPreservesFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.TensorLeftPreservesFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.tensorLeftPreservesFromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.tensorLeftPreservesFromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.TensorRightPreservesFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.TensorRightPreservesFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Internal.tensorRightPreservesFromSource :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal.tensorRightPreservesFromSource

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.ClosedStructureType :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.ClosedStructureType

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12"), instance_reducible]
alias Selected.monoidalClosed :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.monoidalClosed

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.mappingFunctor :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.mappingFunctor

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.AdjunctionFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.AdjunctionFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.adjunction :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.adjunction

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.ihom :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.ihom

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.IhomAdjunctionFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.IhomAdjunctionFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.ihomAdjunction :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.ihomAdjunction

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.TensorLeftPreservesFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.TensorLeftPreservesFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.tensorLeftPreserves :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.tensorLeftPreserves

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.TensorRightPreservesFamily :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.TensorRightPreservesFamily

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.tensorRightPreserves :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.tensorRightPreserves

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.TransposeOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.TransposeOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.transposeOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.transposeOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.UntransposeOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.UntransposeOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.untransposeOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.untransposeOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.UnitOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.UnitOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.unitOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.unitOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.CounitOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.CounitOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.counitOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.counitOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.LeftTriangleFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.LeftTriangleFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.leftTriangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.leftTriangle

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.RightTriangleFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.RightTriangleFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Primitive.rightTriangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive.rightTriangle

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.TransposeOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.TransposeOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.transposeOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.transposeOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.UntransposeOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.UntransposeOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.untransposeOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.untransposeOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.UnitOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.UnitOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.unitOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.unitOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.CounitOriginalFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.CounitOriginalFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.counitOriginal :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.counitOriginal

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.LeftTriangleFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.LeftTriangleFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.leftTriangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.leftTriangle

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.RightTriangleFormula :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.RightTriangleFormula

/-- Deprecated compatibility name for the canonical generic source API. -/
@[deprecated (since := "2026-11-12")]
alias Selected.rightTriangle :=
  CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected.rightTriangle

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed
