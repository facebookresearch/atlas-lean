/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FixedDerivedObstructionMaps

/-!
# Full equivariant POT inputs and their actual fixed derived maps

The original map stays in the native derived category. Its equivariance
uses the actual source action and source-normalized cotangent action.
The fixed theory below uses precisely the already computed restriction
of that original map. Its homology and amplitude properties are separate
proof conclusions about that map.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantPerfectObstructionTheoryModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonObj
open AlgebraicWeightBundleModels DerivedTwoTermObstructionModels
open EquivariantDerivedObstructionModels FixedDerivedObstructionMaps TorusFixedSchemeModels
open GlobalPerfectObstructionTheory GlobalPOTVirtualClass
open GlobalObstructionMorphisms
attribute [local instance] HasDerivedCategory.standard

/-- An equivariant POT retains full equivariance of the original derived phi. -/
structure EquivariantPOT (X : Over base) [ModObj Gm X] where
  terms : EquivariantObstructionTerms X
  cotangent : CotangentActionData X terms.obstruction.cotangent
  source : SourceActionData terms cotangent
  equivariant : IsEquivariantObstruction terms cotangent source

variable {X F : Over base} [ModObj Gm X] (E : EquivariantPOT X)
  (i : F ⟶ X) (hi : FixedPoint Gm X i) (W : FixedTerms E.terms i hi)
  (B : FixedBundleData E.terms i hi W) (P : FixedObstructionData E.terms i hi W B)

/-- These are conclusions about the fixed source and its specific induced map. -/
def FixedTheoryProperties : Prop :=
  FixedPOTProperties E.terms i hi W P ∧
    LocallyPerfectAmplitude (sourceComplex (fixedModel E.terms i hi W B))

/-- The fixed derived POT has no independently assigned phi. -/
def fixedDerivedPOT (h : FixedTheoryProperties E i hi W B P) : DerivedPOT F where
  model := fixedModel E.terms i hi W B
  cotangent := P.cotangent
  map := P.map
  amplitude := h.2
  h0 := h.1.1
  hMinus := h.1.2

end MathlibExt.AlgebraicGeometry.EquivariantPerfectObstructionTheoryModels
