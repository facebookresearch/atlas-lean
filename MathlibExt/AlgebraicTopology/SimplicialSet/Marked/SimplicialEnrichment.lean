/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalMappingComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The native simplicial enrichment of marked simplicial sets

The Hom object is the original maximal-parameter mapping complex. Its
composition pairs two entire marked prisms with the same original
parameter; its unit is the actual source projection. Ordinary marked
maps are precisely the zero simplices, with both composition directions
preserved. No fibrancy or model-category premise is used.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- An original marked map gives its constant whole parameter prism. -/
def maxMappingPoint {X Y : Marked.{u}} (f : X ⟶ Y) :
    𝟙_ SSet.{u} ⟶ mappingComplex .maximal X Y where
  app n := ↾fun _ => prodSnd (max (SSet.stdSimplex.obj n.unop)) X ≫ f
  naturality n m a := by
    ext z
    apply Hom.ext
    rfl

/-- The enriched identity is the same original source projection in every degree. -/
def maxMappingIdentity (X : Marked.{u}) : 𝟙_ SSet.{u} ⟶ mappingComplex .maximal X X :=
  maxMappingPoint (𝟙 X)

/-- Enriched composition keeps the first prism followed by the second prism. -/
def maxMappingCompose (X Y Z : Marked.{u}) :
    mappingComplex .maximal X Y ⊗ mappingComplex .maximal Y Z ⟶
      mappingComplex .maximal X Z :=
  (β_ (mappingComplex .maximal X Y) (mappingComplex .maximal Y Z)).hom ≫
    maxMappingComposition X Y Z

/-- The genuine maximal marked mapping complexes form a simplicial enrichment. -/
@[instance_reducible]
def markedSimplicialEnrichment : EnrichedCategory SSet.{u} Marked.{u} where
  Hom X Y := mappingComplex .maximal X Y
  id := maxMappingIdentity
  comp := maxMappingCompose
  id_comp X Y := by
    ext n f
    apply Hom.ext
    rfl
  comp_id X Y := by
    ext n f
    apply Hom.ext
    rfl
  assoc W X Y Z := by
    ext n fg
    apply Hom.ext
    rfl

/-- A constant marked prism retains its original map under zero-simplex evaluation. -/
theorem maxMappingPoint_zero {X Y : Marked.{u}} (f : X ⟶ Y) :
    mappingComplexZeroEquiv .maximal X Y
      (SSet.unitHomEquiv (mappingComplex .maximal X Y) (maxMappingPoint f)) = f := by
  change (zeroParameterUnitIso .maximal X).inv ≫
    ((zeroParameterUnitIso .maximal X).hom ≫ f) = f
  exact (zeroParameterUnitIso .maximal X).inv_hom_id_assoc f

/-- Ordinary marked maps identify with the actual unit-shaped enriched maps. -/
def maxMappingPointEquiv (X Y : Marked.{u}) :
    (X ⟶ Y) ≃ (𝟙_ SSet.{u} ⟶ mappingComplex .maximal X Y) where
  toFun := maxMappingPoint
  invFun g := mappingComplexZeroEquiv .maximal X Y (SSet.unitHomEquiv _ g)
  left_inv := maxMappingPoint_zero
  right_inv g := by
    apply (SSet.unitHomEquiv _).injective
    apply (mappingComplexZeroEquiv .maximal X Y).injective
    exact maxMappingPoint_zero _

/-- The ordinary category and the native simplicial enrichment have the same original maps. -/
@[instance_reducible]
def markedSimplicialCategory : EnrichedOrdinaryCategory SSet.{u} Marked.{u} where
  toEnrichedCategory := markedSimplicialEnrichment
  homEquiv := maxMappingPointEquiv _ _
  homEquiv_id X := rfl
  homEquiv_comp f g := by
    ext n z
    apply Hom.ext
    rfl

/-- Each enriched composite reads exactly the whole original marked parameter pairing. -/
theorem maxMappingCompose_app (X Y Z : Marked.{u}) (n : ℕ)
    (f : (mappingComplex .maximal X Y) _⦋n⦌) (g : (mappingComplex .maximal Y Z) _⦋n⦌) :
    (maxMappingCompose X Y Z).app (op ⦋n⦌) (f, g) =
      prodLift (prodFst (max (Δ[n] : SSet.{u})) X) f ≫ g := rfl

end SSet.Marked
