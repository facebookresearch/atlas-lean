/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingComponentEdges
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingStrictNaturality

/-!
# Actual component comparison of original coherent mapping spaces

The genuine whole original Hom comparison induces a bijection on
components. Its inverse is derived from the actual original vertex and
edge readbacks, retaining the supplied individual source and target
objects. The component comparison follows the same strict enriched map.
This does not infer a higher mapping weak equivalence from components.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingComponents
open SimplicialEnrichment HomSimplexEndpoints HomMapping MappingComponentEdges
variable {C D : Carrier.{u}} (x y : C)

/-- The actual component readback of a supplied original coherent right-mapping simplex. -/
def read : SSet.π₀ (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) →
    SSet.π₀ (x ⟶[SSet.{u}] y) :=
  SSet.π₀.lift (fun σ => SSet.π₀.mk (MappingVertices.read x y σ))
    (fun {σ τ} e => read_component_eq x y (σ := σ) (τ := τ) e)

/-- The actual component readback is the same original Hom-vertex class, with no quotient of the supplied
  original objects. -/
theorem read_mk (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    read x y (SSet.π₀.mk σ) = SSet.π₀.mk (MappingVertices.read x y σ) := rfl

/-- The actual original Hom component is recovered after the genuine coherent comparison. -/
theorem read_map (c : SSet.π₀ (x ⟶[SSet.{u}] y)) : read x y (SSet.mapπ₀ (HomMapping.map x y) c) = c := by
  obtain ⟨τ, rfl⟩ := SSet.π₀.mk_surjective c
  exact congrArg SSet.π₀.mk (MappingVertices.read_map x y τ)

/-- The entire actual right-mapping component is recovered after its original Hom readback. -/
theorem map_read (c : SSet.π₀ (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y))) :
    SSet.mapπ₀ (HomMapping.map x y) (read x y c) = c := by
  obtain ⟨σ, rfl⟩ := SSet.π₀.mk_surjective c
  exact congrArg SSet.π₀.mk (MappingVertices.map_read x y σ)

/-- The actual component equivalence induced by the original whole Hom-to-right-mapping-space map at the
  same individual objects. -/
def equiv : SSet.π₀ (x ⟶[SSet.{u}] y) ≃
    SSet.π₀ (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) where
  toFun := SSet.mapπ₀ (HomMapping.map x y)
  invFun := read x y
  left_inv := read_map x y
  right_inv := map_read x y

/-- The whole forward component equivalence is precisely the component map of the actual original Hom comparison. -/
theorem equiv_apply (c : SSet.π₀ (x ⟶[SSet.{u}] y)) : equiv x y c = SSet.mapπ₀ (HomMapping.map x y) c := rfl

/-- Each represented original Hom vertex has its literal actual component image. -/
theorem equiv_mk (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    equiv x y (SSet.π₀.mk τ) = SSet.π₀.mk ((HomMapping.map x y).app (op ⦋0⦌) τ) := rfl

/-- The actual original Hom and right-mapping component comparisons follow the same supplied strict enriched functor. -/
theorem naturality (F : C ⟶ D) (c : SSet.π₀ (x ⟶[SSet.{u}] y)) :
    equiv (F.obj x) (F.obj y) (SSet.mapπ₀ (F.map x y) c) =
      SSet.mapπ₀ (MappingStrictNaturality.map F x y) (equiv x y c) := by
  have h := congrArg (fun f => SSet.mapπ₀ f c) (MappingStrictNaturality.homComparison_naturality F x y)
  exact (SSet.mapπ₀_comp_apply _ _ c).symm.trans (h.symm.trans (SSet.mapπ₀_comp_apply _ _ c))

end CategoryTheory.CoherentRealization.MappingComponents
