/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitDetection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingCompositionNaturality

/-!
# The whole identity law of the native marked colimit action

The original value injections detect entire maximal parameter prisms.
Their full action equations therefore transport the original enriched
identity law to the actual colimit, without reducing it to vertices.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits MonoidalCategory

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- The descended actual marked action preserves the whole original enriched identity. -/
theorem fullMap_id (x : C) [HasColimit (evaluated K x)] :
    eId SSet.{u} x ≫ maxCurry (action K x x) = maxMappingIdentity (colimit (evaluated K x)) := by
  apply sourceMap_hom_ext K x (𝟙_ SSet.{u}) (colimit (evaluated K x))
  intro j
  let p : (K.obj j).obj x ⟶ colimit (evaluated K x) := colimit.ι (evaluated K x) j
  have h := injection_fullMap K x x j
  have hi : eId SSet.{u} x ≫ (K.obj j).map x x = maxMappingIdentity ((K.obj j).obj x) :=
    (K.obj j).map_id x
  calc
    (eId SSet.{u} x ≫ maxCurry (action K x x)) ≫ mappingComplexPre .maximal p _ =
        eId SSet.{u} x ≫ ((K.obj j).map x x ≫ mappingComplexPost .maximal _ p) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => eId SSet.{u} x ≫ t) h.symm)
    _ = (eId SSet.{u} x ≫ (K.obj j).map x x) ≫ mappingComplexPost .maximal _ p :=
      (Category.assoc _ _ _).symm
    _ = maxMappingIdentity ((K.obj j).obj x) ≫ mappingComplexPost .maximal _ p :=
      congrArg (fun t => t ≫ mappingComplexPost .maximal ((K.obj j).obj x) p) hi
    _ = maxMappingPoint p := maxMappingIdentity_post p
    _ = maxMappingIdentity (colimit (evaluated K x)) ≫ mappingComplexPre .maximal p _ :=
      (maxMappingIdentity_pre p).symm

end SSet.Marked.EnrichedColimit
