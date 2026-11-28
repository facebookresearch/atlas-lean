/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation

/-!
# Original free-extension components and full target naturality

The proved free evaluation universal property reconstructs every
original whole marked component. Target composition retains the
original coefficient map and the whole enriched action, with no new
adjunction choices.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- Postcomposition of a genuine free extension is the same original coefficient postcomposition. -/
theorem enrichedFreeExtend_post (c : C) (A : Marked.{u}) {F G : EnrichedDiagram C}
    (f : A ⟶ F.obj c) (φ : F ⟶ G) :
    enrichedFreeExtend C c A F f ≫ φ = enrichedFreeExtend C c A G (f ≫ φ.app c) := by
  apply (enrichedFreeHomEquiv C c A G).injective
  change enrichedFreeUnit C c A ≫ ((enrichedFreeExtend C c A F f).app c ≫ φ.app c) =
    enrichedFreeUnit C c A ≫ (enrichedFreeExtend C c A G (f ≫ φ.app c)).app c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ φ.app c) (enrichedFreeExtend_unit C c A F f)).trans
      (enrichedFreeExtend_unit C c A G (f ≫ φ.app c)).symm)

/-- Every whole original free map component is the native action on its original unit evaluation. -/
theorem enrichedFreeMap_component (c : C) (A : Marked.{u}) (F : EnrichedDiagram C)
    (f : enrichedFreeDiagram C c A ⟶ F) (x : C) :
    f.app x = prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeHomEquiv C c A F f) ≫
      enrichedDiagramAction F c x :=
  (congrArg (fun t => t.app x) (enrichedFreeExtend_recover C c A F f)).symm

end SSet.Marked
