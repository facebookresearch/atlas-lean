/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeNaturality

/-!
# Coefficient naturality of native free extension

Changing the coefficient before the actual free extension is the
same extension of the composed coefficient map. The original Hom
coordinate and the whole target action remain unchanged.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Free coefficient precomposition is exactly composition of the original coefficient map before extension. -/
theorem enrichedFreeExtend_pre (C : Type v) [EnrichedCategory SSet.{u} C]
    (c : C) {A B : Marked.{u}} (f : A ⟶ B) (F : EnrichedDiagram C) (g : B ⟶ F.obj c) :
    (enrichedFreeDiagramFunctor C c).map f ≫ enrichedFreeExtend C c B F g =
      enrichedFreeExtend C c A F (f ≫ g) := by
  apply EnrichedDiagramMap.ext
  funext x
  change prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f ≫
      (prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) g ≫ enrichedDiagramAction F c x) =
    prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (f ≫ g) ≫ enrichedDiagramAction F c x
  rw [← Category.assoc, ← prodMap_comp, Category.id_comp]

end SSet.Marked
