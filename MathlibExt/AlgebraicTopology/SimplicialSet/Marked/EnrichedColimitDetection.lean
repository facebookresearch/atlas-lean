/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitAction

/-!
# Actual colimit injections detect entire marked Hom families

The native maximal standard-simplex product preserves the original
marked value colimit. Its original injection maps therefore detect
equality of whole marked prisms. Applying this in each scalar degree
detects complete simplicial Hom maps, not just their zero vertices.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits Opposite

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- The original marked value injections detect each entire maximal parameter prism. -/
theorem prism_hom_ext (x : C) [HasColimit (evaluated K x)] (A : SSet.{u}) (Y : Marked.{u})
    {f g : prod (max A) (colimit (evaluated K x)) ⟶ Y}
    (h : ∀ j : J,
      prodMap (𝟙 (max A)) (colimit.ι (evaluated K x) j) ≫ f =
        prodMap (𝟙 (max A)) (colimit.ι (evaluated K x) j) ≫ g) : f = g := by
  let _ : PreservesColimitsOfSize.{t, w} (prodLeft (max A)) :=
    (leftProductAdjunction (max A)).leftAdjoint_preservesColimits
  exact (isColimitOfPreserves (prodLeft (max A)) (colimit.isColimit (evaluated K x))).hom_ext h

/-- Original source injections detect the whole simplicial Hom map in every scalar degree. -/
theorem sourceMap_hom_ext (x : C) [HasColimit (evaluated K x)] (A : SSet.{u}) (Y : Marked.{u})
    {f g : A ⟶ mappingComplex .maximal (colimit (evaluated K x)) Y}
    (h : ∀ j : J,
      f ≫ mappingComplexPre .maximal (colimit.ι (evaluated K x) j) Y =
        g ≫ mappingComplexPre .maximal (colimit.ι (evaluated K x) j) Y) : f = g := by
  ext n a
  apply prism_hom_ext K x (SSet.stdSimplex.obj n.unop) Y
  intro j
  exact congr($(h j).app n a)

end SSet.Marked.EnrichedColimit
