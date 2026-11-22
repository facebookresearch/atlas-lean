/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSubcomplexColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# The actual full native boundary-face chart colimit

The original boundary is the union of all its original codimension-one
faces, with their exact pairwise face intersections. Its proved native
scalar multicoequalizer transports to the same minimal marked slice
and then to the whole native straightening chart. The statement is a
colimit and operator readback, not relative cofibration recognition.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire original boundary face/intersection cocone is a genuine native same-base minimally marked colimit. -/
def nativeBoundaryFaceIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    IsColimit ((nativeSubcomplexBasisFunctor B n σ).mapCocone
      (SSet.boundary.multicoequalizerDiagram n).multicofork.toLinearOrder) :=
  nativeSubcomplexIsColimit B n σ (SSet.boundary.multicoequalizerDiagram n).multicofork.toLinearOrder
    ((Multicofork.isColimitMapEquiv _ _).symm (SSet.boundary.multicoequalizerDiagram n).isColimit')

/-- Straightening the full original boundary retains exactly the genuine native face/intersection chart colimit and
every original injection. -/
def nativeBoundaryChartFaceIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    IsColimit ((nativeSubcomplexChartFunctor B n σ).mapCocone
      (SSet.boundary.multicoequalizerDiagram n).multicofork.toLinearOrder) :=
  nativeSubcomplexChartIsColimit B n σ (SSet.boundary.multicoequalizerDiagram n).multicofork.toLinearOrder
    ((Multicofork.isColimitMapEquiv _ _).symm (SSet.boundary.multicoequalizerDiagram n).isColimit')

end SSet.Marked
